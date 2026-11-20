//! Integer R1CS of `REL_validUntil` (word level, like MultiSwap/BabyBear).
//!
//! Every variable is an integer *word* that BitZ commits as `width` raw bits, so
//! the range `[0, 2^width)` is enforced by the commitment itself. The
//! assignment is `[const | BYTE | NIBBLE | FLAG | NUM | WIDE | 0 | 0]`, eight
//! blocks of one shared power-of-two capacity; block `b`, entry `i` is column
//! `b * capacity + i`, and `z[0] = 1`.
//!
//! Row `r` states `(A z) * (B z) = (C z)` over the integers (all magnitudes are
//! far below `2^64`, so equality modulo the BitZ prime implies equality over `Z`).
//! A row may name the variable it `defines` (coefficient `+1` in `C`); the
//! witness generator solves such rows in order.
//!
//! Gadgets (details in the report):
//! * **window lookup** - constraints 1 and 3 say `vals = mso[a .. a+L)` with
//!   `L = prefixLen + 22`; a barrel shifter (one multiplication row per byte per
//!   stage, `O(L log m + m)` rows) replaces the `O(m L)` one-hot product.
//!   `a <= m - L` is enforced through a slack word.
//! * **nibbles** - `byte = 16 hi + lo` for the 14 digit characters; `lo` is the
//!   `P_*` value (`bits 5..8` MSB-first).
//! * **division** - `dividend = d q + r`, `r + slack = d - 1` with `r, slack`
//!   words, so `r in [0, d-1]` exactly.
//! * **is-zero** - `r z = 0` and `w = r + z - 1` with `w` a word, so
//!   `z = [r = 0]` (no inverse needed over the integers).
//! * **calendar** - month one-hot gives `L(M)` and `[M <= 2]` linearly; the
//!   leap-day correction `c = leap * [M <= 2]` is the single non-trivial product.
//! * **window of validity** - `e1 = UNIX - now`, `e2 = period - 1 - e1`, both
//!   62-bit words, i.e. `0 <= UNIX - now < period`.

use super::reference::{CUMULATIVE_DAYS, DIGIT_POSITIONS, Statement, TAIL_BYTES};
use thiserror::Error;

/// Block codes (the selector value in the assignment index).
pub const CONST: u8 = 0;
pub const BYTE: u8 = 1;
pub const NIBBLE: u8 = 2;
pub const FLAG: u8 = 3;
pub const NUM: u8 = 4;
pub const WIDE: u8 = 5;
/// Bits committed per entry of each block (block 0 is the implicit constant).
pub const BLOCK_WIDTHS: [usize; 6] = [0, 8, 4, 1, 16, 62];
/// First committed bit slot of each block inside a gate's 128 slots.
pub const SLOT_STARTS: [usize; 6] = [0, 0, 8, 12, 13, 29];
/// Selector variables of the assignment domain (8 blocks, 2 are zero padding).
pub const SELECTOR_VARS: usize = 3;
/// Statement values (`validityPeriod`, `currentUnixTime`) must be below this.
pub const WIDE_LIMIT: u64 = 1 << 62;
/// Smallest gate capacity (keeps the commit geometry in its supported range).
pub const MIN_CAPACITY: usize = 256;

#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum R1csError {
    #[error("mso has {m} bytes but the window needs {need}")]
    WindowDoesNotFit { m: usize, need: usize },
    #[error("validityPeriod and currentUnixTime must be < 2^62")]
    StatementTooLarge,
    #[error("witness input has the wrong length or window position")]
    BadWitnessInput,
}

/// A variable: `block` and `index` inside it. `Var::ONE` is the constant one.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Var {
    pub block: u8,
    pub index: u32,
}

impl Var {
    pub const ONE: Var = Var {
        block: CONST,
        index: 0,
    };
}

/// A linear form `sum coeff * var` over the integers.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lin(Vec<(Var, i128)>);

impl Lin {
    pub fn zero() -> Self {
        Self(Vec::new())
    }
    pub fn var(v: Var) -> Self {
        Self(vec![(v, 1)])
    }
    pub fn constant(c: i128) -> Self {
        Self(vec![(Var::ONE, c)])
    }
    pub fn scaled(mut self, k: i128) -> Self {
        for term in &mut self.0 {
            term.1 *= k;
        }
        self
    }
    pub fn plus(mut self, other: &Lin) -> Self {
        self.0.extend(other.0.iter().copied());
        self
    }
    pub fn minus(mut self, other: &Lin) -> Self {
        self.0.extend(other.0.iter().map(|&(v, c)| (v, -c)));
        self
    }
    pub fn term(mut self, v: Var, c: i128) -> Self {
        self.0.push((v, c));
        self
    }
    /// Sorted, merged, zero-free copy of the terms.
    pub fn normalized(&self) -> Vec<(Var, i128)> {
        let mut terms = self.0.clone();
        terms.sort();
        let mut out: Vec<(Var, i128)> = Vec::with_capacity(terms.len());
        for (v, c) in terms {
            match out.last_mut() {
                Some(last) if last.0 == v => last.1 += c,
                _ => out.push((v, c)),
            }
        }
        out.retain(|&(_, c)| c != 0);
        out
    }
    pub fn is_zero(&self) -> bool {
        self.normalized().is_empty()
    }
}

/// `A z * B z = C z`; `defines` is a variable with coefficient `+1` in `C`.
#[derive(Clone, Debug)]
pub struct Row {
    pub a: Lin,
    pub b: Lin,
    pub c: Lin,
    pub defines: Option<Var>,
}

/// `x * y` words of one division gadget.
#[derive(Clone, Copy, Debug)]
pub struct Div {
    pub q: Var,
    pub r: Var,
    pub slack: Var,
}

/// The circuit: variable layout plus rows. Deterministic in `(statement, strict)`.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub statement: Statement,
    /// Also constrain the CBOR header, separators and decimal digits (the
    /// specification does not; see the report).
    pub strict: bool,
    pub counts: [usize; 6],
    pub rows: Vec<Row>,
    pub mso: Vec<Var>,
    pub a_bits: Vec<Var>,
    pub slack_a: Option<Var>,
    pub window: Vec<Lin>,
    pub hi: [Var; 14],
    pub lo: [Var; 14],
    /// `Y mod/div 4, 100, 400`.
    pub div: [Div; 3],
    /// `(Y-1972) / 4`, `(Y-2000) / 100`, `(Y-2000) / 400`.
    pub div_tilde: [Div; 3],
    pub zero: [Var; 3],
    pub zero_w: [Var; 3],
    pub month: [Var; 12],
    pub leap_c: Var,
    pub e1: Var,
    pub e2: Var,
}

fn bit_len(x: usize) -> usize {
    (usize::BITS - x.leading_zeros()) as usize
}

impl Circuit {
    fn alloc(counts: &mut [usize; 6], block: u8) -> Var {
        let index = counts[block as usize];
        counts[block as usize] += 1;
        Var {
            block,
            index: u32::try_from(index).expect("block fits u32"),
        }
    }

    /// Builds the circuit of a statement.
    pub fn new(statement: &Statement, strict: bool) -> Result<Self, R1csError> {
        let l = statement.window_len();
        let p = statement.prefix_len();
        let m = statement.m;
        if m < l {
            return Err(R1csError::WindowDoesNotFit { m, need: l });
        }
        if statement.validity_period >= WIDE_LIMIT || statement.current_unix_time >= WIDE_LIMIT {
            return Err(R1csError::StatementTooLarge);
        }
        let mut counts = [0usize; 6];
        counts[0] = 1;
        let mut rows: Vec<Row> = Vec::new();
        let one = Lin::constant(1);
        let linear = |rows: &mut Vec<Row>, c: Lin, defines: Option<Var>| {
            rows.push(Row {
                a: Lin::zero(),
                b: Lin::zero(),
                c,
                defines,
            });
        };

        // --- witness bytes of mso -------------------------------------------------
        let mso: Vec<Var> = (0..m).map(|_| Self::alloc(&mut counts, BYTE)).collect();

        // --- address a = addr[0], a <= m - L ---------------------------------------
        let span = m - l;
        let k_bits = bit_len(span);
        let a_bits: Vec<Var> = (0..k_bits)
            .map(|_| Self::alloc(&mut counts, FLAG))
            .collect();
        let slack_a = if k_bits > 0 {
            let t = Self::alloc(&mut counts, WIDE);
            let mut c = Lin::var(t).plus(&one.clone().scaled(-(span as i128)));
            for (k, &bit) in a_bits.iter().enumerate() {
                c = c.term(bit, 1i128 << k);
            }
            linear(&mut rows, c, Some(t));
            Some(t)
        } else {
            None
        };

        // --- barrel shifter: S[0][j] = mso[a + j] ---------------------------------
        let mut stage: Vec<Lin> = (0..l + (1usize << k_bits) - 1)
            .map(|i| if i < m { Lin::var(mso[i]) } else { Lin::zero() })
            .collect();
        for k in (0..k_bits).rev() {
            let shift = 1usize << k;
            let len = l + shift - 1;
            let mut next = Vec::with_capacity(len);
            for i in 0..len {
                let x = &stage[i];
                let y = &stage[i + shift];
                let b = y.clone().minus(x);
                if b.is_zero() {
                    next.push(x.clone());
                    continue;
                }
                let out = Self::alloc(&mut counts, BYTE);
                rows.push(Row {
                    a: Lin::var(a_bits[k]),
                    b,
                    c: Lin::var(out).minus(x),
                    defines: Some(out),
                });
                next.push(Lin::var(out));
            }
            stage = next;
        }
        let window = stage;
        debug_assert_eq!(window.len(), l);

        // --- public prefix (constraint 2) -----------------------------------------
        for j in 0..p {
            let c = window[j]
                .clone()
                .plus(&Lin::constant(-i128::from(statement.prefix[j])));
            linear(&mut rows, c, None);
        }

        // --- nibbles of the 14 digit characters -----------------------------------
        let base = p + 2;
        let mut hi = [Var::ONE; 14];
        let mut lo = [Var::ONE; 14];
        for k in 0..14 {
            hi[k] = Self::alloc(&mut counts, NIBBLE);
            lo[k] = Self::alloc(&mut counts, NIBBLE);
            let c = window[base + DIGIT_POSITIONS[k]]
                .clone()
                .term(hi[k], -16)
                .term(lo[k], -1);
            linear(&mut rows, c, None);
        }
        let number = |digits: &[Var]| {
            let mut value = Lin::zero();
            let mut weight = 1i128;
            for &d in digits.iter().rev() {
                value = value.term(d, weight);
                weight *= 10;
            }
            value
        };
        let year = number(&lo[0..4]);
        let month_value = number(&lo[4..6]);
        let day = number(&lo[6..8]);
        let hour = number(&lo[8..10]);
        let minute = number(&lo[10..12]);
        let second = number(&lo[12..14]);

        // --- divisions -------------------------------------------------------------
        let divmod = |counts: &mut [usize; 6], rows: &mut Vec<Row>, dividend: Lin, d: i128| {
            let q = Self::alloc(counts, NUM);
            let r = Self::alloc(counts, NUM);
            let slack = Self::alloc(counts, NUM);
            rows.push(Row {
                a: Lin::zero(),
                b: Lin::zero(),
                c: dividend.term(q, -d).term(r, -1),
                defines: None,
            });
            rows.push(Row {
                a: Lin::zero(),
                b: Lin::zero(),
                c: Lin::var(slack).term(r, 1).term(Var::ONE, -(d - 1)),
                defines: Some(slack),
            });
            Div { q, r, slack }
        };
        let div = [
            divmod(&mut counts, &mut rows, year.clone(), 4),
            divmod(&mut counts, &mut rows, year.clone(), 100),
            divmod(&mut counts, &mut rows, year.clone(), 400),
        ];
        let div_tilde = [
            divmod(&mut counts, &mut rows, year.clone().term(Var::ONE, -1972), 4),
            divmod(&mut counts, &mut rows, year.clone().term(Var::ONE, -2000), 100),
            divmod(&mut counts, &mut rows, year.clone().term(Var::ONE, -2000), 400),
        ];

        // --- is-zero indicators of r4, r100, r400 ----------------------------------
        let mut zero = [Var::ONE; 3];
        let mut zero_w = [Var::ONE; 3];
        for i in 0..3 {
            let r = div[i].r;
            let z = Self::alloc(&mut counts, FLAG);
            let w = Self::alloc(&mut counts, NUM);
            rows.push(Row {
                a: Lin::var(r),
                b: Lin::var(z),
                c: Lin::zero(),
                defines: None,
            });
            let c = Lin::var(w).term(r, -1).term(z, -1).term(Var::ONE, 1);
            rows.push(Row {
                a: Lin::zero(),
                b: Lin::zero(),
                c,
                defines: Some(w),
            });
            zero[i] = z;
            zero_w[i] = w;
        }
        let leap = Lin::var(zero[0]).term(zero[1], -1).term(zero[2], 1);

        // --- month one-hot ---------------------------------------------------------
        let month: [Var; 12] = std::array::from_fn(|_| Self::alloc(&mut counts, FLAG));
        let mut sum = Lin::constant(-1);
        let mut weighted = month_value.clone().scaled(-1);
        for (j, &s) in month.iter().enumerate() {
            sum = sum.term(s, 1);
            weighted = weighted.term(s, (j + 1) as i128);
        }
        linear(&mut rows, sum, None);
        linear(&mut rows, weighted, None);

        // --- c = leap * [M <= 2] ---------------------------------------------------
        let leap_c = Self::alloc(&mut counts, FLAG);
        rows.push(Row {
            a: leap,
            b: Lin::var(month[0]).term(month[1], 1),
            c: Lin::var(leap_c),
            defines: Some(leap_c),
        });

        // --- UNIX and the validity window -------------------------------------------
        let mut unix = second
            .term(Var::ONE, 0)
            .plus(&minute.scaled(60))
            .plus(&hour.scaled(3600))
            .plus(&day.scaled(86_400))
            .term(Var::ONE, -86_400);
        for (j, &s) in month.iter().enumerate() {
            unix = unix.term(s, 86_400 * CUMULATIVE_DAYS[j]);
        }
        unix = unix.plus(&year.scaled(365 * 86_400));
        unix = unix.term(Var::ONE, -365 * 86_400 * 1970);
        unix = unix
            .term(div_tilde[0].q, 86_400)
            .term(div_tilde[1].q, -86_400)
            .term(div_tilde[2].q, 86_400)
            .term(Var::ONE, 86_400)
            .term(leap_c, -86_400);
        let e1 = Self::alloc(&mut counts, WIDE);
        let e2 = Self::alloc(&mut counts, WIDE);
        // e1 = UNIX - now
        let c1 = Lin::var(e1)
            .minus(&unix)
            .term(Var::ONE, i128::from(statement.current_unix_time));
        linear(&mut rows, c1, Some(e1));
        // e2 = period - 1 - e1
        let c2 = Lin::var(e2)
            .term(e1, 1)
            .term(Var::ONE, -(i128::from(statement.validity_period) - 1));
        linear(&mut rows, c2, Some(e2));

        // --- optional strict format rows ---------------------------------------------
        if strict {
            // CBOR header at p, p+1.
            for (offset, byte) in [(0usize, 0xc0i128), (1, 0x74)] {
                let c = window[p + offset].clone().term(Var::ONE, -byte);
                linear(&mut rows, c, None);
            }
            // separators `-`,`-`,`T`,`:`,`:`,`Z` at date offsets 4,7,10,13,16,19.
            for (offset, byte) in [(4usize, 0x2di128), (7, 0x2d), (10, 0x54), (13, 0x3a), (16, 0x3a), (19, 0x5a)] {
                let c = window[base + offset].clone().term(Var::ONE, -byte);
                linear(&mut rows, c, None);
            }
            // digits are ASCII `0`..`9`: high nibble 3, low nibble <= 9.
            for k in 0..14 {
                linear(&mut rows, Lin::var(hi[k]).term(Var::ONE, -3), None);
                let g = Self::alloc(&mut counts, NIBBLE);
                let c = Lin::var(g).term(lo[k], 1).term(Var::ONE, -9);
                linear(&mut rows, c, Some(g));
            }
        }

        Ok(Self {
            statement: statement.clone(),
            strict,
            counts,
            rows,
            mso,
            a_bits,
            slack_a,
            window,
            hi,
            lo,
            div,
            div_tilde,
            zero,
            zero_w,
            month,
            leap_c,
            e1,
            e2,
        })
    }

    /// Gate capacity: a power of two covering every block and every row.
    pub fn capacity(&self) -> usize {
        let widest = self.counts[1..].iter().copied().max().unwrap_or(0);
        widest
            .max(self.rows.len())
            .max(MIN_CAPACITY)
            .next_power_of_two()
    }

    pub fn gate_vars(&self) -> usize {
        self.capacity().trailing_zeros() as usize
    }

    /// Number of R1CS rows.
    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    /// Number of multiplication rows (both `A` and `B` non-empty).
    pub fn num_products(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| !r.a.is_zero() && !r.b.is_zero())
            .count()
    }

    /// Total committed bits that carry data (before padding to the grid).
    pub fn live_bits(&self) -> usize {
        (1..6).map(|b| self.counts[b] * BLOCK_WIDTHS[b]).sum()
    }

    /// Flat column of a variable.
    pub fn column(&self, v: Var) -> usize {
        v.block as usize * self.capacity() + v.index as usize
    }

    /// Sparse integer rows `[A, B, C]` with flat columns.
    pub fn compile(&self) -> Vec<[Vec<(usize, i128)>; 3]> {
        let capacity = self.capacity();
        let conv = |lin: &Lin| -> Vec<(usize, i128)> {
            lin.normalized()
                .into_iter()
                .map(|(v, c)| (v.block as usize * capacity + v.index as usize, c))
                .collect()
        };
        self.rows
            .iter()
            .map(|r| [conv(&r.a), conv(&r.b), conv(&r.c)])
            .collect()
    }

    /// Solves every witness word from `mso` and the window start `a`.
    ///
    /// Words are truncated to their committed width exactly as the commitment
    /// would, so an unsatisfiable statement yields an assignment that
    /// [`Circuit::check`] rejects instead of an error.
    pub fn fill(&self, mso: &[u8], start: usize) -> Result<Assignment, R1csError> {
        let s = &self.statement;
        let l = s.window_len();
        let p = s.prefix_len();
        if mso.len() != s.m || start > s.m - l {
            return Err(R1csError::BadWitnessInput);
        }
        let mut asg = Assignment::new(self.counts);
        for (i, &v) in self.mso.iter().enumerate() {
            asg.set(v, i128::from(mso[i]));
        }
        for (k, &v) in self.a_bits.iter().enumerate() {
            asg.set(v, ((start >> k) & 1) as i128);
        }
        let base = p + 2;
        let byte = |pos: usize| mso[start + base + pos];
        let digit = |k: usize| i128::from(byte(DIGIT_POSITIONS[k]) & 15);
        for k in 0..14 {
            asg.set(self.hi[k], i128::from(byte(DIGIT_POSITIONS[k]) >> 4));
            asg.set(self.lo[k], digit(k));
        }
        let num = |a: usize, n: usize| (a..a + n).fold(0i128, |acc, k| acc * 10 + digit(k));
        let (y, mo) = (num(0, 4), num(4, 2));
        for (div, (value, d)) in self
            .div
            .iter()
            .zip([(y, 4), (y, 100), (y, 400)])
            .chain(self.div_tilde.iter().zip([(y - 1972, 4), (y - 2000, 100), (y - 2000, 400)]))
        {
            asg.set(div.q, value.div_euclid(d));
            asg.set(div.r, value.rem_euclid(d));
        }
        for i in 0..3 {
            let r = asg.get(self.div[i].r);
            asg.set(self.zero[i], i128::from(r == 0));
        }
        if (1..=12).contains(&mo) {
            asg.set(self.month[(mo - 1) as usize], 1);
        }
        // solve the defined variables in emission order
        for row in &self.rows {
            let Some(v) = row.defines else { continue };
            let product = asg.eval(&row.a) * asg.eval(&row.b);
            let rest = asg.eval(&row.c) - asg.get(v);
            asg.set(v, product - rest);
        }
        Ok(asg)
    }

    /// Checks every row over the integers; `Err(row)` names the first failure.
    pub fn check(&self, asg: &Assignment) -> Result<(), usize> {
        if asg.get(Var::ONE) != 1 {
            return Err(usize::MAX);
        }
        for (i, row) in self.rows.iter().enumerate() {
            if asg.eval(&row.a) * asg.eval(&row.b) != asg.eval(&row.c) {
                return Err(i);
            }
        }
        Ok(())
    }

    /// The fixed number of bytes of the date tail (`0xc0 0x74` + date).
    pub const fn tail_bytes() -> usize {
        TAIL_BYTES
    }
}

/// Values of all words, block by block (each already truncated to its width).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Assignment {
    pub values: [Vec<u64>; 6],
}

impl Assignment {
    fn new(counts: [usize; 6]) -> Self {
        let mut values = counts.map(|n| vec![0u64; n]);
        values[0][0] = 1;
        Self { values }
    }
    pub fn get(&self, v: Var) -> i128 {
        i128::from(self.values[v.block as usize][v.index as usize])
    }
    /// Stores `value` truncated to the block's committed width.
    pub fn set(&mut self, v: Var, value: i128) {
        if v.block == CONST {
            return;
        }
        let mask = (1i128 << BLOCK_WIDTHS[v.block as usize]) - 1;
        self.values[v.block as usize][v.index as usize] = (value & mask) as u64;
    }
    /// Overwrites a word with an arbitrary (adversarial) value, truncated.
    pub fn tamper(&mut self, v: Var, value: i128) {
        self.set(v, value);
    }
    pub fn eval(&self, lin: &Lin) -> i128 {
        lin.0.iter().map(|&(v, c)| c * self.get(v)).sum()
    }
    /// The flat assignment `[const | blocks ..]` padded to `8 * capacity`.
    pub fn flat(&self, capacity: usize) -> Vec<u64> {
        let mut out = vec![0u64; 8 * capacity];
        for (b, block) in self.values.iter().enumerate() {
            out[b * capacity..b * capacity + block.len()].copy_from_slice(block);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::super::reference::{self, civil_to_unix, synthetic_mso};
    use super::*;

    const PREFIX: &[u8] = b"\x6avalidUntil";

    fn stmt(m: usize, now: u64, period: u64) -> Statement {
        Statement {
            m,
            prefix: PREFIX.to_vec(),
            validity_period: period,
            current_unix_time: now,
        }
    }

    #[test]
    fn honest_assignment_satisfies_every_row() {
        let u = civil_to_unix(2031, 2, 28, 13, 45, 9) as u64;
        for (m, start) in [(33, 0), (34, 1), (200, 37), (257, 224), (1000, 417)] {
            let mso = synthetic_mso(m, start, PREFIX, "2031-02-28T13:45:09Z", 5);
            let s = stmt(m, u - 100, 1000);
            for strict in [false, true] {
                let c = Circuit::new(&s, strict).unwrap();
                let a = c.fill(&mso, start).unwrap();
                assert_eq!(c.check(&a), Ok(()), "m={m} start={start} strict={strict}");
            }
        }
    }

    #[test]
    fn r1cs_agrees_with_the_reference_on_dates_and_windows() {
        // every month/day class incl. leap years and century years
        let dates = [
            "2000-02-29T00:00:00Z",
            "2000-03-01T00:00:00Z",
            "2100-02-28T23:59:59Z",
            "2100-03-01T00:00:00Z",
            "2024-12-31T23:59:59Z",
            "2023-01-01T00:00:00Z",
            "2400-02-29T12:00:00Z",
            "2200-01-31T01:02:03Z",
            "1999-12-31T23:59:59Z", // Y < 2000: unsatisfiable
            "2030-13-01T00:00:00Z", // month 13: rejected
            "2030-00-10T00:00:00Z", // month 0: rejected
        ];
        for date in dates {
            for (now_delta, period) in [(0i64, 1u64), (5, 10), (-1, 10), (3, 3), (0, 0)] {
                let y: i64 = date[0..4].parse().unwrap();
                let mo: i64 = date[5..7].parse().unwrap();
                let d: i64 = date[8..10].parse().unwrap();
                let u = if (1..=12).contains(&mo) {
                    civil_to_unix(y, mo, d, 0, 0, 0) + 0
                } else {
                    1_900_000_000
                };
                let hh: i64 = date[11..13].parse().unwrap();
                let mm: i64 = date[14..16].parse().unwrap();
                let ss: i64 = date[17..19].parse().unwrap();
                let target = u + hh * 3600 + mm * 60 + ss;
                let now = (target - now_delta).max(0) as u64;
                let m = 90;
                let start = 11;
                let mso = synthetic_mso(m, start, PREFIX, date, 77);
                let s = stmt(m, now, period);
                let w = reference::honest_witness(&s, &mso, start).unwrap();
                let want = reference::holds(&s, &w);
                let c = Circuit::new(&s, false).unwrap();
                let got = c.check(&c.fill(&mso, start).unwrap()).is_ok();
                assert_eq!(got, want, "{date} now_delta={now_delta} period={period}");
            }
        }
    }

    #[test]
    fn r1cs_agrees_with_the_reference_on_random_mutations() {
        let u = civil_to_unix(2026, 11, 17, 8, 30, 0) as u64;
        let (m, start) = (150, 60);
        let base = synthetic_mso(m, start, PREFIX, "2026-11-17T08:30:00Z", 11);
        let s = stmt(m, u - 20, 600);
        let c = Circuit::new(&s, false).unwrap();
        let mut state = 0x1234_5678_9abc_def1u64;
        let mut rnd = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let (mut accepted, mut rejected) = (0, 0);
        for _ in 0..400 {
            let mut mso = base.clone();
            let flips = (rnd() % 3) as usize;
            for _ in 0..flips {
                let pos = start + (rnd() as usize) % s.window_len();
                mso[pos] ^= 1 << (rnd() % 8);
            }
            let st = (rnd() % 3) as usize; // sometimes use a wrong start
            let start_used = [start, start + 1, start - 1][st];
            let want = reference::honest_witness(&s, &mso, start_used)
                .map(|w| reference::holds(&s, &w))
                .unwrap_or(false);
            let got = c.check(&c.fill(&mso, start_used).unwrap()).is_ok();
            assert_eq!(got, want);
            if got {
                accepted += 1
            } else {
                rejected += 1
            }
        }
        assert!(accepted > 20 && rejected > 20, "{accepted}/{rejected}");
    }

    #[test]
    fn adversarial_words_are_rejected() {
        let u = civil_to_unix(2024, 2, 29, 8, 0, 0) as u64;
        let (m, start) = (120, 20);
        let mso = synthetic_mso(m, start, PREFIX, "2024-02-29T08:00:00Z", 9);
        let s = stmt(m, u - 5, 100);
        let c = Circuit::new(&s, false).unwrap();
        let good = c.fill(&mso, start).unwrap();
        assert_eq!(c.check(&good), Ok(()));
        let mut targets: Vec<Var> = vec![c.a_bits[0], c.lo[3], c.hi[0], c.leap_c, c.e1, c.e2];
        targets.extend(c.div.iter().flat_map(|d| [d.q, d.r, d.slack]));
        targets.extend(c.div_tilde.iter().flat_map(|d| [d.q, d.r, d.slack]));
        targets.extend(c.zero.iter().chain(c.zero_w.iter()).copied());
        targets.extend(c.month.iter().copied());
        targets.extend(c.mso[start..start + s.window_len()].iter().copied());
        for v in targets {
            let mut bad = good.clone();
            let old = bad.get(v);
            bad.tamper(v, old ^ 1);
            assert!(c.check(&bad).is_err(), "flipping {v:?} went unnoticed");
        }
    }

    #[test]
    fn strict_mode_rejects_malformed_formats() {
        let u = civil_to_unix(2030, 1, 1, 0, 0, 0) as u64;
        let (m, start) = (100, 8);
        let s = stmt(m, u, 10);
        let strict = Circuit::new(&s, true).unwrap();
        let loose = Circuit::new(&s, false).unwrap();
        // wrong CBOR header and a nibble 10 inside the year are accepted by
        // the literal relation but not by the strict one
        let mut mso = synthetic_mso(m, start, PREFIX, "2030-01-01T00:00:00Z", 2);
        let ok = strict.fill(&mso, start).unwrap();
        assert_eq!(strict.check(&ok), Ok(()));
        mso[start + PREFIX.len()] = 0x00; // 0xc0 -> 0x00
        assert!(strict.check(&strict.fill(&mso, start).unwrap()).is_err());
        assert!(loose.check(&loose.fill(&mso, start).unwrap()).is_ok());
    }

    #[test]
    fn sizes_are_reasonable() {
        let s = stmt(2048, 1_800_000_000, 1000);
        let c = Circuit::new(&s, false).unwrap();
        // L log m + m shifter words, a few hundred small rows
        assert!(c.num_rows() < 2048 + 40 * 11 + 400, "{}", c.num_rows());
        assert!(c.capacity() <= 8192);
    }

    #[test]
    fn rejects_bad_statements() {
        assert!(matches!(
            Circuit::new(&stmt(10, 1, 1), false),
            Err(R1csError::WindowDoesNotFit { .. })
        ));
        assert!(matches!(
            Circuit::new(&stmt(100, 1 << 62, 1), false),
            Err(R1csError::StatementTooLarge)
        ));
    }
}
