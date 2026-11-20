//! Literal, deliberately naive reference of `REL_validUntil extraction and
//! verification` (constraints 1-10 of the specification).
//!
//! Nothing here is optimised: it is the oracle against which the integer R1CS
//! of [`super::r1cs`] is tested. Conventions (see the report):
//!
//! * `[n]` is `{0, .., n-1}`; `[a..b]` is the closed range.
//! * `bits(vals)` is MSB-first with 1-based positions, so
//!   `Z_{byte*8+5} * 2^3 + .. + Z_{byte*8+8} * 2^0` is the LOW NIBBLE of the
//!   byte (`byte & 15`). Nibbles are not required to be decimal digits.
//! * The Lagrange indicators are replaced by `==` tests. Outside `M in 1..=12`
//!   the literal Lagrange polynomials give meaningless (non-integer) values, so
//!   the reference rejects such months.

/// Number of date bytes `YYYY-MM-DDThh:mm:ssZ`.
pub const DATE_BYTES: usize = 20;
/// Bytes of `vals` after the prefix: `0xc0 0x74` and the date.
pub const TAIL_BYTES: usize = DATE_BYTES + 2;

/// Positions (inside the 20 date bytes) of the digit characters, in the order
/// `Y1 Y2 Y3 Y4 M1 M2 D1 D2 h1 h2 m1 m2 s1 s2`.
pub const DIGIT_POSITIONS: [usize; 14] = [0, 1, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18];

/// Cumulative days before month `j` (`mu_0 + .. + mu_{j-1}`, `j = 1..=12`).
pub const CUMULATIVE_DAYS: [i128; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];

/// Public data of the relation: the index `(m, prefix)` and the input
/// `(validityPeriod, currentUnixTime)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Statement {
    /// Length of `mso` in bytes.
    pub m: usize,
    /// The public byte prefix of `vals` (`prefixLen = prefix.len()`).
    pub prefix: Vec<u8>,
    pub validity_period: u64,
    pub current_unix_time: u64,
}

impl Statement {
    pub fn prefix_len(&self) -> usize {
        self.prefix.len()
    }
    /// `prefixLen + 22`.
    pub fn window_len(&self) -> usize {
        self.prefix.len() + TAIL_BYTES
    }
}

/// The witness exactly as in the specification.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Witness {
    pub mso: Vec<u8>,
    pub vals: Vec<u8>,
    pub addr: Vec<usize>,
    pub q4: u64,
    pub q100: u64,
    pub q400: u64,
    pub r4: u64,
    pub r100: u64,
    pub r400: u64,
    pub qt4: u64,
    pub qt100: u64,
    pub qt400: u64,
    pub rt4: u64,
    pub rt100: u64,
    pub rt400: u64,
}

/// The decimal-ish fields `P_*(bits(vals))`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DateFields {
    pub year: i128,
    pub month: i128,
    pub day: i128,
    pub hour: i128,
    pub minute: i128,
    pub second: i128,
}

/// `P_year .. P_second` of `vals`; `None` if `vals` is too short.
pub fn date_fields(prefix_len: usize, vals: &[u8]) -> Option<DateFields> {
    if vals.len() < prefix_len + TAIL_BYTES {
        return None;
    }
    let base = prefix_len + 2;
    let d = |k: usize| i128::from(vals[base + DIGIT_POSITIONS[k]] & 15);
    Some(DateFields {
        year: 1000 * d(0) + 100 * d(1) + 10 * d(2) + d(3),
        month: 10 * d(4) + d(5),
        day: 10 * d(6) + d(7),
        hour: 10 * d(8) + d(9),
        minute: 10 * d(10) + d(11),
        second: 10 * d(12) + d(13),
    })
}

/// `UNIX(Y, M, D, h, m, s, r4, r100, r400, q~4, q~100, q~400)` of the
/// specification, with the indicators written as `==` tests.
pub fn unix(f: &DateFields, w: &Witness) -> Option<i128> {
    if !(1..=12).contains(&f.month) {
        return None;
    }
    let is = |x: u64| i128::from(x == 0);
    let leap = is(w.r4) - is(w.r100) + is(w.r400);
    let c = leap * i128::from(f.month <= 2);
    let leap_years = (i128::from(w.qt4) + 1) - (i128::from(w.qt100) + 1)
        + (i128::from(w.qt400) + 1)
        - c;
    Some(
        f.second
            + 60 * f.minute
            + 3600 * f.hour
            + 86_400 * (f.day - 1)
            + 86_400 * CUMULATIVE_DAYS[(f.month - 1) as usize]
            + 365 * 86_400 * (f.year - 1970)
            + leap_years * 86_400,
    )
}

/// Which constraint (1-10) fails first, or `None` if the relation holds.
pub fn first_violation(s: &Statement, w: &Witness) -> Option<u8> {
    let l = s.window_len();
    let p = s.prefix_len();
    if w.mso.len() != s.m || w.vals.len() != l || w.addr.len() != l {
        return Some(1);
    }
    // 1) mso[addr[j]] = vals[j]  (addr[j] in [m])
    if (0..l).any(|j| w.addr[j] >= s.m || w.mso[w.addr[j]] != w.vals[j]) {
        return Some(1);
    }
    // 2) vals[j] = prefix[j]
    if (0..p).any(|j| w.vals[j] != s.prefix[j]) {
        return Some(2);
    }
    // 3) addr[j+1] = addr[j] + 1
    if (0..l - 1).any(|j| w.addr[j + 1] != w.addr[j] + 1) {
        return Some(3);
    }
    let f = date_fields(p, &w.vals).expect("length checked");
    let y = f.year;
    let div = |value: i128, d: i128, q: u64, r: u64| {
        r < d as u64 && value == d * i128::from(q) + i128::from(r)
    };
    // 4-6) Y = 4 q4 + r4, = 100 q100 + r100, = 400 q400 + r400
    if !div(y, 4, w.q4, w.r4) {
        return Some(4);
    }
    if !div(y, 100, w.q100, w.r100) {
        return Some(5);
    }
    if !div(y, 400, w.q400, w.r400) {
        return Some(6);
    }
    // 7-9) the tilde divisions (quotients live in N)
    if !div(y - 1972, 4, w.qt4, w.rt4) {
        return Some(7);
    }
    if !div(y - 2000, 100, w.qt100, w.rt100) {
        return Some(8);
    }
    if !div(y - 2000, 400, w.qt400, w.rt400) {
        return Some(9);
    }
    // 10) UNIX(..) - currentUnixTime in [validityPeriod]
    let Some(u) = unix(&f, w) else {
        return Some(10);
    };
    let diff = u - i128::from(s.current_unix_time);
    if !(0 <= diff && diff < i128::from(s.validity_period)) {
        return Some(10);
    }
    None
}

/// `true` iff all ten constraints hold.
pub fn holds(s: &Statement, w: &Witness) -> bool {
    first_violation(s, w).is_none()
}

/// Builds the honest witness whose window starts at `start` in `mso`. The
/// quotient/remainder fields are computed with euclidean division and are
/// meaningful only if the date is satisfiable (`Y >= 2000`).
pub fn honest_witness(s: &Statement, mso: &[u8], start: usize) -> Option<Witness> {
    let l = s.window_len();
    if mso.len() != s.m || start.checked_add(l)? > s.m {
        return None;
    }
    let vals = mso[start..start + l].to_vec();
    let y = date_fields(s.prefix_len(), &vals)?.year;
    let dm = |v: i128, d: i128| (v.div_euclid(d).max(0) as u64, v.rem_euclid(d) as u64);
    let (q4, r4) = dm(y, 4);
    let (q100, r100) = dm(y, 100);
    let (q400, r400) = dm(y, 400);
    let (qt4, rt4) = dm(y - 1972, 4);
    let (qt100, rt100) = dm(y - 2000, 100);
    let (qt400, rt400) = dm(y - 2000, 400);
    Some(Witness {
        mso: mso.to_vec(),
        vals,
        addr: (start..start + l).collect(),
        q4,
        q100,
        q400,
        r4,
        r100,
        r400,
        qt4,
        qt100,
        qt400,
        rt4,
        rt100,
        rt400,
    })
}

/// Test helper: an `mso`-like byte string with `prefix`, `0xc0 0x74` and the
/// ASCII date `YYYY-MM-DDThh:mm:ssZ` embedded at `start`; other bytes come from
/// a small deterministic generator.
pub fn synthetic_mso(
    m: usize,
    start: usize,
    prefix: &[u8],
    date: &str,
    seed: u64,
) -> Vec<u8> {
    assert_eq!(date.len(), DATE_BYTES);
    let mut state = seed | 1;
    let mut mso: Vec<u8> = (0..m)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state >> 24) as u8
        })
        .collect();
    let mut window = prefix.to_vec();
    window.extend_from_slice(&[0xc0, 0x74]);
    window.extend_from_slice(date.as_bytes());
    mso[start..start + window.len()].copy_from_slice(&window);
    mso
}

/// Independent civil-date -> Unix time (Hinnant's days-from-civil).
pub fn civil_to_unix(y: i64, m: i64, d: i64, hh: i64, mm: i64, ss: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    days * 86_400 + hh * 3600 + mm * 60 + ss
}

#[cfg(test)]
mod tests {
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
    fn honest_witness_satisfies_and_matches_independent_unix() {
        let date = "2031-02-28T13:45:09Z";
        let u = civil_to_unix(2031, 2, 28, 13, 45, 9) as u64;
        let mso = synthetic_mso(200, 37, PREFIX, date, 7);
        let s = stmt(200, u - 1000, 5000);
        let w = honest_witness(&s, &mso, 37).unwrap();
        assert_eq!(first_violation(&s, &w), None);
        let f = date_fields(PREFIX.len(), &w.vals).unwrap();
        assert_eq!(unix(&f, &w), Some(i128::from(u)));
    }

    #[test]
    fn unix_formula_matches_calendar_for_every_day_2000_to_2105() {
        for year in 2000..=2105i64 {
            for month in 1..=12i64 {
                let dim = match month {
                    2 if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 => 29,
                    2 => 28,
                    4 | 6 | 9 | 11 => 30,
                    _ => 31,
                };
                for day in 1..=dim {
                    let date = format!("{year:04}-{month:02}-{day:02}T23:59:58Z");
                    let mso = synthetic_mso(64, 5, PREFIX, &date, 1);
                    let want = civil_to_unix(year, month, day, 23, 59, 58);
                    let s = stmt(64, want as u64, 1);
                    let w = honest_witness(&s, &mso, 5).unwrap();
                    assert_eq!(first_violation(&s, &w), None, "{date}");
                }
            }
        }
    }

    #[test]
    fn validity_window_boundaries() {
        let u = civil_to_unix(2030, 6, 15, 0, 0, 0) as u64;
        let mso = synthetic_mso(100, 3, PREFIX, "2030-06-15T00:00:00Z", 3);
        let ok = |now: u64, period: u64| {
            let s = stmt(100, now, period);
            holds(&s, &honest_witness(&s, &mso, 3).unwrap())
        };
        assert!(ok(u, 1)); // diff 0 in [1]
        assert!(!ok(u, 0)); // [0] is empty
        assert!(ok(u - 9, 10)); // diff 9 in [10]
        assert!(!ok(u - 10, 10)); // diff 10 not in [10]
        assert!(!ok(u + 1, 1_000_000)); // expired (negative diff)
    }

    #[test]
    fn each_tamper_is_rejected() {
        let u = civil_to_unix(2024, 2, 29, 8, 0, 0) as u64;
        let mso = synthetic_mso(120, 20, PREFIX, "2024-02-29T08:00:00Z", 9);
        let s = stmt(120, u - 5, 100);
        let good = honest_witness(&s, &mso, 20).unwrap();
        assert!(holds(&s, &good));
        let mut w = good.clone();
        w.vals[3] ^= 1;
        assert_eq!(first_violation(&s, &w), Some(1));
        let mut w = good.clone();
        w.addr[5] += 1;
        assert!(!holds(&s, &w));
        let mut w = good.clone();
        w.r4 = 1;
        assert!(!holds(&s, &w));
        let mut w = good.clone();
        w.qt400 += 1;
        assert!(!holds(&s, &w));
        // a window at a different place whose prefix differs
        let w = honest_witness(&s, &mso, 21).unwrap();
        assert!(!holds(&s, &w));
    }
}
