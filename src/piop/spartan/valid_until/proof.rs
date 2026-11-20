//! `REL_validUntil` through the shared BitZ protocol runner.
//!
//! The integer R1CS of [`super::r1cs`] is described to [`protocol`] as a
//! [`RelationSpec`] with *direct* discharge, one Step-2 prime drawn from the
//! transcript, the plain cubic Spartan kernel and a
//! `PiopWitness::FieldAssignment` witness (row products are derived from the
//! public matrices projected to the drawn prime).
//!
//! Commitment geometry (identical to CM-AND / BabyBear): every "gate" `g`
//! owns 128 bit slots; block `b` stores word `g` in slots
//! `SLOT_STARTS[b] .. +BLOCK_WIDTHS[b]`. With `s = floor(gate_vars/2)` the low
//! `s` gate bits are BitZ columns and the rest plus the 7 slot bits are folded
//! row variables.

use crate::{
    ligerito::{LOG_PACKING, packed_vars},
    ligerito_flock::{
        FlockCommitHint, LigeritoSelection, commit_rs_ligerito_rows, sha_lig_configs,
    },
    pcs::IntegerMatrixLayout,
    piop::spartan::{
        ConstraintMatrices, PreparedConstraintMatrices, SpartanBitzField, SpartanField as _,
        SpartanMatrixError,
        profile::{IopInstanceFacts, IopSecurityParams, Lambda100},
        protocol::{
            self, BindingHasher, BlockTable, Domains, FieldConfig, Kernel, MatrixSource, Opener,
            PiopWitness, PreparedRelation, PreparedRelationPrefix, Proof, ProtocolError,
            RelationSpec, SlotRange,
        },
    },
    transcript::traits::Transcript,
};
use circuit::linear_map::{CscMatrix, binary::PreparedVirtualMap};
use field::RingOps;
use flock_core::pcs::{
    commit::Commitment,
    ligerito::{ProverConfig as LigProverConfig, VerifierConfig as LigVerifierConfig},
};

use super::r1cs::{
    Assignment, BLOCK_WIDTHS, Circuit, R1csError, SELECTOR_VARS, SLOT_STARTS,
};
use super::reference::Statement;

/// Committed bit slots per gate.
pub const SLOTS_PER_GATE: usize = 128;
const BINDING_DOMAIN: &[u8] = b"bitz/valid-until/assignment/v1";
const BLOCK_ORDER: &[u8] = b"e0|byte|nibble|flag|num|wide|zero|zero";

static DOMAINS: Domains = Domains {
    statement_tag: b"valid-until/statement/v1",
    prime_sampling: b"bitz/valid-until/runtime-prime/v1",
    initial_grinding: b"bitz/valid-until/grinding/initial/v1",
    piop_grinding: b"bitz/valid-until/grinding/piop/v1",
    terminal_grinding: b"bitz/valid-until/grinding/terminal/v1",
    bitified_claim: b"bitz/valid-until/bitified-claim/v1",
    claim_tag: b"",
    reduction_grinding: b"",
    reduction_prime: b"",
    scopes: crate::protocol_scopes!("valid-until-bitz"),
};

/// The relation as the shared protocol sees it.
pub struct ValidUntilSpec {
    circuit: Circuit,
    rows: Vec<[Vec<(usize, i128)>; 3]>,
    capacity: usize,
    gate_vars: usize,
    statement_digest: [u8; 32],
    /// Unused by direct discharge; names the (virtual-map) associated type.
    _map: std::marker::PhantomData<PreparedVirtualMap>,
}

impl ValidUntilSpec {
    fn new(circuit: Circuit) -> Self {
        let capacity = circuit.capacity();
        let s = &circuit.statement;
        let mut h = blake3::Hasher::new();
        h.update(b"bitz/valid-until/statement/v1");
        h.update(&(s.m as u64).to_le_bytes());
        h.update(&(s.prefix.len() as u64).to_le_bytes());
        h.update(&s.prefix);
        h.update(&s.validity_period.to_le_bytes());
        h.update(&s.current_unix_time.to_le_bytes());
        h.update(&[u8::from(circuit.strict)]);
        for count in circuit.counts {
            h.update(&(count as u64).to_le_bytes());
        }
        h.update(&(circuit.rows.len() as u64).to_le_bytes());
        Self {
            rows: circuit.compile(),
            gate_vars: capacity.trailing_zeros() as usize,
            statement_digest: *h.finalize().as_bytes(),
            capacity,
            circuit,
            _map: std::marker::PhantomData,
        }
    }

    pub fn circuit(&self) -> &Circuit {
        &self.circuit
    }

    /// BitZ geometry of the committed bit tensor.
    pub fn bitz_params(&self) -> IntegerMatrixLayout {
        bitz_params(self.gate_vars)
    }

    fn row_vars(&self) -> usize {
        self.rows.len().next_power_of_two().trailing_zeros().max(1) as usize
    }

    fn matrices_at(
        &self,
        config: &FieldConfig,
    ) -> Result<PreparedConstraintMatrices<SpartanBitzField, SpartanBitzField>, ProtocolError>
    {
        let zero = SpartanBitzField::zero_with_cfg(config);
        let to_field = |c: i128| {
            let magnitude = SpartanBitzField::from_with_cfg(c.unsigned_abs(), config);
            if c < 0 {
                config.sub(&zero, &magnitude)
            } else {
                magnitude
            }
        };
        let columns = 6 * self.capacity; // const + five blocks
        let build = |which: usize| {
            let rows: Vec<Vec<(usize, SpartanBitzField)>> = self
                .rows
                .iter()
                .map(|r| r[which].iter().map(|&(c, k)| (c, to_field(k))).collect())
                .collect();
            CscMatrix::try_from_rows(columns, rows)
                .map_err(SpartanMatrixError::from)
                .map_err(ProtocolError::relation)
        };
        let matrices = ConstraintMatrices::new(build(0)?, build(1)?, build(2)?)
            .map_err(ProtocolError::relation)?;
        PreparedConstraintMatrices::new(matrices, config).map_err(ProtocolError::relation)
    }
}

const fn bitz_params(gate_vars: usize) -> IntegerMatrixLayout {
    let s = gate_vars / 2;
    IntegerMatrixLayout {
        row_vars: 7 + gate_vars - s,
        col_vars: s,
    }
}

/// `(bit_slot, gate) -> (b, c)`, the row-major cell of the commitment grid.
const fn cell(gate_vars: usize, bit_slot: usize, gate: usize) -> (usize, usize) {
    let s = gate_vars / 2;
    let b = (bit_slot << (gate_vars - s)) | (gate >> s);
    let c = gate & ((1usize << s) - 1);
    (b, c)
}

impl RelationSpec for ValidUntilSpec {
    type Coefficient = SpartanBitzField;
    type Witness = ValidUntilWitness;
    type Map = PreparedVirtualMap;

    fn domains(&self) -> &'static Domains {
        &DOMAINS
    }

    fn committed_layout(&self) -> IntegerMatrixLayout {
        self.bitz_params()
    }

    fn gate_vars(&self) -> usize {
        self.gate_vars
    }

    fn instance_facts(&self) -> IopInstanceFacts {
        let p = self.bitz_params();
        IopInstanceFacts {
            // every row residual is < 2^64 in absolute value
            defect_log2_bound: 80,
            lift_arity_log2: p.row_vars as u32,
            opening_t: p.row_vars as u32,
            direct_opening: true,
            tau_arity: self.row_vars() as u32,
            piop_degree: 3,
            step50_magnitude_log2: 0,
        }
    }

    fn matrices(&self) -> Result<MatrixSource<SpartanBitzField>, ProtocolError> {
        Ok(MatrixSource::PerPrime)
    }

    fn project_matrices(
        &self,
        config: &FieldConfig,
    ) -> Result<PreparedConstraintMatrices<SpartanBitzField, SpartanBitzField>, ProtocolError>
    {
        self.matrices_at(config)
    }

    fn validate_geometry(&self) -> Result<(), ProtocolError> {
        let p = self.bitz_params();
        if p.row_vars < LOG_PACKING
            || p.col_vars > self.gate_vars
            || p.row_vars > 125
            || p.row_vars + p.col_vars != self.gate_vars + 7
            || SLOTS_PER_GATE != 1 << 7
            || self.rows.len() > self.capacity
            || SLOT_STARTS[5] + BLOCK_WIDTHS[5] > SLOTS_PER_GATE
        {
            return Err(ProtocolError::InvalidBitzParameters);
        }
        Ok(())
    }

    /// Selector order: 000 = constant, 001 = byte, 010 = nibble, 011 = flag,
    /// 100 = num, 101 = wide, 110/111 = public zero padding.
    fn block_table(&self) -> BlockTable {
        let block = |b: usize| {
            Some(SlotRange {
                bit_slot_start: SLOT_STARTS[b],
                bit_count: BLOCK_WIDTHS[b],
            })
        };
        BlockTable::new(
            SELECTOR_VARS,
            vec![None, block(1), block(2), block(3), block(4), block(5), None, None],
        )
        .expect("the valid-until block table is complete")
    }

    fn kernel(&self) -> Kernel {
        Kernel::Plain
    }

    fn check_witness(&self, witness: &ValidUntilWitness) -> Result<(), ProtocolError> {
        if witness.capacity != self.capacity {
            return Err(ProtocolError::RelationWitnessLayoutMismatch);
        }
        Ok(())
    }

    fn assignment_binding(
        &self,
        commitment: &Commitment,
        security: &IopSecurityParams,
        _ligerito: &LigProverConfig,
    ) -> Result<[u8; 32], ProtocolError> {
        let p = self.bitz_params();
        protocol::bind_assignment(BINDING_DOMAIN, BLOCK_ORDER, commitment, security, |hasher| {
            hasher.bytes(&self.statement_digest);
            hasher.usizes(&[self.capacity, self.gate_vars, p.row_vars, p.col_vars, 1usize])?;
            Ok(())
        })
    }

    fn hash_bridge_constants(&self, hasher: &mut BindingHasher) -> Result<(), ProtocolError> {
        let p = self.bitz_params();
        hasher.bytes(&self.statement_digest);
        hasher.usizes(&[self.capacity, self.gate_vars, p.row_vars, p.col_vars, 1usize])?;
        for b in 1..6 {
            hasher.usizes(&[SLOT_STARTS[b], BLOCK_WIDTHS[b]])?;
        }
        Ok(())
    }

    fn piop_witness<'w>(
        &self,
        witness: &'w ValidUntilWitness,
        config: &FieldConfig,
    ) -> Result<PiopWitness<'w>, ProtocolError> {
        use crate::piop::spartan::raw_monty::raw_shared;
        use field::{IntegerEmbedding, Uint};
        let flat = witness.assignment.flat(self.capacity);
        let assignment = flat
            .iter()
            .map(|&v| raw_shared(config.from_integer(&Uint::<1>::from_u64(v))))
            .collect();
        Ok(PiopWitness::FieldAssignment { assignment })
    }
}

/// The word assignment plus the compact committed bit rows.
#[derive(Clone, Debug)]
pub struct ValidUntilWitness {
    capacity: usize,
    assignment: Assignment,
}

impl ValidUntilWitness {
    /// Honest witness: the date window sits at `start` inside `mso`.
    pub fn new(circuit: &Circuit, mso: &[u8], start: usize) -> Result<Self, R1csError> {
        Ok(Self::from_assignment(circuit, circuit.fill(mso, start)?))
    }

    /// Any assignment (also adversarial ones; no honesty is imposed).
    pub fn from_assignment(circuit: &Circuit, assignment: Assignment) -> Self {
        Self {
            capacity: circuit.capacity(),
            assignment,
        }
    }

    pub fn assignment(&self) -> &Assignment {
        &self.assignment
    }

    /// Compact committed rows: `rows[c]` holds the bits of column `c`.
    pub fn bit_rows(&self) -> Vec<Vec<u64>> {
        let gate_vars = self.capacity.trailing_zeros() as usize;
        let p = bitz_params(gate_vars);
        let words_per_row = p.rows() / u64::BITS as usize;
        let mut rows = vec![vec![0u64; words_per_row]; p.cols()];
        for block in 1..6 {
            for (gate, &value) in self.assignment.values[block].iter().enumerate() {
                for bit in 0..BLOCK_WIDTHS[block] {
                    if value >> bit & 1 == 1 {
                        let (b, c) = cell(gate_vars, SLOT_STARTS[block] + bit, gate);
                        rows[c][b / 64] |= 1u64 << (b % 64);
                    }
                }
            }
        }
        rows
    }
}

enum Prepared {
    /// Validator-gated production opener (`gate_vars >= 15`).
    Production(PreparedRelation<ValidUntilSpec>),
    /// Small shapes: algebra only, provable with an explicit configuration.
    Unaudited(PreparedRelationPrefix<ValidUntilSpec>),
}

/// A prepared statement: circuit, matrices source and security profile.
pub struct PreparedValidUntil {
    prepared: Prepared,
}

impl PreparedValidUntil {
    fn prefix(&self) -> &PreparedRelationPrefix<ValidUntilSpec> {
        match &self.prepared {
            Prepared::Production(r) => r.prefix(),
            Prepared::Unaudited(p) => p,
        }
    }

    fn production(&self) -> Result<&PreparedRelation<ValidUntilSpec>, ProtocolError> {
        match &self.prepared {
            Prepared::Production(r) => Ok(r),
            Prepared::Unaudited(_) => Err(ProtocolError::UnauditedBitzParameters),
        }
    }

    pub fn circuit(&self) -> &Circuit {
        self.prefix().layout().circuit()
    }

    pub fn bitz_params(&self) -> IntegerMatrixLayout {
        self.prefix().layout().bitz_params()
    }

    pub fn is_production(&self) -> bool {
        matches!(self.prepared, Prepared::Production(_))
    }

    /// Serialized proof size in bytes (Spartan payload + nonces + BitZ opening).
    pub fn proof_size_bytes(&self, proof: &Proof) -> usize {
        proof.size_bytes(self.prefix().security())
    }
}

/// Builds the circuit of `statement` and prepares it for BitZ.
pub fn prepare_valid_until(
    statement: &Statement,
    strict: bool,
) -> Result<PreparedValidUntil, ProtocolError> {
    let circuit = Circuit::new(statement, strict).map_err(ProtocolError::relation)?;
    let spec = ValidUntilSpec::new(circuit);
    let gate_vars = spec.gate_vars;
    let prefix = PreparedRelationPrefix::new::<Lambda100>(spec)?;
    let prepared = if gate_vars >= protocol::MIN_PRODUCTION_GATE_VARS {
        Prepared::Production(PreparedRelation::with_ligerito(
            prefix,
            LigeritoSelection::JOHNSON,
        )?)
    } else {
        Prepared::Unaudited(prefix)
    };
    Ok(PreparedValidUntil { prepared })
}

/// Commits the witness bits under an explicit prover configuration (test-only
/// below the audited `gate_vars >= 15` regime).
pub fn commit_valid_until_with_config(
    relation: &PreparedValidUntil,
    witness: &ValidUntilWitness,
    pc: &LigProverConfig,
) -> Result<FlockCommitHint, ProtocolError> {
    let prefix = relation.prefix();
    prefix.layout().validate_geometry()?;
    prefix.layout().check_witness(witness)?;
    let p = prefix.params();
    let rows = witness.bit_rows();
    protocol::validate_bit_rows(&p, &rows)?;
    let hint = commit_rs_ligerito_rows(&p, rows, pc);
    protocol::validate_commitment(&p, &hint.commitment, pc)?;
    Ok(hint)
}

/// Commits under the production (validator-gated) configuration.
pub fn commit_valid_until(
    relation: &PreparedValidUntil,
    witness: &ValidUntilWitness,
) -> Result<FlockCommitHint, ProtocolError> {
    relation.production()?;
    let p = relation.bitz_params();
    let (pc, vc) = sha_lig_configs(packed_vars(&p)).map_err(ProtocolError::LigeritoConfig)?;
    protocol::validate_config_pair(&p, &pc, &vc)?;
    commit_valid_until_with_config(relation, witness, &pc)
}

/// Proves under an explicit prover configuration.
pub fn prove_valid_until_with_config<T: Transcript + Send>(
    transcript: &mut T,
    relation: &PreparedValidUntil,
    witness: &ValidUntilWitness,
    hint: &FlockCommitHint,
    pc: &LigProverConfig,
) -> Result<Proof, ProtocolError> {
    let opener = Opener::Custom {
        prover: Some(pc.clone()),
        verifier: None,
    };
    protocol::prove_with_opener(transcript, relation.prefix(), &opener, witness, hint)
}

/// Proves with the production opener.
pub fn prove_valid_until<T: Transcript + Send>(
    transcript: &mut T,
    relation: &PreparedValidUntil,
    witness: &ValidUntilWitness,
    hint: &FlockCommitHint,
) -> Result<Proof, ProtocolError> {
    protocol::prove(transcript, relation.production()?, witness, hint)
}

/// Verifies under an explicit verifier configuration.
pub fn verify_valid_until_with_config<T: Transcript + Send>(
    transcript: &mut T,
    relation: &PreparedValidUntil,
    commitment: &Commitment,
    proof: &Proof,
    vc: &LigVerifierConfig,
) -> Result<(), ProtocolError> {
    let opener = Opener::Custom {
        prover: None,
        verifier: Some(vc.clone()),
    };
    protocol::verify_with_opener(transcript, relation.prefix(), &opener, commitment, proof)
}

/// Verifies with the production opener.
pub fn verify_valid_until<T: Transcript + Send>(
    transcript: &mut T,
    relation: &PreparedValidUntil,
    commitment: &Commitment,
    proof: &Proof,
) -> Result<(), ProtocolError> {
    protocol::verify(transcript, relation.production()?, commitment, proof)
}
