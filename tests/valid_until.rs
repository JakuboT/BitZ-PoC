//! End-to-end tests of REL_validUntil on BitZ (integer R1CS -> Spartan ->
//! direct BitZ opening). Small shapes use an ad-hoc Ligerito configuration
//! (the audited production opener starts at `gate_vars >= 15`).

use std::panic::{AssertUnwindSafe, catch_unwind};

use bitz::ligerito::packed_vars;
use bitz::ligerito_flock::{LigConfig, lig_configs};
use bitz::piop::spartan::valid_until::r1cs::{BYTE, NUM};
use bitz::piop::spartan::valid_until::reference::{civil_to_unix, synthetic_mso};
use bitz::piop::spartan::valid_until::{
    PreparedValidUntil, Statement, ValidUntilWitness, commit_valid_until_with_config,
    prepare_valid_until, prove_valid_until_with_config, verify_valid_until_with_config,
};
use bitz::transcript::Blake3Transcript;

const PREFIX: &[u8] = b"\x6avalidUntil";
const DATE: &str = "2026-11-17T08:30:00Z";

fn statement(m: usize, now: u64, period: u64) -> Statement {
    Statement { m, prefix: PREFIX.to_vec(), validity_period: period, current_unix_time: now }
}

fn configs(
    rel: &PreparedValidUntil,
) -> (flock_core::pcs::ligerito::ProverConfig, flock_core::pcs::ligerito::VerifierConfig) {
    let p = rel.bitz_params();
    lig_configs(packed_vars(&p), LigConfig::Adhoc { log_batch: 2, log_inv_rate: 2 })
        .expect("ad-hoc configuration")
}

/// Prove `witness` for `prove_rel` and verify against `verify_rel`;
/// true iff an accepting proof came out.
fn accepted(
    prove_rel: &PreparedValidUntil,
    verify_rel: &PreparedValidUntil,
    witness: &ValidUntilWitness,
) -> bool {
    let (pc, vc) = configs(prove_rel);
    catch_unwind(AssertUnwindSafe(|| {
        let hint = commit_valid_until_with_config(prove_rel, witness, &pc).ok()?;
        let proof = prove_valid_until_with_config(
            &mut Blake3Transcript::new(), prove_rel, witness, &hint, &pc,
        )
        .ok()?;
        verify_valid_until_with_config(
            &mut Blake3Transcript::new(), verify_rel, &hint.commitment, &proof, &vc,
        )
        .ok()
    }))
    .ok()
    .flatten()
    .is_some()
}

fn setup(m: usize, start: usize) -> (u64, Vec<u8>) {
    let u = civil_to_unix(2026, 11, 17, 8, 30, 0) as u64;
    (u, synthetic_mso(m, start, PREFIX, DATE, 3))
}

#[test]
fn honest_witness_is_accepted() {
    for (m, start) in [(40, 0), (100, 33), (300, 211)] {
        let (u, mso) = setup(m, start);
        let rel = prepare_valid_until(&statement(m, u - 50, 1000), false).unwrap();
        let w = ValidUntilWitness::new(rel.circuit(), &mso, start).unwrap();
        assert!(accepted(&rel, &rel, &w), "honest proof rejected (m={m})");
    }
}

#[test]
fn strict_mode_honest_is_accepted() {
    let (u, mso) = setup(100, 33);
    let rel = prepare_valid_until(&statement(100, u - 50, 1000), true).unwrap();
    let w = ValidUntilWitness::new(rel.circuit(), &mso, 33).unwrap();
    assert!(accepted(&rel, &rel, &w));
}

#[test]
fn tampered_witness_is_rejected() {
    let (u, mso) = setup(100, 33);
    let rel = prepare_valid_until(&statement(100, u - 50, 1000), false).unwrap();
    let honest = ValidUntilWitness::new(rel.circuit(), &mso, 33).unwrap();
    for (block, idx) in [(BYTE, 3usize), (BYTE, 50), (NUM, 0), (NUM, 7)] {
        let mut a = honest.assignment().clone();
        a.values[block as usize][idx] ^= 1;
        let w = ValidUntilWitness::from_assignment(rel.circuit(), a);
        assert!(!accepted(&rel, &rel, &w), "tamper ({block},{idx}) accepted");
    }
}

#[test]
fn expired_certificate_is_rejected() {
    let (u, mso) = setup(100, 33);
    // now is after the end of the validity period: no honest witness exists
    let rel = prepare_valid_until(&statement(100, u + 5000, 1000), false).unwrap();
    let w = ValidUntilWitness::new(rel.circuit(), &mso, 33).unwrap();
    assert!(!accepted(&rel, &rel, &w));
}

#[test]
fn wrong_public_statement_is_rejected() {
    let (u, mso) = setup(100, 33);
    let good = prepare_valid_until(&statement(100, u - 50, 1000), false).unwrap();
    let w = ValidUntilWitness::new(good.circuit(), &mso, 33).unwrap();
    for other in [statement(100, u - 51, 1000), statement(100, u - 50, 999)] {
        let bad = prepare_valid_until(&other, false).unwrap();
        assert!(!accepted(&good, &bad, &w), "verifier accepted a different statement");
    }
}

/// Production (audited, validator-gated) opener: needs gate_vars >= 15.
#[test]
fn production_shape_roundtrips() {
    use bitz::piop::spartan::valid_until::{commit_valid_until, prove_valid_until, verify_valid_until};
    let (m, start) = (20_000, 12_345);
    let (u, mso) = setup(m, start);
    let rel = prepare_valid_until(&statement(m, u - 50, 1000), false).unwrap();
    assert!(rel.is_production(), "capacity {}", rel.circuit().capacity());
    let w = ValidUntilWitness::new(rel.circuit(), &mso, start).unwrap();
    let hint = commit_valid_until(&rel, &w).unwrap();
    let proof = prove_valid_until(&mut Blake3Transcript::new(), &rel, &w, &hint).unwrap();
    verify_valid_until(&mut Blake3Transcript::new(), &rel, &hint.commitment, &proof).unwrap();
}
