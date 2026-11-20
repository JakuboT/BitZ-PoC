//! `REL_validUntil extraction and verification` on BitZ.
//!
//! * [`reference`] - literal, naive implementation of the ten constraints (test oracle);
//! * [`r1cs`] - the same relation as an integer R1CS over committed words, with a
//!   witness generator and an integer satisfiability check.
//!
//! The BitZ (Spartan + opening) wiring lives in `proof` (step 3 of the plan).

pub mod proof;
pub mod r1cs;
pub mod reference;

pub use proof::{
    PreparedValidUntil, ValidUntilWitness, commit_valid_until, commit_valid_until_with_config,
    prepare_valid_until, prove_valid_until, prove_valid_until_with_config, verify_valid_until,
    verify_valid_until_with_config,
};
pub use r1cs::{Assignment, Circuit, R1csError};
pub use reference::{Statement, Witness};
