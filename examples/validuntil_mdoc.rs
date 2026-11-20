//! Times REL_validUntil on the MSOs of longfellow-zk's `mdoc_examples.h`.
//!
//! usage: validuntil_mdoc <data.txt> [idx ...]      (ad-hoc Ligerito, any shape)
//!        validuntil_mdoc --synthetic <m>           (random mso; production opener if gate_vars >= 15)
//! Data lines come from `extract_mdoc_examples.py`.
//! Timings are wall clock of one run each; memory is measured by the caller.

use std::time::Instant;

use bitz::ligerito::packed_vars;
use bitz::ligerito_flock::{LigConfig, lig_configs};
use bitz::piop::spartan::valid_until::reference::{civil_to_unix, synthetic_mso};
use bitz::piop::spartan::valid_until::{
    Statement, ValidUntilWitness, commit_valid_until, commit_valid_until_with_config,
    prepare_valid_until, prove_valid_until, prove_valid_until_with_config, verify_valid_until,
    verify_valid_until_with_config,
};
use bitz::transcript::Blake3Transcript;

const PREFIX: &[u8] = b"\x6avalidUntil";
const PERIOD: u64 = 400 * 86_400;

fn unix(iso: &str) -> u64 {
    let n = |a: usize, b: usize| iso[a..b].parse::<i64>().unwrap();
    civil_to_unix(n(0, 4), n(5, 7), n(8, 10), n(11, 13), n(14, 16), n(17, 19)) as u64
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

fn run(label: &str, mso: &[u8], start: usize, now: u64, period: u64) {
    let stmt = Statement {
        m: mso.len(),
        prefix: PREFIX.to_vec(),
        validity_period: period,
        current_unix_time: now,
    };
    let t = Instant::now();
    let rel = prepare_valid_until(&stmt, false).unwrap();
    let t_prep = ms(t);
    let w = ValidUntilWitness::new(rel.circuit(), mso, start).unwrap();
    let c = rel.circuit();
    let p = rel.bitz_params();
    let production = rel.is_production();
    let (pc, vc) = if production {
        (None, None)
    } else {
        let (pc, vc) = lig_configs(
            packed_vars(&p),
            LigConfig::Adhoc { log_batch: 2, log_inv_rate: 2 },
        )
        .unwrap();
        (Some(pc), Some(vc))
    };
    let t = Instant::now();
    let hint = match &pc {
        Some(pc) => commit_valid_until_with_config(&rel, &w, pc),
        None => commit_valid_until(&rel, &w),
    }
    .unwrap();
    let t_commit = ms(t);
    let t = Instant::now();
    let proof = match &pc {
        Some(pc) => prove_valid_until_with_config(&mut Blake3Transcript::new(), &rel, &w, &hint, pc),
        None => prove_valid_until(&mut Blake3Transcript::new(), &rel, &w, &hint),
    }
    .unwrap();
    let t_prove = ms(t);
    let t = Instant::now();
    match &vc {
        Some(vc) => verify_valid_until_with_config(
            &mut Blake3Transcript::new(), &rel, &hint.commitment, &proof, vc,
        ),
        None => verify_valid_until(&mut Blake3Transcript::new(), &rel, &hint.commitment, &proof),
    }
    .expect("honest proof must verify");
    let t_verify = ms(t);
    println!(
        "{label} m={} rows={} cap={} gv={} {} prep={t_prep:.1}ms commit={t_commit:.1}ms \
         prove={t_prove:.1}ms verify={t_verify:.1}ms proof={}B",
        mso.len(),
        c.num_rows(),
        c.capacity(),
        c.gate_vars(),
        if production { "PROD" } else { "ADHOC" },
        rel.proof_size_bytes(&proof),
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("--synthetic") {
        let m: usize = args[1].parse().unwrap();
        let now = unix("2026-11-17T08:30:00Z");
        let start = m / 2;
        let mso = synthetic_mso(m, start, PREFIX, "2026-11-17T08:30:00Z", 3);
        run("synthetic", &mso, start, now - 50, PERIOD);
        return;
    }
    let data = std::fs::read_to_string(&args[0]).unwrap();
    let only: Vec<usize> = args[1..].iter().map(|a| a.parse().unwrap()).collect();
    for line in data.lines().filter(|l| !l.starts_with('#')) {
        let f: Vec<&str> = line.split_whitespace().collect();
        let idx: usize = f[0].parse().unwrap();
        if !only.is_empty() && !only.contains(&idx) {
            continue;
        }
        let (now, until) = (unix(f[1]), unix(f[2]));
        assert!(now <= until && until - now < PERIOD, "example {idx} outside period");
        let mso: Vec<u8> = (0..f[3].len() / 2)
            .map(|i| u8::from_str_radix(&f[3][2 * i..2 * i + 2], 16).unwrap())
            .collect();
        let mut pat = PREFIX.to_vec();
        pat.extend_from_slice(&[0xc0, 0x74]);
        let start = mso.windows(pat.len()).position(|w| w == pat.as_slice()).unwrap();
        run(&format!("ex{idx:02}"), &mso, start, now, PERIOD);
    }
}
