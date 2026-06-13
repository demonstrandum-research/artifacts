//! Standalone CLI for the F_13 cap-assault pilot (attack angle 2).
//! Kept out of main.rs to avoid conflicts with sibling campaigns.
//!
//! Subcommands:
//!   arcs <out_dir> [--secs S] [--threads T] [--seed X]
//!       randomized miner for maximum mod-13 arcs (caps at 14 by Ball's
//!       theorem); writes STATUS_arcs.json and arcs.json into out_dir.
//!   seed <out_dir> --arcs <arcs.json> [--secs S] [--control C] [--free F]
//!        [--protected P] [--stall K] [--seed X]
//!       3-arm seeded-ILS comparison on the exact integer engine:
//!       control (recipe scratch) vs arc-seeded free vs arc-seeded protected.

use no5core::f13::{run_arcs, run_seeded, ArcsConfig, SeedConfig};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: f13run arcs <out_dir> [--secs S] [--threads T] [--seed X]\n       f13run seed <out_dir> --arcs <arcs.json> [--secs S] [--control C] [--free F] [--protected P] [--stall K] [--seed X]";
    if args.len() < 3 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let mut secs = 60.0f64;
    let mut threads = 8usize;
    let mut seed = 0xF13u64;
    let mut control = 2usize;
    let mut free = 3usize;
    let mut protected = 3usize;
    let mut stall = 250u64;
    let mut arcs_path = String::new();
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--secs" => {
                secs = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--threads" => {
                threads = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--seed" => {
                seed = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--control" => {
                control = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--free" => {
                free = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--protected" => {
                protected = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--stall" => {
                stall = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--arcs" => {
                arcs_path = args[i + 1].clone();
                i += 2;
            }
            other => {
                eprintln!("unknown flag {other}\n{usage}");
                std::process::exit(2);
            }
        }
    }
    let code = match args[1].as_str() {
        "arcs" => run_arcs(&ArcsConfig { secs, threads, seed, out_dir: args[2].clone() }),
        "seed" => {
            if arcs_path.is_empty() {
                eprintln!("seed requires --arcs <arcs.json>\n{usage}");
                std::process::exit(2);
            }
            run_seeded(&SeedConfig {
                secs,
                control,
                free,
                protected,
                seed,
                stall,
                arcs_path,
                out_dir: args[2].clone(),
            })
        }
        other => {
            eprintln!("unknown subcommand {other}\n{usage}");
            2
        }
    };
    std::process::exit(code);
}
