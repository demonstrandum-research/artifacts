//! CLI for the no-5-on-a-sphere exact search core.
//!
//! Subcommands:
//!   check <points.json> [n]          exact full-certificate check (all 5-subsets)
//!   saturation <points.json> [--brute]
//!                                    build incremental state, report addable cells;
//!                                    --brute cross-validates the whole blocked grid
//!                                    against an independent det5 recount
//!   witness <points.json> <x> <y> <z>
//!                                    print one quadruple of S blocking the given cell
//!   bench <points.json> [--secs S] [--threads T]
//!                                    remove+re-add churn benchmark at |S| = m
//!
//! Input files must be plain JSON arrays of [x,y,z] integer triples.

use no5core::*;
use std::time::Instant;

fn parse_points(s: &str) -> Result<Vec<Point>, String> {
    let mut nums: Vec<i64> = Vec::new();
    let mut cur: Option<(i64, bool)> = None; // (abs value, negative)
    let mut depth = 0i32;
    let mut maxdepth = 0i32;
    let flush = |cur: &mut Option<(i64, bool)>, nums: &mut Vec<i64>| {
        if let Some((v, neg)) = cur.take() {
            nums.push(if neg { -v } else { v });
        }
    };
    for ch in s.chars() {
        match ch {
            '[' => {
                flush(&mut cur, &mut nums);
                depth += 1;
                maxdepth = maxdepth.max(depth);
            }
            ']' => {
                flush(&mut cur, &mut nums);
                depth -= 1;
                if depth < 0 {
                    return Err("unbalanced brackets".into());
                }
            }
            ',' | ' ' | '\t' | '\r' | '\n' => flush(&mut cur, &mut nums),
            '-' => {
                if cur.is_some() {
                    return Err("misplaced '-'".into());
                }
                cur = Some((0, true));
            }
            '0'..='9' => {
                let (v, neg) = cur.unwrap_or((0, false));
                cur = Some((v * 10 + (ch as i64 - '0' as i64), neg));
            }
            _ => {
                return Err(format!(
                    "unexpected character {ch:?}: expected a plain JSON array of [x,y,z] integer triples"
                ))
            }
        }
    }
    flush(&mut cur, &mut nums);
    if depth != 0 {
        return Err("unbalanced brackets".into());
    }
    if maxdepth != 2 {
        return Err("expected nesting depth exactly 2: [[x,y,z],...]".into());
    }
    if nums.len() % 3 != 0 || nums.is_empty() {
        return Err(format!("number count {} not a positive multiple of 3", nums.len()));
    }
    Ok(nums
        .chunks(3)
        .map(|c| [c[0] as i32, c[1] as i32, c[2] as i32])
        .collect())
}

fn load_points(path: &str) -> Vec<Point> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });
    parse_points(&text).unwrap_or_else(|e| {
        eprintln!("cannot parse {path}: {e}");
        std::process::exit(2);
    })
}

fn cmd_check(path: &str, n: i32) -> i32 {
    let pts = load_points(path);
    let m = pts.len();
    // range + distinctness
    for p in &pts {
        if !p.iter().all(|&c| (0..n).contains(&c)) {
            println!("INVALID m={m} n={n}: point {:?} out of range", p);
            return 1;
        }
    }
    for i in 0..m {
        for j in i + 1..m {
            if pts[i] == pts[j] {
                println!("INVALID m={m} n={n}: duplicate point {:?}", pts[i]);
                return 1;
            }
        }
    }
    match find_zero_5subset(&pts) {
        None => {
            println!("VALID m={m} n={n}");
            0
        }
        Some(w) => {
            println!("INVALID m={m} n={n}: zero 5-subset {:?}", w);
            1
        }
    }
}

fn cmd_saturation(path: &str, brute: bool) -> i32 {
    let pts = load_points(path);
    let t0 = Instant::now();
    let st = SearchState::from_points(&pts);
    let build_ms = t0.elapsed().as_secs_f64() * 1e3;
    let addable = st.addable_cells();
    let valid = st.is_valid_set();
    let s = st.len() as u64;
    let trivial = if s >= 4 { (s - 1) * (s - 2) * (s - 3) / 6 } else { 0 };
    let min_unocc = (0..NCELLS)
        .filter(|&i| !st.is_occupied(i))
        .map(|i| st.blocked_count(i))
        .min()
        .unwrap_or(0);
    println!("m={} build_ms={:.1} valid_set={}", st.len(), build_ms, valid);
    println!(
        "addable_count={} min_blocked_unoccupied={} trivial_member_count={}",
        addable.len(),
        min_unocc,
        trivial
    );
    println!(
        "addable_cells={:?}",
        addable.iter().map(|&i| cell_point(i)).collect::<Vec<_>>()
    );
    if brute {
        let t1 = Instant::now();
        let bf = blocked_bruteforce(&pts);
        let agree = (0..NCELLS).all(|i| bf[i] == st.blocked_count(i));
        println!(
            "bruteforce_grid_match={} bruteforce_ms={:.0}",
            agree,
            t1.elapsed().as_secs_f64() * 1e3
        );
        if !agree {
            return 1;
        }
    }
    0
}

fn cmd_witness(path: &str, p: Point) -> i32 {
    let pts = load_points(path);
    let st = SearchState::from_points(&pts);
    let cell = cell_index(p);
    match st.blocking_witness(cell) {
        Some(q) => {
            println!(
                "cell {:?} blocked_by {:?} det5={}",
                p,
                q,
                det5(&q, p)
            );
            0
        }
        None => {
            println!("cell {:?} is unblocked (addable={})", p, st.is_addable_cell(cell));
            1
        }
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
}

fn bench_one(pts: &[Point], secs: f64, seed: u64) -> (u64, u64, u64, f64) {
    let mut st = SearchState::from_points(pts);
    let mut rng = Rng(seed | 1);
    // warmup
    for _ in 0..16 {
        let p = st.points()[(rng.next() % st.len() as u64) as usize];
        st.remove_point(p);
        st.add_point(p);
    }
    st.evals = 0;
    st.quads_processed = 0;
    let mut transitions = 0u64;
    let t0 = Instant::now();
    let mut elapsed;
    loop {
        for _ in 0..32 {
            let p = st.points()[(rng.next() % st.len() as u64) as usize];
            st.remove_point(p);
            st.add_point(p);
            transitions += 2;
        }
        elapsed = t0.elapsed().as_secs_f64();
        if elapsed >= secs {
            break;
        }
    }
    (transitions, st.evals, st.quads_processed, elapsed)
}

fn cmd_bench(path: &str, secs: f64, threads: usize) -> i32 {
    let pts = load_points(path);
    println!(
        "bench: |S|={} grid={}^3 ({} cells) secs={} threads={}",
        pts.len(),
        N,
        NCELLS,
        secs,
        threads
    );
    let results: Vec<(u64, u64, u64, f64)> = if threads <= 1 {
        vec![bench_one(&pts, secs, 0x9E3779B97F4A7C15)]
    } else {
        std::thread::scope(|sc| {
            let handles: Vec<_> = (0..threads)
                .map(|t| {
                    let pts = &pts;
                    sc.spawn(move || bench_one(pts, secs, 0x9E3779B97F4A7C15 ^ (t as u64) << 17))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    };
    let mut tot_trans = 0f64;
    let mut tot_evals = 0f64;
    let mut tot_quads = 0f64;
    for &(tr, ev, qu, el) in &results {
        tot_trans += tr as f64 / el;
        tot_evals += ev as f64 / el;
        tot_quads += qu as f64 / el;
    }
    let adds_per_sec = tot_trans / 2.0;
    // each add determines addability of ALL 2197 cells => amortized cell determinations
    let cell_determinations = adds_per_sec * NCELLS as f64;
    println!(
        "RESULT transitions_per_sec={:.0} adds_per_sec={:.0} quads_per_sec={:.0} quadcell_evals_per_sec={:.3e} cell_determinations_per_sec={:.3e} threads={}",
        tot_trans, adds_per_sec, tot_quads, tot_evals, cell_determinations, threads
    );
    println!(
        "RESULT_PER_THREAD transitions_per_sec={:.0} quadcell_evals_per_sec={:.3e} cell_determinations_per_sec={:.3e}",
        tot_trans / threads as f64,
        tot_evals / threads as f64,
        cell_determinations / threads as f64
    );
    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: no5core check <points.json> [n]\n       no5core saturation <points.json> [--brute]\n       no5core witness <points.json> <x> <y> <z>\n       no5core bench <points.json> [--secs S] [--threads T]\n       no5core ils <out_dir> [--secs S] [--threads T] [--pure P] [--seed X]";
    if args.len() < 3 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let code = match args[1].as_str() {
        "check" => {
            let n = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(13);
            cmd_check(&args[2], n)
        }
        "saturation" => cmd_saturation(&args[2], args.iter().any(|a| a == "--brute")),
        "witness" => {
            let p: Vec<i32> = args[3..6].iter().map(|s| s.parse().unwrap()).collect();
            cmd_witness(&args[2], [p[0], p[1], p[2]])
        }
        "bench" => {
            let mut secs = 5.0f64;
            let mut threads = 1usize;
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
                    other => {
                        eprintln!("unknown bench flag {other}\n{usage}");
                        std::process::exit(2);
                    }
                }
            }
            cmd_bench(&args[2], secs, threads)
        }
        "ils" => {
            let mut secs = 60.0f64;
            let mut threads = 8usize;
            let mut pure_threads: Option<usize> = None;
            let mut seed = 0x5EEDu64;
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
                    "--pure" => {
                        pure_threads = Some(args[i + 1].parse().unwrap());
                        i += 2;
                    }
                    "--seed" => {
                        seed = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    other => {
                        eprintln!("unknown ils flag {other}\n{usage}");
                        std::process::exit(2);
                    }
                }
            }
            let cfg = ils::IlsConfig {
                secs,
                threads,
                pure_threads: pure_threads.unwrap_or(threads / 2),
                seed,
                out_dir: args[2].clone(),
            };
            ils::run_ils(&cfg)
        }
        other => {
            eprintln!("unknown subcommand {other}\n{usage}");
            2
        }
    };
    std::process::exit(code);
}
