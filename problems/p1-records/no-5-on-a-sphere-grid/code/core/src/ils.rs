//! Baseline ILS — attack angle 6 ("reproduce-and-fix the published recipe").
//!
//! Faithful port of the evolved n=12 recipe from the official AlphaEvolve
//! notebook (cell "An example evolved code for n=12") onto the incremental
//! cofactor-vector core, generalized to n=13, with the notebook's admitted
//! harness bug FIXED: a shared, deduplicated elite population persists across
//! restarts and threads.
//!
//! Two arms run side by side:
//!   - "pure"  arm: the verbatim recipe per thread, no cross-seeding. This is
//!     the control: it measures how often record-grade sizes are reached from
//!     scratch by raw recipe + compute.
//!   - "fixed" arm: identical recipe, except the full-restart branch usually
//!     re-seeds `best` from the shared elite pool (the bug fix).
//!
//! Recipe fidelity notes (from the notebook source):
//!   - 12 sorting keys, ported exactly (incl. the n-dependent center keys).
//!   - initial build: greedy over all cells sorted by a uniformly random key.
//!   - per trial: with p = 0.15 full restart (70% key-sorted / 30% shuffled
//!     candidate order), else ruin-and-rebuild from `best`: remove
//!     randint(max(1, m/20), max(2, m/4)) uniform points (inclusive bounds,
//!     like Python's randint), rebuild greedily over all non-member cells
//!     (80% key-sorted / 20% shuffled).
//!   - acceptance: size >= best replaces best (plateau acceptance).
//!   - a greedy pass is monotone (adding points only blocks more cells), so
//!     every trial result is maximal/saturated in {0..12}^3 by construction.
//!
//! All arithmetic is exact integer arithmetic (via the core). NO floats in
//! any validity decision; floats appear only in progress statistics.

use crate::{cell_index, cell_point, find_zero_5subset, Point, SearchState, N, NCELLS};
use std::collections::HashMap;
use std::io::Write as IoWrite;
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const NKEYS: usize = 12;
const MAX_SIZE_STAT: usize = 40;
/// Elite sets stored (for re-seeding) per size class.
const ELITE_CAP_PER_SIZE: usize = 512;
/// Hard cap on the dedup map (memory guard; beyond it we only count).
const DEDUP_CAP: usize = 500_000;
/// JSONL logging caps per size class.
const LOG_CAP_32: usize = 2_000;
const LOG_CAP_33PLUS: usize = 10_000;

// ----------------------------- RNG (xorshift64*) ----------------------------

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        // splitmix64 scramble so nearby seeds decorrelate
        let mut z = seed.wrapping_add(0x9E3779B97F4A7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        Rng((z ^ (z >> 31)) | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    /// uniform in [0, n)
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    /// uniform in [a, b] inclusive (Python randint semantics)
    fn randint(&mut self, a: usize, b: usize) -> usize {
        a + self.below(b - a + 1)
    }
    /// uniform f64 in [0,1) — used ONLY for branch probabilities (never validity)
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    fn shuffle(&mut self, v: &mut [u16]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}

// ----------------------------- sorting keys ---------------------------------

/// The 12 sorting keys of the evolved recipe, as total-order tuples.
/// Python `sorted` is ascending over the tuple; we replicate with [i64; 5].
fn key_tuple(k: usize, p: Point) -> [i64; 5] {
    let (x, y, z) = (p[0] as i64, p[1] as i64, p[2] as i64);
    let r2 = x * x + y * y + z * z;
    let s = x + y + z;
    let mx = x.max(y).max(z);
    let n1 = (N - 1) as i64; // 12
    let cdist = (2 * x - n1).abs() + (2 * y - n1).abs() + (2 * z - n1).abs();
    let zeros = [x, y, z].iter().filter(|&&c| c == 0).count() as i64;
    let highs = [x, y, z].iter().filter(|&&c| c == n1).count() as i64;
    match k {
        0 => [r2, s, x, y, z],
        1 => [s, r2, x, y, z],
        2 => [-s, r2, x, y, z],
        3 => [x, y, z, 0, 0],
        4 => [-x, -y, -z, 0, 0],
        5 => [-mx, x, y, z, 0],
        6 => [mx, x, y, z, 0],
        7 => [s % 2, x, y, z, 0], // s >= 0, Python % agrees
        8 => [cdist, x, y, z, 0],
        9 => [-cdist, x, y, z, 0],
        10 => [-zeros, x, y, z, 0],
        11 => [-highs, x, y, z, 0],
        _ => unreachable!(),
    }
}

/// Precompute the 12 full-grid cell orders (sorting keys are static, so the
/// per-trial "sort the candidate pool" reduces to walking a fixed permutation
/// and skipping occupied cells).
fn sorted_orders() -> Vec<Vec<u16>> {
    (0..NKEYS)
        .map(|k| {
            let mut v: Vec<u16> = (0..NCELLS as u16).collect();
            v.sort_by_key(|&ci| key_tuple(k, cell_point(ci as usize)));
            v
        })
        .collect()
}

// --------------------------- canonical form ----------------------------------

/// Canonical form under the 48 symmetries of the cube {0..12}^3 (axis
/// permutations x coordinate flips c -> 12-c): the lexicographically smallest
/// sorted cell-index vector over all 48 images. Exact dedup key.
pub fn canonical_form(pts: &[Point]) -> Vec<u16> {
    const PERMS: [[usize; 3]; 6] = [
        [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
    ];
    let mut best: Option<Vec<u16>> = None;
    let mut img: Vec<u16> = vec![0; pts.len()];
    for perm in PERMS {
        for flips in 0..8u32 {
            for (slot, p) in img.iter_mut().zip(pts.iter()) {
                let mut q = [0i32; 3];
                for a in 0..3 {
                    let c = p[perm[a]];
                    q[a] = if flips >> a & 1 == 1 { N - 1 - c } else { c };
                }
                *slot = cell_index(q) as u16;
            }
            img.sort_unstable();
            if best.as_ref().is_none_or(|b| img < *b) {
                best = Some(img.clone());
            }
        }
    }
    best.unwrap()
}

// ------------------------------ shared state ---------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arm {
    Pure,
    Fixed,
}
impl Arm {
    fn name(self) -> &'static str {
        match self {
            Arm::Pure => "pure",
            Arm::Fixed => "fixed",
        }
    }
}

#[derive(Default, Clone)]
struct ArmStats {
    iters: u64,
    scratch_builds: u64,
    scratch_hist: Vec<u64>, // index = build size
    ils_trials: u64,
    accepts_improve: u64,
    accepts_equal: u64,
    rejects: u64,
    // plateau statistics while best == 33
    at33_trials: u64,
    at33_drop: u64,
    at33_same: u64,
    at33_move: u64,
    at33_up: u64,
    reseeds: u64, // fixed arm only: restarts seeded from the elite pool
}

struct FoundSet {
    ts: f64,
    worker: usize,
    arm: Arm,
    size: usize,
    points: Vec<Point>,
}

struct Event {
    ts: f64,
    worker: usize,
    arm: Arm,
    what: String,
}

struct Shared {
    best_size: usize,
    /// dedup key -> size, for every distinct canonical set ever pushed (>= 31)
    seen: HashMap<Vec<u16>, usize>,
    seen_overflow: u64,
    /// distinct canonical count per size (index = size), total and per arm
    /// (per-arm = arm of the FIRST finder of each canonical)
    distinct_per_size: Vec<u64>,
    distinct_pure: Vec<u64>,
    distinct_fixed: Vec<u64>,
    /// elite sets for re-seeding, per size: (distinct candidates seen, reservoir)
    elites: HashMap<usize, (u64, Vec<Vec<Point>>)>,
    pending_log: Vec<FoundSet>,
    logged_per_size: Vec<u64>,
    events: Vec<Event>,
    stats_pure: ArmStats,
    stats_fixed: ArmStats,
    candidate34: Option<Vec<Point>>,
    workers_done: usize,
}

impl Shared {
    fn new() -> Self {
        Shared {
            best_size: 0,
            seen: HashMap::new(),
            seen_overflow: 0,
            distinct_per_size: vec![0; MAX_SIZE_STAT],
            distinct_pure: vec![0; MAX_SIZE_STAT],
            distinct_fixed: vec![0; MAX_SIZE_STAT],
            elites: HashMap::new(),
            pending_log: Vec::new(),
            logged_per_size: vec![0; MAX_SIZE_STAT],
            events: Vec::new(),
            stats_pure: ArmStats { scratch_hist: vec![0; MAX_SIZE_STAT], ..Default::default() },
            stats_fixed: ArmStats { scratch_hist: vec![0; MAX_SIZE_STAT], ..Default::default() },
            candidate34: None,
            workers_done: 0,
        }
    }
}

// ------------------------------ worker logic ---------------------------------

pub struct IlsConfig {
    pub secs: f64,
    pub threads: usize,
    pub pure_threads: usize,
    pub seed: u64,
    pub out_dir: String,
}

struct Worker<'a> {
    tid: usize,
    arm: Arm,
    rng: Rng,
    st: SearchState,
    best: Vec<Point>,
    orders: &'a [Vec<u16>],
    shared: &'a Mutex<Shared>,
    t0: Instant,
    out_dir: &'a str,
    /// first time this worker's best reached size s (for s >= 30)
    reached: Vec<bool>,
    local: ArmStats,
}

impl<'a> Worker<'a> {
    /// Greedy pass on the live state: walk `order`, adding every addable
    /// cell. Monotone, so the result is maximal.
    fn greedy_pass(&mut self, order: &[u16]) {
        greedy_pass_into(&mut self.st, order);
    }

    /// Fresh from-scratch greedy build into a brand-new TEMP state (the live
    /// best state stays untouched so a rejected restart costs nothing to
    /// undo — Codex review, finding 2).
    fn scratch_state(&mut self, use_key: bool) -> SearchState {
        let mut st = SearchState::new();
        if use_key {
            let order = self.orders[self.rng.below(NKEYS)].clone();
            greedy_pass_into(&mut st, &order);
        } else {
            let mut order: Vec<u16> = (0..NCELLS as u16).collect();
            self.rng.shuffle(&mut order);
            greedy_pass_into(&mut st, &order);
        }
        let size = st.len().min(MAX_SIZE_STAT - 1);
        self.local.scratch_builds += 1;
        self.local.scratch_hist[size] += 1;
        st
    }

    /// Restore the live state to exactly `self.best` (after a rejected trial).
    fn restore_to_best(&mut self) {
        let cur: Vec<Point> = self.st.points().to_vec();
        for p in cur {
            if !self.best.contains(&p) {
                self.st.remove_point(p);
            }
        }
        for i in 0..self.best.len() {
            let p = self.best[i];
            if !self.st.is_occupied(cell_index(p)) {
                self.st.add_point(p);
            }
        }
        debug_assert_eq!(self.st.len(), self.best.len());
    }

    /// Adopt `seed_set` as the new local best and load it into the state.
    fn adopt(&mut self, seed_set: Vec<Point>) {
        self.best = seed_set;
        self.st = SearchState::from_points(&self.best);
    }

    fn now(&self) -> f64 {
        self.t0.elapsed().as_secs_f64()
    }

    /// Push a result set into the shared structures (dedup, elites, logging,
    /// best tracking, candidate-34 alarm). Called for sizes >= 31.
    fn push_shared(&mut self, pts: &[Point]) {
        let size = pts.len();
        if size < 31 {
            return;
        }
        // paranoia: exact full validation before anything record-adjacent is
        // stored. By construction every trial result is valid; trust nothing.
        if size >= 33 {
            assert!(
                find_zero_5subset(pts).is_none(),
                "INVALID set of size {size} produced by search — engine bug"
            );
        }
        let canon = canonical_form(pts);
        let ts = self.now();
        let rnd = self.rng.next();
        let mut sh = self.shared.lock().unwrap();
        // CANDIDATE-34 PATH FIRST: must run before any dedup early-return so a
        // 34-set can never be silently dropped (Codex review, finding 1).
        if size >= 34 && sh.candidate34.is_none() {
            sh.candidate34 = Some(pts.to_vec());
            sh.events.push(Event {
                ts,
                worker: self.tid,
                arm: self.arm,
                what: format!("CANDIDATE34 size={size}"),
            });
            // immediate, unconditional dump — never rely on the writer thread
            let path = format!("{}/CANDIDATE34_IMMEDIATE.json", self.out_dir);
            let _ = std::fs::write(&path, points_json(pts));
            eprintln!(
                "!!! CANDIDATE 34-SET FOUND by worker {} ({}) at t={ts:.1}s !!!",
                self.tid,
                self.arm.name()
            );
        }
        let is_new = if sh.seen.len() < DEDUP_CAP {
            match sh.seen.entry(canon) {
                std::collections::hash_map::Entry::Occupied(_) => false,
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(size);
                    true
                }
            }
        } else {
            sh.seen_overflow += 1;
            // over cap: still log record-grade sets (size >= 33), skip dedup
            size >= 33
        };
        if !is_new {
            return;
        }
        let sidx = size.min(MAX_SIZE_STAT - 1);
        sh.distinct_per_size[sidx] += 1;
        match self.arm {
            Arm::Pure => sh.distinct_pure[sidx] += 1,
            Arm::Fixed => sh.distinct_fixed[sidx] += 1,
        }
        if size > sh.best_size {
            sh.best_size = size;
            sh.events.push(Event {
                ts,
                worker: self.tid,
                arm: self.arm,
                what: format!("new_best size={size}"),
            });
        }
        // reservoir sampling per size class (uniform over all distinct
        // canonicals ever seen — avoids freezing on the first 512 basins)
        let (seen_count, reservoir) = sh.elites.entry(size).or_insert_with(|| (0, Vec::new()));
        *seen_count += 1;
        if reservoir.len() < ELITE_CAP_PER_SIZE {
            reservoir.push(pts.to_vec());
        } else {
            let j = (rnd % *seen_count) as usize;
            if j < ELITE_CAP_PER_SIZE {
                reservoir[j] = pts.to_vec();
            }
        }
        let log_cap = if size >= 33 { LOG_CAP_33PLUS } else { LOG_CAP_32 };
        if size >= 32 && sh.logged_per_size[sidx] < log_cap as u64 {
            sh.logged_per_size[sidx] += 1;
            sh.pending_log.push(FoundSet {
                ts,
                worker: self.tid,
                arm: self.arm,
                size,
                points: pts.to_vec(),
            });
        }
    }

    /// Sample an elite from the shared pool (fixed arm re-seeding).
    /// Prefers the current best size (p=0.7) over best-1 when both exist.
    fn sample_elite(&mut self) -> Option<Vec<Point>> {
        let pick_best = self.rng.unit() < 0.7;
        let r = self.rng.next();
        let sh = self.shared.lock().unwrap();
        let bs = sh.best_size;
        if bs == 0 {
            return None;
        }
        let mut sizes: Vec<usize> = Vec::new();
        if pick_best {
            sizes.extend([bs, bs.saturating_sub(1)]);
        } else {
            sizes.extend([bs.saturating_sub(1), bs]);
        }
        for s in sizes {
            if let Some((_, v)) = sh.elites.get(&s) {
                if !v.is_empty() {
                    return Some(v[(r % v.len() as u64) as usize].clone());
                }
            }
        }
        None
    }

    fn record_reached(&mut self) {
        let size = self.best.len();
        for s in 30..=size.min(MAX_SIZE_STAT - 1) {
            if !self.reached[s] {
                self.reached[s] = true;
                let ts = self.now();
                let mut sh = self.shared.lock().unwrap();
                sh.events.push(Event {
                    ts,
                    worker: self.tid,
                    arm: self.arm,
                    what: format!("worker_reached size={s}"),
                });
            }
        }
    }

    fn flush_stats(&mut self) {
        let mut sh = self.shared.lock().unwrap();
        let dst = match self.arm {
            Arm::Pure => &mut sh.stats_pure,
            Arm::Fixed => &mut sh.stats_fixed,
        };
        dst.iters += self.local.iters;
        dst.scratch_builds += self.local.scratch_builds;
        for i in 0..MAX_SIZE_STAT {
            dst.scratch_hist[i] += self.local.scratch_hist[i];
        }
        dst.ils_trials += self.local.ils_trials;
        dst.accepts_improve += self.local.accepts_improve;
        dst.accepts_equal += self.local.accepts_equal;
        dst.rejects += self.local.rejects;
        dst.at33_trials += self.local.at33_trials;
        dst.at33_drop += self.local.at33_drop;
        dst.at33_same += self.local.at33_same;
        dst.at33_move += self.local.at33_move;
        dst.at33_up += self.local.at33_up;
        dst.reseeds += self.local.reseeds;
        self.local = ArmStats { scratch_hist: vec![0; MAX_SIZE_STAT], ..Default::default() };
    }

    /// Acceptance + bookkeeping shared by all trial kinds. `result_state`:
    /// None  => the trial ran in-place on self.st (ILS branch);
    /// Some  => the trial built a temp state (scratch branches).
    fn settle_trial(&mut self, prev_size: usize, prev_canon33: Option<Vec<u16>>, temp: Option<SearchState>) {
        let trial_len = temp.as_ref().map_or(self.st.len(), |t| t.len());
        if prev_size == 33 {
            self.local.at33_trials += 1;
        }
        if trial_len >= prev_size && trial_len > 0 {
            if let Some(t) = temp {
                self.st = t;
            }
            let result: Vec<Point> = self.st.points().to_vec();
            if trial_len > prev_size {
                self.local.accepts_improve += 1;
                if prev_size == 33 {
                    self.local.at33_up += 1;
                }
            } else {
                self.local.accepts_equal += 1;
                if let Some(pc) = &prev_canon33 {
                    if canonical_form(&result) == *pc {
                        self.local.at33_same += 1;
                    } else {
                        self.local.at33_move += 1;
                    }
                }
            }
            self.best = result.clone();
            self.record_reached();
            self.push_shared(&result);
        } else {
            self.local.rejects += 1;
            if prev_size == 33 {
                self.local.at33_drop += 1;
            }
            if temp.is_none() {
                // in-place ILS trial failed: rebuild the live state to best
                self.restore_to_best();
            }
            // temp scratch trial failed: drop it, live state still == best
        }
    }

    fn run(&mut self, deadline: Instant) {
        // ---- initial build: greedy with a uniformly random key (recipe) ----
        let st = self.scratch_state(true);
        self.st = st;
        self.best = self.st.points().to_vec();
        self.record_reached();
        let snapshot = self.best.clone();
        self.push_shared(&snapshot);
        let mut last_flush = Instant::now();

        while Instant::now() < deadline {
            self.local.iters += 1;
            let full_restart = self.best.is_empty() || self.rng.unit() < 0.15;
            let prev_size = self.best.len();
            let prev_canon33 =
                if prev_size == 33 { Some(canonical_form(&self.best)) } else { None };

            if full_restart {
                // bug fix (fixed arm only): usually re-seed from the elite pool
                if self.arm == Arm::Fixed && self.rng.unit() < 0.75 {
                    if let Some(e) = self.sample_elite() {
                        // adopt only if at least as good (plateau acceptance);
                        // an equal-size foreign elite injects diversity.
                        if e.len() >= self.best.len() {
                            self.adopt(e);
                            self.local.reseeds += 1;
                            self.record_reached();
                            // a reseed is not a search trial: skip acceptance
                            // stats entirely (Codex review, finding 5)
                            continue;
                        }
                    }
                }
                // recipe restart: 70% key-sorted, 30% shuffled; temp state
                let use_key = self.rng.unit() < 0.7;
                let t = self.scratch_state(use_key);
                self.settle_trial(prev_size, prev_canon33, Some(t));
            } else {
                // ---- ILS ruin-and-rebuild from best ----
                self.local.ils_trials += 1;
                let m = self.best.len();
                let r = self.rng.randint((m / 20).max(1), (m / 4).max(2));
                if m <= r {
                    // recipe: degenerate case = scratch rebuild (80/20 probs)
                    let use_key = self.rng.unit() < 0.8;
                    let t = self.scratch_state(use_key);
                    self.settle_trial(prev_size, prev_canon33, Some(t));
                } else {
                    // choose r distinct victims (uniform, like random.sample)
                    let mut idx: Vec<u16> = (0..m as u16).collect();
                    for i in 0..r {
                        let j = i + self.rng.below(m - i);
                        idx.swap(i, j);
                    }
                    let victims: Vec<Point> =
                        idx[..r].iter().map(|&i| self.best[i as usize]).collect();
                    for v in victims {
                        self.st.remove_point(v);
                    }
                    // rebuild order: 80% key-sorted, 20% shuffled
                    if self.rng.unit() < 0.8 {
                        let order = self.orders[self.rng.below(NKEYS)].clone();
                        self.greedy_pass(&order);
                    } else {
                        let mut order: Vec<u16> = (0..NCELLS as u16).collect();
                        self.rng.shuffle(&mut order);
                        self.greedy_pass(&order);
                    }
                    self.settle_trial(prev_size, prev_canon33, None);
                }
            }

            if last_flush.elapsed() > Duration::from_secs(5) {
                self.flush_stats();
                last_flush = Instant::now();
            }
        }
        self.flush_stats();
        let mut sh = self.shared.lock().unwrap();
        sh.workers_done += 1;
    }
}

/// Greedy pass over `order` into an arbitrary state (monotone => maximal).
fn greedy_pass_into(st: &mut SearchState, order: &[u16]) {
    for &ci in order {
        if st.is_addable_cell(ci as usize) {
            st.add_point(cell_point(ci as usize));
        }
    }
}

// ------------------------------ JSON helpers ---------------------------------

fn points_json(pts: &[Point]) -> String {
    let body: Vec<String> =
        pts.iter().map(|p| format!("[{},{},{}]", p[0], p[1], p[2])).collect();
    format!("[{}]", body.join(","))
}

fn unix_now() -> f64 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs_f64()
}

fn arm_stats_json(s: &ArmStats) -> String {
    let hist: Vec<String> = (0..MAX_SIZE_STAT)
        .filter(|&i| s.scratch_hist[i] > 0)
        .map(|i| format!("\"{}\":{}", i, s.scratch_hist[i]))
        .collect();
    format!(
        "{{\"iters\":{},\"scratch_builds\":{},\"scratch_hist\":{{{}}},\"ils_trials\":{},\"accepts_improve\":{},\"accepts_equal\":{},\"rejects\":{},\"at33_trials\":{},\"at33_drop\":{},\"at33_same\":{},\"at33_move\":{},\"at33_up\":{},\"reseeds\":{}}}",
        s.iters, s.scratch_builds, hist.join(","), s.ils_trials, s.accepts_improve,
        s.accepts_equal, s.rejects, s.at33_trials, s.at33_drop, s.at33_same,
        s.at33_move, s.at33_up, s.reseeds
    )
}

// ------------------------------ entry point ----------------------------------

pub fn run_ils(cfg: &IlsConfig) -> i32 {
    std::fs::create_dir_all(&cfg.out_dir).expect("cannot create out dir");
    let orders = sorted_orders();
    let shared = Mutex::new(Shared::new());
    let t0 = Instant::now();
    let deadline = t0 + Duration::from_secs_f64(cfg.secs);
    let status_path = format!("{}/STATUS.json", cfg.out_dir);
    let start_unix = unix_now();
    // unique per run so re-using an out dir never mixes records
    let jsonl_path = format!("{}/found_sets_{}.jsonl", cfg.out_dir, start_unix as u64);
    assert!(
        cfg.pure_threads <= cfg.threads,
        "--pure must be <= --threads"
    );

    println!(
        "ils: n={N} threads={} (pure={}, fixed={}) secs={} seed={} out={}",
        cfg.threads,
        cfg.pure_threads,
        cfg.threads - cfg.pure_threads,
        cfg.secs,
        cfg.seed,
        cfg.out_dir
    );

    std::thread::scope(|sc| {
        for tid in 0..cfg.threads {
            let arm = if tid < cfg.pure_threads { Arm::Pure } else { Arm::Fixed };
            let orders = &orders;
            let shared = &shared;
            let out_dir = cfg.out_dir.as_str();
            let seed = cfg.seed ^ ((tid as u64 + 1) << 32);
            sc.spawn(move || {
                let mut w = Worker {
                    tid,
                    arm,
                    rng: Rng::new(seed),
                    st: SearchState::new(),
                    best: Vec::new(),
                    orders,
                    shared,
                    t0,
                    out_dir,
                    reached: vec![false; MAX_SIZE_STAT],
                    local: ArmStats { scratch_hist: vec![0; MAX_SIZE_STAT], ..Default::default() },
                };
                w.run(deadline);
            });
        }

        // ---- writer loop (this thread): STATUS + JSONL every ~15 s ----
        let mut jsonl = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&jsonl_path)
            .expect("cannot open jsonl");
        loop {
            let done = {
                let sh = shared.lock().unwrap();
                sh.workers_done == cfg.threads
            };
            // drain found sets
            let (pending, status) = {
                let mut sh = shared.lock().unwrap();
                let pending: Vec<FoundSet> = sh.pending_log.drain(..).collect();
                let elapsed = t0.elapsed().as_secs_f64();
                let hist_json = |h: &Vec<u64>| -> String {
                    (0..MAX_SIZE_STAT)
                        .filter(|&i| h[i] > 0)
                        .map(|i| format!("\"{}\":{}", i, h[i]))
                        .collect::<Vec<_>>()
                        .join(",")
                };
                let dps = hist_json(&sh.distinct_per_size);
                let dpure = hist_json(&sh.distinct_pure);
                let dfixed = hist_json(&sh.distinct_fixed);
                let events: Vec<String> = sh
                    .events
                    .iter()
                    .map(|e| {
                        format!(
                            "{{\"t\":{:.1},\"worker\":{},\"arm\":\"{}\",\"what\":\"{}\"}}",
                            e.ts, e.worker, e.arm.name(), e.what
                        )
                    })
                    .collect();
                let status = format!(
                    "{{\"start_unix\":{:.0},\"elapsed_secs\":{:.1},\"budget_secs\":{},\"threads\":{},\"pure_threads\":{},\"done\":{},\"workers_done\":{},\"best_size\":{},\"candidate34_found\":{},\"distinct_per_size\":{{{}}},\"distinct_pure\":{{{}}},\"distinct_fixed\":{{{}}},\"seen_total\":{},\"seen_overflow\":{},\"stats_pure\":{},\"stats_fixed\":{},\"events\":[{}]}}",
                    start_unix,
                    elapsed,
                    cfg.secs,
                    cfg.threads,
                    cfg.pure_threads,
                    done,
                    sh.workers_done,
                    sh.best_size,
                    sh.candidate34.is_some(),
                    dps,
                    dpure,
                    dfixed,
                    sh.seen.len(),
                    sh.seen_overflow,
                    arm_stats_json(&sh.stats_pure),
                    arm_stats_json(&sh.stats_fixed),
                    events.join(",")
                );
                (pending, status)
            };
            for f in &pending {
                let line = format!(
                    "{{\"t\":{:.1},\"worker\":{},\"arm\":\"{}\",\"size\":{},\"points\":{}}}\n",
                    f.ts, f.worker, f.arm.name(), f.size, points_json(&f.points)
                );
                let _ = jsonl.write_all(line.as_bytes());
            }
            let _ = jsonl.flush();
            let _ = std::fs::write(&status_path, &status);
            if done {
                break;
            }
            // safety valve: if a worker panicked, workers_done never reaches
            // the thread count — don't hang the writer forever (Codex, finding 3)
            if t0.elapsed().as_secs_f64() > cfg.secs + 600.0 {
                eprintln!("ils: writer safety valve tripped — workers stalled past deadline+600s");
                break;
            }
            std::thread::sleep(Duration::from_secs(15));
        }
    });

    // ---- final summary ----
    let sh = shared.lock().unwrap();
    println!(
        "ils done: best_size={} distinct@best={} candidate34={}",
        sh.best_size,
        sh.distinct_per_size[sh.best_size.min(MAX_SIZE_STAT - 1)],
        sh.candidate34.is_some()
    );
    if let Some(c) = &sh.candidate34 {
        let path = format!("{}/CANDIDATE34_FINAL.json", cfg.out_dir);
        let _ = std::fs::write(&path, points_json(c));
        println!("!!! 34-SET SAVED to {path} !!!");
        return 0;
    }
    0
}

// ------------------------------ tests ----------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orders_are_permutations() {
        for ord in sorted_orders() {
            let mut v = ord.clone();
            v.sort_unstable();
            assert_eq!(v, (0..NCELLS as u16).collect::<Vec<_>>());
        }
    }

    #[test]
    fn key0_starts_at_origin_key4_starts_at_corner() {
        let orders = sorted_orders();
        assert_eq!(cell_point(orders[0][0] as usize), [0, 0, 0]);
        assert_eq!(cell_point(orders[4][0] as usize), [12, 12, 12]);
        assert_eq!(cell_point(orders[3][0] as usize), [0, 0, 0]);
        assert_eq!(cell_point(orders[3][NCELLS - 1] as usize), [12, 12, 12]);
    }

    #[test]
    fn canonical_form_invariant_under_symmetry() {
        let pts: Vec<Point> = vec![[0, 1, 2], [3, 4, 5], [12, 0, 7], [6, 6, 6], [1, 11, 3]];
        let base = canonical_form(&pts);
        // apply an arbitrary symmetry: permute (z,x,y), flip x and z
        let img: Vec<Point> =
            pts.iter().map(|p| [12 - p[2], p[0], 12 - p[1]]).collect();
        assert_eq!(canonical_form(&img), base);
        // and a different set must (generically) differ
        let other: Vec<Point> = vec![[0, 1, 2], [3, 4, 5], [12, 0, 7], [6, 6, 6], [2, 11, 3]];
        assert_ne!(canonical_form(&other), base);
    }

    #[test]
    fn greedy_pass_is_maximal_and_valid() {
        let orders = sorted_orders();
        let shared = Mutex::new(Shared::new());
        let mut w = Worker {
            tid: 0,
            arm: Arm::Pure,
            rng: Rng::new(42),
            st: SearchState::new(),
            best: Vec::new(),
            orders: &orders,
            shared: &shared,
            t0: Instant::now(),
            out_dir: ".",
            reached: vec![false; MAX_SIZE_STAT],
            local: ArmStats { scratch_hist: vec![0; MAX_SIZE_STAT], ..Default::default() },
        };
        // NOTE: several recipe keys (e.g. lexicographic) start with 4 collinear
        // or cocircular cells, which block the whole grid — the published
        // recipe has the same property. Test with key 0 (origin-distance),
        // which is a known-good starter.
        w.st = SearchState::new();
        let order0 = w.orders[0].clone();
        w.greedy_pass(&order0);
        let pts = w.st.points().to_vec();
        assert!(pts.len() >= 20, "greedy build unexpectedly small: {}", pts.len());
        assert!(find_zero_5subset(&pts).is_none(), "greedy build invalid");
        assert!(w.st.addable_cells().is_empty(), "greedy build not maximal");
        // restore_to_best round-trip
        w.best = pts.clone();
        w.st.remove_point(pts[0]);
        w.st.remove_point(pts[5]);
        w.restore_to_best();
        let mut a = w.st.points().to_vec();
        let mut b = pts.clone();
        a.sort_unstable();
        b.sort_unstable();
        assert_eq!(a, b);
    }
}
