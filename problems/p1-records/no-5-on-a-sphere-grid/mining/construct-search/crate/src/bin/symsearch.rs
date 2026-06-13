//! Central-inversion symmetric pilot search (dossier attack angle 3) for the
//! no-5-on-a-sphere grid problem, n = 13 (AlphaEvolve Problem 6.60).
//!
//! Searches for S in {0..12}^3 invariant under the central inversion
//! sigma(p) = (12,12,12) - p about the true center c = (6,6,6).
//! 34 points = 17 orbit-pairs. The center cell itself is excluded (center +
//! any two orbit-pairs is automatically 5-coplanar: every two orbit-pairs
//! form a parallelogram whose diagonals meet at c).
//!
//! Exact structural facts used (all integer-exact, no floats anywhere):
//!  * Two orbit-pairs {p,sp},{q,sq} always form a parallelogram (coplanar
//!    4-set: LEGAL). It is COCIRCULAR — a rank-degenerate, all-cell-blocking
//!    quadruple — iff the parallelogram is a rectangle, iff the diagonals are
//!    equal, iff |p-c|^2 == |q-c|^2. Hence all pairs in a live symmetric set
//!    must occupy pairwise DISTINCT shells r2 = |p-c|^2 in {1..108}
//!    (used_shell filter; an exact, lossless pruning).
//!  * 4-collinear {p,sp,q,sq} (both pairs on one central line) is also
//!    rank-degenerate; shells differ so the shell filter does not see it, but
//!    it and every other degenerate quad involving both new points is caught
//!    by the exact pair-addability check below. Degenerate quads with >= 3
//!    old points are impossible to add: blocked[] catches them via any 4th
//!    old point (|S| >= 4 in all reachable states with quads).
//!  * Pair addability is decided EXACTLY, without touching the state:
//!      (1) cheap filter: cells p and sp unoccupied with blocked == 0
//!          (covers every 5-subset {4 old + 1 new}), shell unused;
//!      (2) cofactor_vec(x, y, p, sp) != 0 over all member 2-subsets {x,y}
//!          (covers all rank-degenerate quads containing both new points);
//!      (3) det5({x,y,z,p}, sp) != 0 over all member 3-subsets
//!          (covers every 5-subset containing both new points).
//!    Together these cover every 5-subset and every degenerate quadruple of
//!    S + {p, sp}; a belt-and-braces full degenerate sweep and is_valid_set()
//!    assertions run continuously during the search.
//!
//! Algorithm: GRASP/ILS over orbit-pairs. Greedy randomized fill to
//! saturation; ruin-and-rebuild (remove r in {1,2,3} random pairs, rebuild
//! with the removed pairs tabu, then final fill without tabu); accept if the
//! pair count did not drop, else revert; restart from scratch after `stall`
//! iterations without a restart-best improvement. At good local optima an
//! ASYMMETRIC greedy extension is measured (and reverted) to record how close
//! symmetric optima are to 33/34-point sets; any 34-point set found by either
//! route is brute-force re-verified and dumped immediately.
//!
//! Usage:
//!   symsearch <out_dir> [--secs S] [--threads T] [--seed X] [--stall N] [--extmin K] [--target P]
//! Writes STATUS.json (every ~10 s), best_sym.json, best_total.json,
//! pool_16p.jsonl, pool_total33.jsonl, pool_34.jsonl (every distinct >= 34-point
//! set, brute-force re-verified before pooling) and, when a set with >= P
//! points (default 35) is found, FOUND_TARGET_*.json + FOUND.flag, then stops.
//! 34-point sets do NOT stop the run unless --target 34: the pilot already
//! secured 34 and hunts 35 (17 pairs + 1 asymmetric point, or 18 pairs).
//! Exit code 3 iff the target was reached.

use no5core::*;
use std::fs;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Scaled shell 4*|p-c|^2 = sum (2 p_i - (N-1))^2 about the true center
/// c = ((N-1)/2,)*3 (half-integral when N is even — the x4 scaling keeps
/// everything in integers for BOTH parities; equal true shells iff equal
/// scaled shells, so the rectangle/cocircular degeneracy argument carries).
const NSHELL: usize = (3 * ((N as i64 - 1) * (N as i64 - 1)) + 1) as usize;
const HIST_P: usize = 40; // pair-count histogram bins
const HIST_T: usize = 80; // total-point-count histogram bins

#[inline]
fn mirror(p: Point) -> Point {
    [N - 1 - p[0], N - 1 - p[1], N - 1 - p[2]]
}

#[inline]
fn shell(p: Point) -> usize {
    let d = |v: i32| {
        let t = (2 * v - (N - 1)) as i64;
        (t * t) as usize
    };
    d(p[0]) + d(p[1]) + d(p[2])
}

/// Orbit representatives: the cells with cell_index(p) < cell_index(sigma p).
/// For odd N the fixed center cell is excluded automatically; for even N
/// sigma is fixed-point-free and the reps are exactly half the cells.
fn orbit_reps() -> Vec<Point> {
    (0..NCELLS)
        .map(cell_point)
        .filter(|&p| cell_index(p) < cell_index(mirror(p)))
        .collect()
}

/// xorshift64* — deterministic, no external deps (same generator as the
/// existing bench/ILS code).
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
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}

/// Exact pair-addability core (steps 2+3 of the module docs). `pts` is the
/// current symmetric set; `p` an orbit rep whose cells already passed the
/// cheap blocked[]==0 filter. Returns true iff adding {p, sigma p} would
/// create a zero 5-subset or a rank-degenerate quadruple.
fn pair_conflict_exact(pts: &[Point], p: Point) -> bool {
    let q = mirror(p);
    let m = pts.len();
    // (2) rank-degenerate quads {x, y, p, q} (4-collinear through c, or
    //     cocircular): zero cofactor vector.
    for i in 0..m {
        for j in i + 1..m {
            if cofactor_vec(&[pts[i], pts[j], p, q]) == [0i64; 5] {
                return true;
            }
        }
    }
    // (3) zero 5-subsets containing both new points: {x, y, z, p, q}.
    for i in 0..m {
        for j in i + 1..m {
            for k in j + 1..m {
                if det5(&[pts[i], pts[j], pts[k], p], q) == 0 {
                    return true;
                }
            }
        }
    }
    false
}

/// Belt-and-braces invariant sweep: number of rank-degenerate 4-subsets
/// (zero cofactor vector) in the whole set. Must be 0 in every live state.
fn degenerate_quad_count(pts: &[Point]) -> usize {
    let m = pts.len();
    let mut n = 0;
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    if cofactor_vec(&[pts[a], pts[b], pts[c], pts[d]]) == [0i64; 5] {
                        n += 1;
                    }
                }
            }
        }
    }
    n
}

/// Order-independent FNV hash of a point set (for cheap dedup of pool writes).
fn set_hash(pts: &[Point]) -> u64 {
    let mut cells: Vec<u16> = pts.iter().map(|&p| cell_index(p) as u16).collect();
    cells.sort_unstable();
    let mut h = 0xcbf29ce484222325u64;
    for c in cells {
        h = (h ^ c as u64).wrapping_mul(0x100000001b3);
    }
    h
}

fn points_json(pts: &[Point]) -> String {
    let mut sorted: Vec<Point> = pts.to_vec();
    sorted.sort_by_key(|&p| cell_index(p));
    let mut s = String::from("[");
    for (i, p) in sorted.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&format!("[{},{},{}]", p[0], p[1], p[2]));
    }
    s.push(']');
    s
}

fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

// --------------------------- shared aggregator -------------------------------

struct BestLocked {
    pairs: usize,
    total: usize,
    pool_sym_lines: u32,
    pool_total_lines: u32,
}

struct Global {
    stop: AtomicBool,
    found34: AtomicBool,
    /// stop only at >= target points (pilot phase 2: 35)
    target: usize,
    sets34_pooled: AtomicU64,
    iters: AtomicU64,
    restarts: AtomicU64,
    accept_improve: AtomicU64,
    accept_lateral: AtomicU64,
    reverts: AtomicU64,
    ext_runs: AtomicU64,
    pair_adds: AtomicU64,
    exact_checks: AtomicU64,
    exact_rejects: AtomicU64,
    best_pairs_a: AtomicU64,
    best_total_a: AtomicU64,
    locopt_hist: Vec<AtomicU64>,        // local-optimum pair counts
    restart_pairs_hist: Vec<AtomicU64>, // per-restart max pair count
    restart_total_hist: Vec<AtomicU64>, // per-restart max total points (with asym ext)
    thread_best: Vec<AtomicU64>,
    best: Mutex<BestLocked>,
    out_dir: PathBuf,
}

impl Global {
    fn new(out_dir: PathBuf, threads: usize, target: usize) -> Self {
        let mkhist = |n: usize| (0..n).map(|_| AtomicU64::new(0)).collect::<Vec<_>>();
        Global {
            stop: AtomicBool::new(false),
            found34: AtomicBool::new(false),
            target,
            sets34_pooled: AtomicU64::new(0),
            iters: AtomicU64::new(0),
            restarts: AtomicU64::new(0),
            accept_improve: AtomicU64::new(0),
            accept_lateral: AtomicU64::new(0),
            reverts: AtomicU64::new(0),
            ext_runs: AtomicU64::new(0),
            pair_adds: AtomicU64::new(0),
            exact_checks: AtomicU64::new(0),
            exact_rejects: AtomicU64::new(0),
            best_pairs_a: AtomicU64::new(0),
            best_total_a: AtomicU64::new(0),
            locopt_hist: mkhist(HIST_P),
            restart_pairs_hist: mkhist(HIST_P),
            restart_total_hist: mkhist(HIST_T),
            thread_best: mkhist(threads),
            best: Mutex::new(BestLocked {
                pairs: 0,
                total: 0,
                pool_sym_lines: 0,
                pool_total_lines: 0,
            }),
            out_dir,
        }
    }

    fn pool_append(&self, fname: &str, pts: &[Point], counter: impl Fn(&mut BestLocked) -> &mut u32) {
        let mut b = self.best.lock().unwrap();
        let c = counter(&mut b);
        if *c >= 5000 {
            return; // cap pool files
        }
        *c += 1;
        if let Ok(mut f) =
            fs::OpenOptions::new().create(true).append(true).open(self.out_dir.join(fname))
        {
            let _ = writeln!(f, "{}", points_json(pts));
        }
    }

    /// Called with the symmetric set at every local optimum.
    fn record_locopt_set(&self, pts: &[Point]) {
        let pairs = pts.len() / 2;
        if (pairs as u64) > self.best_pairs_a.load(Relaxed) {
            // independent brute-force re-verification before publishing
            assert!(
                find_zero_5subset(pts).is_none(),
                "BUG: candidate best symmetric set failed brute-force validation"
            );
            let mut b = self.best.lock().unwrap();
            if pairs > b.pairs {
                b.pairs = pairs;
                self.best_pairs_a.store(pairs as u64, Relaxed);
                let _ = fs::write(self.out_dir.join("best_sym.json"), points_json(pts));
            }
        }
        if pts.len() >= self.target {
            self.found(pts, "sym");
        }
    }

    /// Archive a distinct large symmetric set (worker pre-deduplicates by
    /// hash); every pooled set is independently brute-force re-verified first.
    fn pool_sym(&self, pts: &[Point]) {
        assert!(
            find_zero_5subset(pts).is_none(),
            "BUG: symmetric pool candidate failed brute-force validation"
        );
        self.sets34_pooled.fetch_add(1, Relaxed);
        self.pool_append("pool_sym.jsonl", pts, |b| &mut b.pool_sym_lines);
    }

    /// Called with any (possibly asymmetric) valid superset reached by greedy
    /// extension, and with symmetric sets via record_locopt_set callers.
    fn record_total_set(&self, pts: &[Point]) {
        let total = pts.len();
        if (total as u64) > self.best_total_a.load(Relaxed) {
            assert!(
                find_zero_5subset(pts).is_none(),
                "BUG: candidate best total set failed brute-force validation"
            );
            let mut b = self.best.lock().unwrap();
            if total > b.total {
                b.total = total;
                self.best_total_a.store(total as u64, Relaxed);
                let _ = fs::write(self.out_dir.join("best_total.json"), points_json(pts));
            }
        }
        if total >= self.target {
            self.found(pts, "total");
        }
    }

    fn found(&self, pts: &[Point], tag: &str) {
        assert!(
            find_zero_5subset(pts).is_none(),
            "BUG: FOUND candidate failed brute-force validation"
        );
        let js = points_json(pts);
        let m = pts.len();
        let _ = fs::write(self.out_dir.join(format!("FOUND{m}_{tag}.json")), &js);
        let _ = fs::write(self.out_dir.join("FOUND.flag"), &js);
        self.found34.store(true, Relaxed);
        self.stop.store(true, Relaxed);
        eprintln!("\n!!!!! FOUND {m}-POINT SET ({tag}) — NEW WORLD RECORD CANDIDATE !!!!!");
        eprintln!("{js}\n");
    }
}

// ------------------------------- worker --------------------------------------

struct Cfg {
    stall: u64,
    extmin: usize,
    /// archive symmetric local optima with >= this many pairs
    pool_pairs: usize,
    /// archive (possibly asymmetric) extended sets with >= this many points
    pool_total: usize,
}

struct Worker<'g> {
    st: SearchState,
    used_shell: [bool; NSHELL],
    pairs: Vec<Point>, // orbit reps of current pairs
    rng: Rng,
    reps: &'g [Point],
    g: &'g Global,
    cfg: &'g Cfg,
    tid: usize,
    restart_max_pairs: usize,
    restart_max_total: usize,
    since_improve: u64,
    iter_in_restart: u64,
    last_pool34_hash: u64,
    last_ext34_hash: u64,
}

impl<'g> Worker<'g> {
    fn new(tid: usize, seed: u64, reps: &'g [Point], g: &'g Global, cfg: &'g Cfg) -> Self {
        Worker {
            st: SearchState::new(),
            used_shell: [false; NSHELL],
            pairs: Vec::new(),
            rng: Rng(seed | 1),
            reps,
            g,
            cfg,
            tid,
            restart_max_pairs: 0,
            restart_max_total: 0,
            since_improve: 0,
            iter_in_restart: 0,
            last_pool34_hash: 0,
            last_ext34_hash: 0,
        }
    }

    fn reset(&mut self) {
        self.st = SearchState::new();
        self.used_shell = [false; NSHELL];
        self.pairs.clear();
        self.restart_max_pairs = 0;
        self.restart_max_total = 0;
        self.since_improve = 0;
        self.iter_in_restart = 0;
    }

    fn add_pair(&mut self, p: Point) {
        self.st.add_point(p);
        self.st.add_point(mirror(p));
        // exact validity invariant, O(|S|) via the maintained blocked grid
        assert!(self.st.is_valid_set(), "BUG: pair add broke validity at {:?}", p);
        let sh = shell(p);
        assert!(!self.used_shell[sh], "BUG: duplicate shell {sh}");
        self.used_shell[sh] = true;
        self.pairs.push(p);
        self.g.pair_adds.fetch_add(1, Relaxed);
    }

    fn remove_pair(&mut self, p: Point) {
        self.st.remove_point(p);
        self.st.remove_point(mirror(p));
        self.used_shell[shell(p)] = false;
        let i = self.pairs.iter().position(|&x| x == p).unwrap();
        self.pairs.swap_remove(i);
    }

    fn candidates(&self, tabu: &[Point]) -> Vec<Point> {
        self.reps
            .iter()
            .copied()
            .filter(|&p| {
                self.st.is_addable_cell(cell_index(p))
                    && self.st.is_addable_cell(cell_index(mirror(p)))
                    && !self.used_shell[shell(p)]
                    && !tabu.contains(&p)
            })
            .collect()
    }

    /// Greedy randomized fill to saturation (w.r.t. non-tabu pairs).
    fn greedy_fill(&mut self, tabu: &[Point]) {
        loop {
            let mut cands = self.candidates(tabu);
            if cands.is_empty() {
                return;
            }
            self.rng.shuffle(&mut cands);
            let mut added = false;
            for &p in &cands {
                self.g.exact_checks.fetch_add(1, Relaxed);
                if pair_conflict_exact(self.st.points(), p) {
                    self.g.exact_rejects.fetch_add(1, Relaxed);
                } else {
                    self.add_pair(p);
                    added = true;
                    break;
                }
            }
            if !added {
                return;
            }
        }
    }

    /// Measure the greedy ASYMMETRIC extension of the current symmetric local
    /// optimum (then restore the state). Records 33+/34+ discoveries.
    fn extend_stat(&mut self) -> usize {
        self.g.ext_runs.fetch_add(1, Relaxed);
        let mut added: Vec<Point> = Vec::new();
        loop {
            let cells = self.st.addable_cells();
            if cells.is_empty() {
                break;
            }
            let p = cell_point(cells[self.rng.below(cells.len())]);
            self.st.add_point(p);
            added.push(p);
        }
        let total = self.st.len();
        if !added.is_empty() {
            assert!(self.st.is_valid_set(), "BUG: asym extension broke validity");
            if total >= self.cfg.pool_total {
                let h = set_hash(self.st.points());
                if h != self.last_ext34_hash {
                    self.last_ext34_hash = h;
                    assert!(
                        find_zero_5subset(self.st.points()).is_none(),
                        "BUG: total pool candidate failed brute-force validation"
                    );
                    self.g.pool_append("pool_total.jsonl", self.st.points(), |b| {
                        &mut b.pool_total_lines
                    });
                }
            }
            self.g.record_total_set(self.st.points());
            for &p in &added {
                self.st.remove_point(p);
            }
        }
        total
    }

    /// Bookkeeping at every local optimum (saturated symmetric state).
    fn note_locopt(&mut self) {
        let np = self.pairs.len();
        self.g.locopt_hist[np.min(HIST_P - 1)].fetch_add(1, Relaxed);
        self.g.record_locopt_set(self.st.points());
        if np >= self.cfg.pool_pairs {
            // archive every distinct large symmetric local optimum
            let h = set_hash(self.st.points());
            if h != self.last_pool34_hash {
                self.last_pool34_hash = h;
                self.g.pool_sym(self.st.points());
            }
        }
        let mut total = 2 * np;
        if np >= self.cfg.extmin {
            total = self.extend_stat();
        }
        if np > self.restart_max_pairs {
            self.restart_max_pairs = np;
            self.since_improve = 0;
        } else {
            self.since_improve += 1;
        }
        self.restart_max_total = self.restart_max_total.max(total);
        let tb = &self.g.thread_best[self.tid];
        if (np as u64) > tb.load(Relaxed) {
            tb.store(np as u64, Relaxed);
        }
    }

    /// One ILS step: ruin r pairs, rebuild (removed pairs tabu, then free),
    /// accept iff the pair count did not drop, else revert exactly.
    fn iterate(&mut self) {
        let saved = self.pairs.clone();
        let cur = saved.len();
        if cur == 0 {
            self.greedy_fill(&[]);
            self.note_locopt();
            return;
        }
        let roll = self.rng.next() % 100;
        let r = (if roll < 35 { 1 } else if roll < 75 { 2 } else { 3 }).min(cur);
        let mut removed: Vec<Point> = Vec::with_capacity(r);
        for _ in 0..r {
            let p = self.pairs[self.rng.below(self.pairs.len())];
            self.remove_pair(p);
            removed.push(p);
        }
        self.greedy_fill(&removed);
        self.greedy_fill(&[]);
        let newn = self.pairs.len();
        self.note_locopt();
        if newn < cur {
            self.g.reverts.fetch_add(1, Relaxed);
            for p in self.pairs.clone() {
                if !saved.contains(&p) {
                    self.remove_pair(p);
                }
            }
            for &p in &saved {
                if !self.pairs.contains(&p) {
                    self.add_pair(p);
                }
            }
            assert_eq!(self.pairs.len(), cur, "BUG: revert did not restore the state");
        } else if newn == cur {
            self.g.accept_lateral.fetch_add(1, Relaxed);
        } else {
            self.g.accept_improve.fetch_add(1, Relaxed);
        }
        self.iter_in_restart += 1;
        if self.iter_in_restart % 512 == 0 {
            // belt-and-braces: no rank-degenerate quadruple may ever survive
            assert_eq!(
                degenerate_quad_count(self.st.points()),
                0,
                "BUG: degenerate quadruple in live state"
            );
        }
    }

    fn flush_restart(&mut self) {
        self.g.restart_pairs_hist[self.restart_max_pairs.min(HIST_P - 1)]
            .fetch_add(1, Relaxed);
        self.g.restart_total_hist[self.restart_max_total.min(HIST_T - 1)]
            .fetch_add(1, Relaxed);
        self.g.restarts.fetch_add(1, Relaxed);
    }

    fn run(&mut self) {
        while !self.g.stop.load(Relaxed) {
            self.reset();
            self.greedy_fill(&[]);
            self.note_locopt();
            while self.since_improve < self.cfg.stall && !self.g.stop.load(Relaxed) {
                self.iterate();
                self.g.iters.fetch_add(1, Relaxed);
            }
            self.flush_restart();
        }
    }
}

// ------------------------------ status / main --------------------------------

fn hist_json(v: &[AtomicU64]) -> String {
    let mut s = String::from("[");
    for (i, a) in v.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&a.load(Relaxed).to_string());
    }
    s.push(']');
    s
}

fn write_status(g: &Global, secs_budget: f64, threads: usize, seed: u64, elapsed: f64, done: bool) {
    let iters = g.iters.load(Relaxed);
    let s = format!(
        "{{\n  \"angle\": \"central-inversion-symmetric\",\n  \"done\": {done},\n  \"found_target\": {},\n  \"target_points\": {},\n  \"sets34_distinct_pooled\": {},\n  \"elapsed_secs\": {elapsed:.1},\n  \"budget_secs\": {secs_budget},\n  \"threads\": {threads},\n  \"seed\": {seed},\n  \"iters\": {iters},\n  \"iters_per_sec\": {:.1},\n  \"restarts\": {},\n  \"accept_improve\": {},\n  \"accept_lateral\": {},\n  \"reverts\": {},\n  \"ext_runs\": {},\n  \"pair_adds\": {},\n  \"exact_checks\": {},\n  \"exact_rejects\": {},\n  \"best_pairs\": {},\n  \"best_sym_points\": {},\n  \"best_total_points\": {},\n  \"locopt_pairs_hist\": {},\n  \"restart_max_pairs_hist\": {},\n  \"restart_max_total_hist\": {},\n  \"thread_best_pairs\": {},\n  \"updated_unix\": {}\n}}\n",
        g.found34.load(Relaxed),
        g.target,
        g.sets34_pooled.load(Relaxed),
        iters as f64 / elapsed.max(1e-9),
        g.restarts.load(Relaxed),
        g.accept_improve.load(Relaxed),
        g.accept_lateral.load(Relaxed),
        g.reverts.load(Relaxed),
        g.ext_runs.load(Relaxed),
        g.pair_adds.load(Relaxed),
        g.exact_checks.load(Relaxed),
        g.exact_rejects.load(Relaxed),
        g.best_pairs_a.load(Relaxed),
        2 * g.best_pairs_a.load(Relaxed),
        g.best_total_a.load(Relaxed),
        hist_json(&g.locopt_hist),
        hist_json(&g.restart_pairs_hist),
        hist_json(&g.restart_total_hist),
        hist_json(&g.thread_best),
        unix_now(),
    );
    let tmp = g.out_dir.join("STATUS.json.tmp");
    if fs::write(&tmp, &s).is_ok() {
        let _ = fs::rename(&tmp, g.out_dir.join("STATUS.json"));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: symsearch <out_dir> [--secs S] [--threads T] [--seed X] [--stall N] [--extmin K] [--target P]";
    if args.len() < 2 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let out_dir = PathBuf::from(&args[1]);
    let mut secs = 3900.0f64;
    let mut threads = 8usize;
    let mut seed = 0x5EEDC0DE2026_u64;
    let mut stall = 600u64;
    let mut extmin = 14usize;
    let mut target = 35usize;
    let mut pool_pairs = 0usize; // 0 => derive from target below
    let mut pool_total = 0usize;
    let mut i = 2;
    while i + 1 < args.len() + 1 && i < args.len() {
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
            "--stall" => {
                stall = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--extmin" => {
                extmin = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--target" => {
                target = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--poolpairs" => {
                pool_pairs = args[i + 1].parse().unwrap();
                i += 2;
            }
            "--pooltotal" => {
                pool_total = args[i + 1].parse().unwrap();
                i += 2;
            }
            other => {
                eprintln!("unknown flag {other}\n{usage}");
                std::process::exit(2);
            }
        }
    }
    fs::create_dir_all(&out_dir).expect("cannot create out_dir");
    if pool_pairs == 0 {
        pool_pairs = (target / 2).saturating_sub(1).max(1);
    }
    if pool_total == 0 {
        pool_total = target.saturating_sub(2).max(1);
    }
    let g = Global::new(out_dir, threads, target);
    let cfg = Cfg { stall, extmin, pool_pairs, pool_total };
    let reps = orbit_reps();
    // odd N: center cell excluded; even N: sigma is fixed-point-free
    assert_eq!(reps.len(), if N % 2 == 1 { (NCELLS - 1) / 2 } else { NCELLS / 2 });
    println!(
        "symsearch: central-inversion symmetric ILS | n={N} reps={} threads={threads} secs={secs} seed={seed:#x} stall={stall} extmin={extmin} target={target} poolpairs={pool_pairs} pooltotal={pool_total}",
        reps.len()
    );
    let t0 = Instant::now();
    std::thread::scope(|sc| {
        for tid in 0..threads {
            let g = &g;
            let cfg = &cfg;
            let reps = &reps;
            let wseed = seed ^ (tid as u64).wrapping_mul(0x9E3779B97F4A7C15);
            sc.spawn(move || Worker::new(tid, wseed, reps, g, cfg).run());
        }
        // reporter (main thread)
        let mut last_status = Instant::now() - Duration::from_secs(60);
        let mut last_heartbeat = Instant::now();
        loop {
            std::thread::sleep(Duration::from_millis(2000));
            let elapsed = t0.elapsed().as_secs_f64();
            if elapsed >= secs {
                g.stop.store(true, Relaxed);
            }
            if last_status.elapsed().as_secs_f64() >= 10.0 {
                write_status(&g, secs, threads, seed, elapsed, false);
                last_status = Instant::now();
            }
            if last_heartbeat.elapsed().as_secs_f64() >= 60.0 {
                println!(
                    "heartbeat t={:.0}s iters={} restarts={} best_pairs={} best_total={}",
                    elapsed,
                    g.iters.load(Relaxed),
                    g.restarts.load(Relaxed),
                    g.best_pairs_a.load(Relaxed),
                    g.best_total_a.load(Relaxed)
                );
                last_heartbeat = Instant::now();
            }
            if g.stop.load(Relaxed) {
                break;
            }
        }
    });
    let elapsed = t0.elapsed().as_secs_f64();
    write_status(&g, secs, threads, seed, elapsed, true);
    let found = g.found34.load(Relaxed);
    println!(
        "SUMMARY found34={found} best_pairs={} best_total={} iters={} restarts={} elapsed={elapsed:.0}s",
        g.best_pairs_a.load(Relaxed),
        g.best_total_a.load(Relaxed),
        g.iters.load(Relaxed),
        g.restarts.load(Relaxed)
    );
    std::process::exit(if found { 3 } else { 0 });
}

// ------------------------------- tests ---------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mirror_shell_reps_sanity() {
        let reps = orbit_reps();
        assert_eq!(reps.len(), if N % 2 == 1 { (NCELLS - 1) / 2 } else { NCELLS / 2 });
        for &p in &reps {
            assert_eq!(mirror(mirror(p)), p);
            assert_ne!(mirror(p), p);
            assert_eq!(shell(p), shell(mirror(p)));
            assert!((1..NSHELL).contains(&shell(p)));
            assert!(cell_index(p) < cell_index(mirror(p)));
        }
    }

    /// Two orbit-pairs with EQUAL shells form a rectangle => rank-degenerate
    /// (cocircular) quadruple: the exact reason for the used_shell filter.
    #[test]
    fn equal_shell_pairs_are_degenerate() {
        if N != 13 {
            // fixture coordinates are n=13-specific; the property itself is
            // exercised for every N by mini_ils_run_is_exactly_valid
            return;
        }
        let p: Point = [6, 6, 0];
        let q: Point = [6, 0, 6]; // both shell 36 (scaled 144)
        assert_eq!(shell(p), shell(q));
        assert_eq!(cofactor_vec(&[p, mirror(p), q, mirror(q)]), [0i64; 5]);
        // different shells: plain parallelogram, NOT degenerate
        let r: Point = [5, 0, 6]; // shell 37
        assert_ne!(shell(p), shell(r));
        assert_ne!(cofactor_vec(&[p, mirror(p), r, mirror(r)]), [0i64; 5]);
    }

    /// Both-new-point degeneracies are caught by pair_conflict_exact:
    /// {a, b, p, sigma p} cocircular on a circle NOT centred at c
    /// (circle centre (5,8,6), r^2=10, in the central plane z=6).
    #[test]
    fn pair_conflict_catches_cocircular_quad() {
        if N != 13 {
            return; // n=13-specific fixture
        }
        let a: Point = [6, 11, 6];
        let b: Point = [4, 11, 6];
        let p: Point = [8, 7, 6];
        // fixture sanity: the quad really is rank-degenerate
        assert_eq!(cofactor_vec(&[a, b, p, mirror(p)]), [0i64; 5]);
        let s = vec![a, mirror(a), b, mirror(b)];
        assert!(pair_conflict_exact(&s, p));
    }

    /// 4-collinear through the centre (different shells!) is caught too.
    #[test]
    fn pair_conflict_catches_central_line() {
        if N != 13 {
            return; // n=13-specific fixture
        }
        let a: Point = [4, 6, 6]; // shell 4, on the x-axis line through c
        let p: Point = [0, 6, 6]; // shell 36, same central line
        assert_ne!(shell(a), shell(p));
        assert_eq!(cofactor_vec(&[a, mirror(a), p, mirror(p)]), [0i64; 5]);
        let s = vec![a, mirror(a)];
        assert!(pair_conflict_exact(&s, p));
    }

    /// End-to-end mini-run: greedy fill + 150 ILS iterations, with full
    /// brute-force cross-validation of the final state.
    #[test]
    fn mini_ils_run_is_exactly_valid() {
        let dir = std::env::temp_dir().join("no5_symsearch_test");
        let _ = fs::create_dir_all(&dir);
        let g = Global::new(dir, 1, 99);
        let cfg = Cfg { stall: 10_000, extmin: 12, pool_pairs: 99, pool_total: 99 };
        let reps = orbit_reps();
        let mut w = Worker::new(0, 0xABCDEF12345, &reps, &g, &cfg);
        w.reset();
        w.greedy_fill(&[]);
        w.note_locopt();
        assert!(w.pairs.len() >= 8, "greedy fill only reached {} pairs", w.pairs.len());
        for _ in 0..150 {
            w.iterate();
        }
        let pts = w.st.points().to_vec();
        assert_eq!(pts.len(), 2 * w.pairs.len());
        // symmetric, valid, degenerate-free — checked by independent brute force
        for &p in &pts {
            assert!(pts.contains(&mirror(p)));
        }
        assert!(w.st.is_valid_set());
        assert!(find_zero_5subset(&pts).is_none());
        assert_eq!(degenerate_quad_count(&pts), 0);
        // shells pairwise distinct
        let mut shells: Vec<usize> = w.pairs.iter().map(|&p| shell(p)).collect();
        shells.sort_unstable();
        shells.dedup();
        assert_eq!(shells.len(), w.pairs.len());
    }
}
