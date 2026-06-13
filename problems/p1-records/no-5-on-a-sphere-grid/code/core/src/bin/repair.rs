//! Pilot angle 1: exact blocker-cofactor repair search — r-out/(r+1)-in escape
//! moves (r <= 3) found as exact hitting-set queries over per-cell
//! blocking-quadruple bitsets (dossier "no-5-on-a-sphere-grid", attack angle 1).
//!
//! Theory. For a valid saturated set S in {0..12}^3, every unoccupied cell p
//! carries the exact blocker family B(p) = { Q in C(S,4) : det5(Q, p) == 0 }.
//! After deleting D from S, the surviving quadruples of S are exactly those
//! avoiding D, so p is addable to S \ D  iff  D intersects every member of
//! B(p) — i.e. D is a hitting set of B(p). An r-out/(r+1)-in escape is a
//! deletion set D (|D| = r) together with r+1 cells, each rescued by D
//! (hitting-set condition) and mutually compatible (no zero 5-subset among
//! (S \ D) plus any 2..5 of the new cells). Applying it gives a valid set of
//! size |S| + 1. All arithmetic is exact integer (det5 / cofactor engine of
//! the parent crate); every accepted move is re-verified from first principles
//! with find_zero_5subset before being trusted, and the driver re-checks
//! addability/validity against the incremental engine when applying.
//!
//! This binary is deliberately self-contained on top of the PUBLIC no5core
//! API: it does not modify lib.rs / main.rs (other campaign pilots extend the
//! same crate concurrently).
//!
//! Subcommands:
//!   repair escape <points.json> [--rmax R]
//!       exhaustive escape analysis of one saturated seed (no caps, no early
//!       exit): per-r candidate-deletion statistics + every escape found.
//!   repair run <outdir> [--secs S] [--threads T] [--rmax R] [--seed N]
//!              [--seed-file F]...
//!       multithreaded search campaign: randomized greedy to saturation,
//!       escape-move ascent, random kicks (ruin-and-recreate) with exact
//!       escape repair, restarts. Checkpoints STATUS.json + best sets to
//!       <outdir>; any 34-point set is saved immediately and loudly.

use no5core::*;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

// ----------------------------- rng ------------------------------------------

/// xorshift64* (same generator family as the crate's tests/bench).
pub struct Rng(u64);
impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    #[inline]
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    #[inline]
    pub fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0);
        (self.next() % n as u64) as usize
    }
    pub fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}

// ------------------------ blocker masks (exact) -----------------------------

/// Per-cell blocking-quadruple bitmasks over point indices (bit i = pts[i]).
/// out[cell] has one mask per quadruple Q of pts with det5(Q, cell) == 0.
/// Built with the production cofactor + SIMD zero-scan (exact integers);
/// `scratch` is only used for its scan kernel. Cells of members themselves
/// are included (trivial self-incidences) — callers skip occupied cells.
fn blocker_masks(pts: &[Point], scratch: &mut SearchState) -> Vec<Vec<u64>> {
    let m = pts.len();
    assert!(m <= 60, "blocker_masks requires |S| <= 60 (u64 index masks)");
    let mut out: Vec<Vec<u64>> = vec![Vec::new(); NCELLS];
    let mut zbuf: Vec<u16> = Vec::new();
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let q = [pts[a], pts[b], pts[c], pts[d]];
                    let mask = 1u64 << a | 1u64 << b | 1u64 << c | 1u64 << d;
                    zbuf.clear();
                    scratch.profile_scan(cofactor_vec(&q), &mut zbuf);
                    for &cell in &zbuf {
                        out[cell as usize].push(mask);
                    }
                }
            }
        }
    }
    out
}

// --------------------------- hitting sets -----------------------------------

/// Enumerate hitting sets of size <= rmax for `blockers` (each entry the
/// 4-member index mask of one blocking quadruple). Guarantees:
///   soundness   — every output mask hits all blockers;
///   completeness — every minimal hitting set of size <= rmax is output
///                  (so D of size <= rmax rescues the cell iff some output
///                   mask is a subset of D).
/// Some non-minimal hitting sets may also appear (harmless for subset
/// queries). Output is deduplicated.
pub fn hitting_sets(blockers: &[u64], rmax: u32, out: &mut Vec<u64>) {
    out.clear();
    rec_hs(blockers, 0, 0, rmax, out);
    out.sort_unstable();
    out.dedup();
}

fn rec_hs(blockers: &[u64], cur: u64, size: u32, rmax: u32, out: &mut Vec<u64>) {
    // branch on the first blocker not hit by `cur`: any (minimal) hitting set
    // extending `cur` must contain one of its 4 members.
    match blockers.iter().find(|&&b| b & cur == 0) {
        None => out.push(cur),
        Some(&b) => {
            if size == rmax {
                return;
            }
            let mut bb = b;
            while bb != 0 {
                let bit = bb & bb.wrapping_neg();
                rec_hs(blockers, cur | bit, size + 1, rmax, out);
                bb &= bb - 1;
            }
        }
    }
}

// ----------------------- escape move enumeration ----------------------------

#[derive(Clone)]
pub struct Limits {
    pub rmax: usize,
    /// search mode: rescued-cell sample cap per deletion set
    pub max_cells_per_d: usize,
    /// search mode: candidate deletion sets fully checked per r per round
    pub max_ds_checked: usize,
    /// clique-search node cap per deletion set
    pub max_clique_nodes: u64,
    /// analysis mode: no caps, no early exit, deterministic order
    pub exhaustive: bool,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            rmax: 3,
            max_cells_per_d: 32,
            max_ds_checked: 400,
            max_clique_nodes: 20_000,
            exhaustive: false,
        }
    }
}

#[derive(Default, Clone)]
pub struct EscapeStats {
    pub rounds: u64,
    pub rescuable_cells: u64,
    /// histogram of per-cell minimum hitting-set size (index 1..=4)
    pub min_hs_hist: [u64; 5],
    /// per r: deletion sets rescuing >= 1 cell
    pub ds_any_rescue: [u64; 5],
    /// per r: deletion sets rescuing >= r+1 cells (full candidates)
    pub cand_ds: [u64; 5],
    /// per r: max rescued cells seen for a single deletion set
    pub max_rescued: [u64; 5],
    pub compat_pairs: u64,
    pub joint_checks: u64,
    /// per r: escapes found (validated)
    pub escapes: [u64; 5],
    pub cap_hits: u64,
    pub violations: u64,
}

impl EscapeStats {
    fn absorb(&mut self, o: &EscapeStats) {
        self.rounds += o.rounds;
        self.rescuable_cells += o.rescuable_cells;
        for i in 0..5 {
            self.min_hs_hist[i] += o.min_hs_hist[i];
            self.ds_any_rescue[i] += o.ds_any_rescue[i];
            self.cand_ds[i] += o.cand_ds[i];
            self.max_rescued[i] = self.max_rescued[i].max(o.max_rescued[i]);
            self.escapes[i] += o.escapes[i];
        }
        self.compat_pairs += o.compat_pairs;
        self.joint_checks += o.joint_checks;
        self.cap_hits += o.cap_hits;
        self.violations += o.violations;
    }
}

pub struct EscapeMove {
    pub outs: Vec<Point>,
    pub ins: Vec<Point>,
    pub r: usize,
}

/// Exact pairwise compatibility of two rescued cells over base T: no zero
/// 5-subset of T u {p, q} containing both p and q (i.e. 3 of T + p + q).
fn pair_compatible(t: &[Point], p: Point, q: Point) -> bool {
    let n = t.len();
    for a in 0..n {
        for b in a + 1..n {
            for c in b + 1..n {
                if det5(&[t[a], t[b], t[c], p], q) == 0 {
                    return false;
                }
            }
        }
    }
    true
}

/// Higher-order joint check for a pairwise-compatible clique `ins` over T:
/// 5-subsets with exactly 3 new (3 ins + 2 of T), exactly 4 new (4 ins + 1 of
/// T) and — defensively, unreachable for r <= 4 — all-new. Exactly-1-new is
/// the hitting-set rescue condition; exactly-2-new is pairwise compatibility.
fn joint_valid(t: &[Point], ins: &[Point]) -> bool {
    let k = ins.len();
    for a in 0..k {
        for b in a + 1..k {
            for c in b + 1..k {
                for i in 0..t.len() {
                    for j in i + 1..t.len() {
                        if det5(&[t[i], t[j], ins[a], ins[b]], ins[c]) == 0 {
                            return false;
                        }
                    }
                }
            }
        }
    }
    for a in 0..k {
        for b in a + 1..k {
            for c in b + 1..k {
                for d in c + 1..k {
                    for &tp in t {
                        if det5(&[tp, ins[a], ins[b], ins[c]], ins[d]) == 0 {
                            return false;
                        }
                    }
                }
            }
        }
    }
    if k >= 5 && find_zero_5subset(ins).is_some() {
        return false;
    }
    true
}

/// Lazy-memoized clique finder over the rescued-cell compatibility graph.
struct CliqueFinder<'a> {
    t: &'a [Point],
    cpts: &'a [Point],
    memo: Vec<u8>, // 0 unknown, 1 compatible, 2 incompatible
    n: usize,
    nodes: u64,
    node_cap: u64,
    capped: bool,
}

impl CliqueFinder<'_> {
    fn compat(&mut self, i: usize, j: usize, stats: &mut EscapeStats) -> bool {
        let idx = i * self.n + j;
        if self.memo[idx] == 0 {
            stats.compat_pairs += 1;
            let v = if pair_compatible(self.t, self.cpts[i], self.cpts[j]) { 1 } else { 2 };
            self.memo[idx] = v;
            self.memo[j * self.n + i] = v;
        }
        self.memo[idx] == 1
    }

    /// Depth-first search for a k-clique whose joint_valid check also passes.
    fn rec(
        &mut self,
        order: &[usize],
        start: usize,
        chosen: &mut Vec<usize>,
        k: usize,
        stats: &mut EscapeStats,
    ) -> bool {
        if chosen.len() == k {
            stats.joint_checks += 1;
            let ins: Vec<Point> = chosen.iter().map(|&i| self.cpts[i]).collect();
            return joint_valid(self.t, &ins);
        }
        for oi in start..order.len() {
            if order.len() - oi < k - chosen.len() {
                break;
            }
            if self.nodes >= self.node_cap {
                self.capped = true;
                return false;
            }
            self.nodes += 1;
            let v = order[oi];
            let mut ok = true;
            for ci in 0..chosen.len() {
                let u = chosen[ci];
                if !self.compat(u, v, stats) {
                    ok = false;
                    break;
                }
            }
            if ok {
                chosen.push(v);
                if self.rec(order, oi + 1, chosen, k, stats) {
                    return true;
                }
                chosen.pop();
            }
        }
        false
    }
}

/// Find a joint-valid (r+1)-clique among rescued cells; returns its points.
fn find_clique(
    t: &[Point],
    cells: &[u16],
    k: usize,
    rng: &mut Rng,
    lim: &Limits,
    stats: &mut EscapeStats,
) -> Option<Vec<Point>> {
    let n = cells.len();
    if n < k {
        return None;
    }
    let cpts: Vec<Point> = cells.iter().map(|&c| cell_point(c as usize)).collect();
    let mut order: Vec<usize> = (0..n).collect();
    if !lim.exhaustive {
        rng.shuffle(&mut order);
    }
    let mut cf = CliqueFinder {
        t,
        cpts: &cpts,
        memo: vec![0u8; n * n],
        n,
        nodes: 0,
        node_cap: if lim.exhaustive { u64::MAX } else { lim.max_clique_nodes },
        capped: false,
    };
    let mut chosen = Vec::with_capacity(k);
    let found = cf.rec(&order, 0, &mut chosen, k, stats);
    if cf.capped {
        stats.cap_hits += 1;
    }
    if found {
        Some(chosen.iter().map(|&i| cpts[i]).collect())
    } else {
        None
    }
}

/// Enumerate r-out/(r+1)-in escapes of the valid (ideally saturated) set in
/// `st`, r = 1..=lim.rmax. Search mode (exhaustive=false): randomized order,
/// caps, return at first validated move. Analysis mode (exhaustive=true):
/// deterministic full enumeration; with collect_all also keeps ALL moves.
/// Every returned move has passed a from-first-principles find_zero_5subset
/// re-verification of the complete new set.
pub fn find_escapes(
    st: &SearchState,
    lim: &Limits,
    rng: &mut Rng,
    stats: &mut EscapeStats,
    collect_all: bool,
) -> Vec<EscapeMove> {
    stats.rounds += 1;
    let pts: Vec<Point> = st.points().to_vec();
    let m = pts.len();
    assert!(m <= 60);
    let mut scratch = SearchState::new();
    let blockers = blocker_masks(&pts, &mut scratch);

    // hitting-set map: hs mask -> cells rescued by any D containing that mask
    let mut map: HashMap<u64, Vec<u16>> = HashMap::new();
    let mut hsbuf: Vec<u64> = Vec::new();
    for cell in 0..NCELLS {
        if st.is_occupied(cell) || blockers[cell].is_empty() {
            continue; // occupied, or already addable (caller saturates first)
        }
        hitting_sets(&blockers[cell], lim.rmax as u32, &mut hsbuf);
        if !hsbuf.is_empty() {
            stats.rescuable_cells += 1;
            let minhs = hsbuf.iter().map(|h| h.count_ones()).min().unwrap() as usize;
            if minhs < 5 {
                stats.min_hs_hist[minhs] += 1;
            }
        }
        for &h in &hsbuf {
            map.entry(h).or_default().push(cell as u16);
        }
    }

    let mut moves: Vec<EscapeMove> = Vec::new();
    for r in 1..=lim.rmax {
        if m < r + 4 {
            break;
        }
        // candidate deletion sets: union of rescued cells over all submasks
        let mut cands: Vec<(u64, Vec<u16>)> = Vec::new();
        let limit = 1u64 << m;
        let mut dmask = (1u64 << r) - 1;
        while dmask < limit {
            let mut cells: Vec<u16> = Vec::new();
            let mut sub = dmask;
            loop {
                if let Some(v) = map.get(&sub) {
                    cells.extend_from_slice(v);
                }
                if sub == 0 {
                    break;
                }
                sub = (sub - 1) & dmask;
            }
            cells.sort_unstable();
            cells.dedup();
            if !cells.is_empty() {
                stats.ds_any_rescue[r] += 1;
                stats.max_rescued[r] = stats.max_rescued[r].max(cells.len() as u64);
                if cells.len() >= r + 1 {
                    cands.push((dmask, cells));
                }
            }
            // Gosper's hack: next mask with the same popcount
            let c = dmask & dmask.wrapping_neg();
            let rr = dmask + c;
            dmask = (((rr ^ dmask) >> 2) / c) | rr;
        }
        stats.cand_ds[r] += cands.len() as u64;
        if !lim.exhaustive {
            // randomize, then bring high-rescue deletion sets to the front:
            // they have the best odds of containing a compatible (r+1)-clique
            // (Codex review). r <= 2 is processed exhaustively (cheap).
            rng.shuffle(&mut cands);
            cands.sort_by_key(|(_, cells)| std::cmp::Reverse(cells.len().min(8)));
        }
        let cap = if lim.exhaustive || r <= 2 { usize::MAX } else { lim.max_ds_checked };
        let mut processed = 0usize;
        for (dmask, mut cells) in cands {
            if !lim.exhaustive {
                if processed >= cap {
                    stats.cap_hits += 1;
                    break;
                }
                processed += 1;
                if cells.len() > lim.max_cells_per_d {
                    rng.shuffle(&mut cells);
                    cells.truncate(lim.max_cells_per_d);
                }
            }
            let outs: Vec<Point> =
                (0..m).filter(|i| dmask >> i & 1 == 1).map(|i| pts[i]).collect();
            let t: Vec<Point> =
                (0..m).filter(|i| dmask >> i & 1 == 0).map(|i| pts[i]).collect();
            if let Some(ins) = find_clique(&t, &cells, r + 1, rng, lim, stats) {
                // ground truth: full exact certificate check of the new set
                let mut newpts = t.clone();
                newpts.extend_from_slice(&ins);
                if let Some(w) = find_zero_5subset(&newpts) {
                    stats.violations += 1;
                    eprintln!(
                        "SOUNDNESS VIOLATION (must never happen): escape r={r} \
                         outs={outs:?} ins={ins:?} has zero 5-subset {w:?}"
                    );
                    continue;
                }
                stats.escapes[r] += 1;
                moves.push(EscapeMove { outs, ins, r });
                if !collect_all {
                    return moves;
                }
            }
        }
    }
    moves
}

// --------------------------- search driver ----------------------------------

/// Add uniformly random addable cells until saturation. With `lookahead`,
/// from size 10 sample up to 6 candidates and keep the one leaving the most
/// addable cells (exact 1-step lookahead via the incremental engine).
pub fn greedy_fill(st: &mut SearchState, rng: &mut Rng, lookahead: bool) {
    loop {
        let addable = st.addable_cells();
        if addable.is_empty() {
            break;
        }
        let pick = if lookahead && st.len() >= 10 && addable.len() > 1 {
            let mut best_cell = addable[0];
            let mut best_v = -1i64;
            for _ in 0..6 {
                let cand = addable[rng.below(addable.len())];
                let p = cell_point(cand);
                st.add_point(p);
                let v = st.addable_cells().len() as i64;
                st.remove_point(p);
                if v > best_v {
                    best_v = v;
                    best_cell = cand;
                }
            }
            best_cell
        } else {
            addable[rng.below(addable.len())]
        };
        st.add_point(cell_point(pick));
    }
}

/// Apply an escape move, cross-validating each step against the incremental
/// engine. Returns false (state must then be rebuilt by caller) on any
/// inconsistency — counted as a violation; should never happen.
pub fn apply_move(st: &mut SearchState, mv: &EscapeMove) -> bool {
    for &p in &mv.outs {
        st.remove_point(p);
    }
    for &p in &mv.ins {
        if !st.is_addable_cell(cell_index(p)) {
            return false;
        }
        st.add_point(p);
    }
    st.is_valid_set()
}

/// Saturate, then alternate escape moves and greedy refills until no escape
/// (<= rmax) is found. Returns the number of escapes applied.
pub fn ascend(st: &mut SearchState, lim: &Limits, rng: &mut Rng, stats: &mut EscapeStats) -> u32 {
    greedy_fill(st, rng, false);
    let mut applied = 0u32;
    loop {
        let mvs = find_escapes(st, lim, rng, stats, false);
        let Some(mv) = mvs.into_iter().next() else {
            break;
        };
        let snap = st.points().to_vec();
        if !apply_move(st, &mv) {
            stats.violations += 1;
            eprintln!("APPLY VIOLATION (must never happen): rebuilding from snapshot");
            *st = SearchState::from_points(&snap);
            break;
        }
        applied += 1;
        greedy_fill(st, rng, false);
    }
    applied
}

/// Canonical hash of a point set under the 48 isometries of the cube
/// {0..12}^3 (axis permutations x per-axis reflections c -> 12 - c).
/// Used for dedup statistics only; certificates stay explicit point lists.
pub fn canon_hash(pts: &[Point]) -> u64 {
    const PERMS: [[usize; 3]; 6] =
        [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    let mut best = u64::MAX;
    let mut cells: Vec<u16> = Vec::with_capacity(pts.len());
    for perm in PERMS {
        for flips in 0..8u32 {
            cells.clear();
            for p in pts {
                let mut q = [0i32; 3];
                for (a, qa) in q.iter_mut().enumerate() {
                    let v = p[perm[a]];
                    *qa = if flips >> a & 1 == 1 { N - 1 - v } else { v };
                }
                cells.push(cell_index(q) as u16);
            }
            cells.sort_unstable();
            let mut h = 0xcbf29ce484222325u64; // FNV-1a
            for &c in &cells {
                h ^= c as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
            best = best.min(h);
        }
    }
    best
}

// ------------------------- shared campaign state -----------------------------

const MAXSZ: usize = 41;

struct Store {
    seen: HashSet<u64>,
    distinct: [u64; MAXSZ],
    saved: [u64; MAXSZ],
}

struct Shared {
    stop: AtomicBool,
    restarts: AtomicU64,
    seeded_restarts: AtomicU64,
    reached33: AtomicU64,
    /// restarts whose INITIAL greedy+ascent (before any kick) reached >= 33
    reached33_initial: AtomicU64,
    kicks: AtomicU64,
    best_size: AtomicU64,
    reached: Vec<AtomicU64>, // dead-end best-of-restart histogram (random restarts)
    stats: Mutex<EscapeStats>,
    store: Mutex<Store>,
}

impl Shared {
    fn new() -> Self {
        Shared {
            stop: AtomicBool::new(false),
            restarts: AtomicU64::new(0),
            seeded_restarts: AtomicU64::new(0),
            reached33: AtomicU64::new(0),
            reached33_initial: AtomicU64::new(0),
            kicks: AtomicU64::new(0),
            best_size: AtomicU64::new(0),
            reached: (0..MAXSZ).map(|_| AtomicU64::new(0)).collect(),
            stats: Mutex::new(EscapeStats::default()),
            store: Mutex::new(Store {
                seen: HashSet::new(),
                distinct: [0; MAXSZ],
                saved: [0; MAXSZ],
            }),
        }
    }
    fn flush(&self, s: &mut EscapeStats) {
        self.stats.lock().unwrap().absorb(s);
        *s = EscapeStats::default();
    }
}

fn points_json(pts: &[Point]) -> String {
    let body: Vec<String> =
        pts.iter().map(|p| format!("[{}, {}, {}]", p[0], p[1], p[2])).collect();
    format!("[{}]", body.join(", "))
}

/// Record a new local best. Dedups canonically; saves >= 32 to disk; a >= 34
/// set triggers the loud candidate path (after one more independent check).
fn report_best(pts: &[Point], shared: &Shared, outdir: &str) {
    let size = pts.len();
    if size < 31 {
        shared.best_size.fetch_max(size as u64, Relaxed);
        return;
    }
    let h = canon_hash(pts);
    let mut store = shared.store.lock().unwrap();
    shared.best_size.fetch_max(size as u64, Relaxed);
    if !store.seen.insert(h) {
        return;
    }
    let sz = size.min(MAXSZ - 1);
    store.distinct[sz] += 1;
    if size >= 32 && store.saved[sz] < 300 {
        store.saved[sz] += 1;
        let path = format!("{outdir}/best_{size}_{h:016x}.json");
        let _ = std::fs::write(&path, points_json(pts));
    }
    if size >= 34 {
        // independent re-verification before shouting
        if find_zero_5subset(pts).is_some() {
            eprintln!("CANDIDATE {size} FAILED re-verification — discarded (BUG)");
            return;
        }
        let path = format!("{outdir}/CANDIDATE34_{h:016x}.json");
        let _ = std::fs::write(&path, points_json(pts));
        println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        println!("!!! {size}-POINT VALID SET FOUND — saved to {path}");
        println!("!!! {}", points_json(pts));
        println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
    }
}

struct RunCfg {
    outdir: String,
    secs: f64,
    threads: usize,
    rmax: usize,
    rng_seed: u64,
    seed_sets: Vec<Vec<Point>>,
    base_kicks: u32,
    hi_kicks: u32,
    kick_min: usize,
    kick_max: usize,
}

fn worker(
    tid: usize,
    cfg: &RunCfg,
    shared: &Shared,
    seed_queue: &Mutex<Vec<Vec<Point>>>,
) {
    let mut rng = Rng::new(
        cfg.rng_seed ^ (tid as u64).wrapping_mul(0x9E3779B97F4A7C15) ^ 0x5DEECE66D,
    );
    let lim = Limits { rmax: cfg.rmax, ..Default::default() };
    let lookahead = tid % 2 == 1;
    // tiered kick budgets: 33+ basins get the big budget, 32 a medium one, so
    // 32-plateaus do not starve independent restarts (Codex review)
    let budget_for = |len: usize| -> u32 {
        if len >= 33 {
            cfg.hi_kicks
        } else if len >= 32 {
            (cfg.hi_kicks / 3).max(cfg.base_kicks)
        } else {
            cfg.base_kicks
        }
    };
    while !shared.stop.load(Relaxed) {
        // shared queue: every restart pops the next unused seed set (if any),
        // so ALL seed files get exploited regardless of thread count
        // (Codex review of the follow-on plan).
        let pending_seed: Option<Vec<Point>> = seed_queue.lock().unwrap().pop();
        let seeded = pending_seed.is_some();
        let mut st = match pending_seed {
            Some(p) => SearchState::from_points(&p),
            None => SearchState::new(),
        };
        let mut stats = EscapeStats::default();
        greedy_fill(&mut st, &mut rng, lookahead);
        ascend(&mut st, &lim, &mut rng, &mut stats);
        shared.flush(&mut stats);
        let mut best = st.points().to_vec();
        report_best(&best, shared, &cfg.outdir);
        if !seeded && best.len() >= 33 {
            shared.reached33_initial.fetch_add(1, Relaxed);
        }
        let mut budget = budget_for(best.len());
        while budget > 0 && !shared.stop.load(Relaxed) {
            shared.kicks.fetch_add(1, Relaxed);
            let k = cfg.kick_min + rng.below(cfg.kick_max - cfg.kick_min + 1);
            for _ in 0..k.min(st.len().saturating_sub(4)) {
                let p = st.points()[rng.below(st.len())];
                st.remove_point(p);
            }
            let mut stats = EscapeStats::default();
            greedy_fill(&mut st, &mut rng, lookahead);
            ascend(&mut st, &lim, &mut rng, &mut stats);
            shared.flush(&mut stats);
            if st.len() >= best.len() && st.len() >= 31 {
                // record equal-size sets too: diverse inequivalent seeds are a
                // pilot deliverable (canonical dedup happens inside)
                report_best(st.points(), shared, &cfg.outdir);
            }
            if st.len() > best.len() {
                best = st.points().to_vec();
                budget = budget_for(best.len());
            } else {
                if st.len() + 2 <= best.len() {
                    st = SearchState::from_points(&best);
                }
                budget -= 1;
            }
        }
        if seeded {
            shared.seeded_restarts.fetch_add(1, Relaxed);
        } else {
            shared.restarts.fetch_add(1, Relaxed);
            shared.reached[best.len().min(MAXSZ - 1)].fetch_add(1, Relaxed);
            if best.len() >= 33 {
                shared.reached33.fetch_add(1, Relaxed);
            }
        }
    }
}

fn write_status(cfg: &RunCfg, shared: &Shared, elapsed: f64) {
    let s = shared.stats.lock().unwrap().clone();
    let store = shared.store.lock().unwrap();
    let hist: Vec<String> = (0..MAXSZ)
        .filter(|&i| shared.reached[i].load(Relaxed) > 0)
        .map(|i| format!("\"{}\": {}", i, shared.reached[i].load(Relaxed)))
        .collect();
    let distinct: Vec<String> = (31..MAXSZ)
        .filter(|&i| store.distinct[i] > 0)
        .map(|i| format!("\"{}\": {}", i, store.distinct[i]))
        .collect();
    let epoch =
        SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
    let json = format!(
        "{{\n  \"elapsed_secs\": {:.1},\n  \"threads\": {},\n  \"rmax\": {},\n  \
         \"best_size\": {},\n  \"restarts\": {},\n  \"seeded_restarts\": {},\n  \
         \"reached33_restarts\": {},\n  \"reached33_initial\": {},\n  \"kicks\": {},\n  \"escape_rounds\": {},\n  \
         \"rescuable_cells_total\": {},\n  \"min_hs_hist\": [{}, {}, {}],\n  \
         \"ds_any_rescue\": [{}, {}, {}],\n  \"cand_ds\": [{}, {}, {}],\n  \
         \"escapes\": [{}, {}, {}],\n  \"max_rescued\": [{}, {}, {}],\n  \
         \"compat_pairs\": {},\n  \"joint_checks\": {},\n  \"cap_hits\": {},\n  \
         \"violations\": {},\n  \"dead_end_hist\": {{{}}},\n  \
         \"distinct_by_size\": {{{}}},\n  \"last_update_epoch\": {}\n}}\n",
        elapsed,
        cfg.threads,
        cfg.rmax,
        shared.best_size.load(Relaxed),
        shared.restarts.load(Relaxed),
        shared.seeded_restarts.load(Relaxed),
        shared.reached33.load(Relaxed),
        shared.reached33_initial.load(Relaxed),
        shared.kicks.load(Relaxed),
        s.rounds,
        s.rescuable_cells,
        s.min_hs_hist[1],
        s.min_hs_hist[2],
        s.min_hs_hist[3],
        s.ds_any_rescue[1],
        s.ds_any_rescue[2],
        s.ds_any_rescue[3],
        s.cand_ds[1],
        s.cand_ds[2],
        s.cand_ds[3],
        s.escapes[1],
        s.escapes[2],
        s.escapes[3],
        s.max_rescued[1],
        s.max_rescued[2],
        s.max_rescued[3],
        s.compat_pairs,
        s.joint_checks,
        s.cap_hits,
        s.violations,
        hist.join(", "),
        distinct.join(", "),
        epoch,
    );
    let _ = std::fs::write(format!("{}/STATUS.json", cfg.outdir), json);
}

fn cmd_run(cfg: RunCfg) -> i32 {
    std::fs::create_dir_all(&cfg.outdir).expect("cannot create outdir");
    let shared = Shared::new();
    println!(
        "repair run: threads={} rmax={} secs={} seeds={} outdir={}",
        cfg.threads,
        cfg.rmax,
        cfg.secs,
        cfg.seed_sets.len(),
        cfg.outdir
    );
    // reversed so queue.pop() hands out seeds in the given CLI order
    let seed_queue: Mutex<Vec<Vec<Point>>> =
        Mutex::new(cfg.seed_sets.iter().rev().cloned().collect());
    std::thread::scope(|sc| {
        for tid in 0..cfg.threads {
            let shared = &shared;
            let cfg = &cfg;
            let seed_queue = &seed_queue;
            sc.spawn(move || worker(tid, cfg, shared, seed_queue));
        }
        let t0 = Instant::now();
        loop {
            std::thread::sleep(Duration::from_secs(10));
            write_status(&cfg, &shared, t0.elapsed().as_secs_f64());
            if t0.elapsed().as_secs_f64() >= cfg.secs {
                break;
            }
        }
        shared.stop.store(true, Relaxed);
        // workers join at scope exit
    });
    write_status(&cfg, &shared, cfg.secs);
    let best = shared.best_size.load(Relaxed);
    println!(
        "DONE best_size={} restarts={} reached33={} (STATUS.json has full stats)",
        best,
        shared.restarts.load(Relaxed),
        shared.reached33.load(Relaxed)
    );
    if best >= 34 {
        println!("!!! CANDIDATE 34+ SET(S) IN {} — VERIFY AND CELEBRATE !!!", cfg.outdir);
    }
    0
}

// ----------------------------- escape CLI -----------------------------------

fn cmd_escape(path: &str, rmax: usize) -> i32 {
    let pts = load_points(path);
    let st = SearchState::from_points(&pts);
    let addable = st.addable_cells();
    println!(
        "m={} valid={} addable={} (exhaustive escape analysis, rmax={})",
        st.len(),
        st.is_valid_set(),
        addable.len(),
        rmax
    );
    if !st.is_valid_set() {
        eprintln!("input set is INVALID — aborting");
        return 2;
    }
    if !addable.is_empty() {
        println!("note: set NOT saturated; greedy-add first — already-addable cells are skipped here");
    }
    let lim = Limits { rmax, exhaustive: true, ..Default::default() };
    let mut rng = Rng::new(0xC0FFEE);
    let mut stats = EscapeStats::default();
    let t0 = Instant::now();
    let moves = find_escapes(&st, &lim, &mut rng, &mut stats, true);
    println!("elapsed_secs={:.1}", t0.elapsed().as_secs_f64());
    let hsh: Vec<String> = (1..=rmax).map(|i| stats.min_hs_hist[i].to_string()).collect();
    println!(
        "rescuable_cells={} min_hs_hist(r=1..={})=[{}]",
        stats.rescuable_cells,
        rmax,
        hsh.join(", ")
    );
    for r in 1..=rmax {
        println!(
            "r={}: ds_any_rescue={} cand_ds(>= r+1 rescued)={} max_rescued={} escapes={}",
            r, stats.ds_any_rescue[r], stats.cand_ds[r], stats.max_rescued[r], stats.escapes[r]
        );
    }
    println!(
        "compat_pairs={} joint_checks={} violations={}",
        stats.compat_pairs, stats.joint_checks, stats.violations
    );
    for mv in moves.iter().take(20) {
        println!("ESCAPE r={} outs={:?} ins={:?}", mv.r, mv.outs, mv.ins);
    }
    if let Some(mv) = moves.first() {
        let mut st2 = SearchState::from_points(&pts);
        if apply_move(&mut st2, mv) {
            let mut rng2 = Rng::new(1);
            greedy_fill(&mut st2, &mut rng2, false);
            let newpts = st2.points().to_vec();
            assert!(find_zero_5subset(&newpts).is_none());
            println!("RESULT_SIZE={}", newpts.len());
            println!("RESULT={}", points_json(&newpts));
            if newpts.len() >= 34 {
                let out = format!("{path}.escape34.json");
                let _ = std::fs::write(&out, points_json(&newpts));
                println!("!!! 34-POINT SET — saved to {out} !!!");
            }
        }
        0
    } else {
        println!("NO ESCAPE: set is r-out/(r+1)-in dead for all r <= {rmax}");
        1
    }
}

// ------------------------------- io / cli -----------------------------------

/// Minimal strict parser for plain JSON arrays of [x,y,z] integer triples
/// (same convention as the main CLI; rejects anything else).
fn parse_points(s: &str) -> Result<Vec<Point>, String> {
    let mut nums: Vec<i64> = Vec::new();
    let mut cur: Option<(i64, bool)> = None;
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
            _ => return Err(format!("unexpected character {ch:?}")),
        }
    }
    flush(&mut cur, &mut nums);
    if depth != 0 || maxdepth != 2 || nums.len() % 3 != 0 || nums.is_empty() {
        return Err("expected [[x,y,z],...]".into());
    }
    Ok(nums.chunks(3).map(|c| [c[0] as i32, c[1] as i32, c[2] as i32]).collect())
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: repair escape <points.json> [--rmax R(<=4)]\n       \
                 repair run <outdir> [--secs S] [--threads T] [--rmax R(<=3)] [--seed N] \
                 [--base-kicks K] [--hi-kicks K] [--kick-min K] [--kick-max K] [--seed-file F]...";
    if args.len() < 3 {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let code = match args[1].as_str() {
        "escape" => {
            let mut rmax = 3usize;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--rmax" => {
                        rmax = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    other => {
                        eprintln!("unknown flag {other}\n{usage}");
                        std::process::exit(2);
                    }
                }
            }
            assert!(
                (1..=4).contains(&rmax),
                "rmax must be 1..=4 in analysis mode (stats arrays sized for r<=4)"
            );
            cmd_escape(&args[2], rmax)
        }
        "run" => {
            let mut cfg = RunCfg {
                outdir: args[2].clone(),
                secs: 3600.0,
                threads: 8,
                rmax: 3,
                rng_seed: 0xB10C4E5C4FE5EED5,
                seed_sets: Vec::new(),
                base_kicks: 60,
                hi_kicks: 400,
                kick_min: 3,
                kick_max: 5,
            };
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--secs" => {
                        cfg.secs = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--threads" => {
                        cfg.threads = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--rmax" => {
                        cfg.rmax = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--seed" => {
                        cfg.rng_seed = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--base-kicks" => {
                        cfg.base_kicks = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--hi-kicks" => {
                        cfg.hi_kicks = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--seed-file" => {
                        cfg.seed_sets.push(load_points(&args[i + 1]));
                        i += 2;
                    }
                    "--kick-min" => {
                        cfg.kick_min = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    "--kick-max" => {
                        cfg.kick_max = args[i + 1].parse().unwrap();
                        i += 2;
                    }
                    other => {
                        eprintln!("unknown flag {other}\n{usage}");
                        std::process::exit(2);
                    }
                }
            }
            assert!((1..=3).contains(&cfg.rmax), "rmax must be 1..=3 in run mode");
            assert!(
                cfg.kick_min >= 1 && cfg.kick_min <= cfg.kick_max && cfg.kick_max <= 20,
                "need 1 <= kick_min <= kick_max <= 20"
            );
            cmd_run(cfg)
        }
        other => {
            eprintln!("unknown subcommand {other}\n{usage}");
            2
        }
    };
    std::process::exit(code);
}

// --------------------------------- tests ------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Published 33-point n=12 record (verbatim, fits {0..12}^3).
    fn s12_points() -> Vec<Point> {
        vec![
            [5, 9, 10], [10, 5, 8], [11, 11, 2], [0, 2, 10], [4, 9, 0], [3, 8, 9],
            [6, 10, 6], [3, 1, 11], [1, 4, 6], [8, 8, 2], [8, 7, 6], [0, 10, 0],
            [4, 2, 1], [1, 10, 7], [10, 11, 7], [4, 3, 7], [9, 0, 9], [10, 6, 0],
            [4, 3, 5], [7, 2, 0], [2, 0, 11], [0, 5, 1], [9, 9, 8], [0, 9, 2],
            [11, 1, 1], [9, 6, 10], [7, 1, 2], [1, 2, 5], [7, 3, 10], [11, 7, 11],
            [1, 11, 9], [8, 0, 11], [11, 0, 3],
        ]
    }

    /// hitting_sets: sound (every output hits all blockers) and complete
    /// (every subset of size <= 3 that hits all blockers contains an output).
    #[test]
    fn hitting_sets_sound_and_complete() {
        let mut rng = Rng::new(123);
        for _ in 0..150 {
            let nb = 3 + rng.below(8);
            let mut blockers = Vec::new();
            for _ in 0..nb {
                let mut mask = 0u64;
                while mask.count_ones() < 4 {
                    mask |= 1 << rng.below(12);
                }
                blockers.push(mask);
            }
            let mut hs = Vec::new();
            hitting_sets(&blockers, 3, &mut hs);
            for &h in &hs {
                assert!(h.count_ones() <= 3);
                assert!(blockers.iter().all(|&b| b & h != 0));
            }
            for d in 0u64..(1 << 12) {
                if d.count_ones() > 3 {
                    continue;
                }
                let hits = blockers.iter().all(|&b| b & d != 0);
                let covered = hs.iter().any(|&h| h & d == h);
                assert_eq!(hits, covered, "d={d:#b} blockers={blockers:?}");
            }
        }
    }

    /// The hitting-set rescue prediction must equal an independent engine
    /// recount: addable cells of S \ D (excluding D's own cells).
    #[test]
    fn rescue_prediction_matches_engine() {
        let pts = s12_points();
        let st = SearchState::from_points(&pts);
        assert!(st.is_valid_set());
        let mut scratch = SearchState::new();
        let blockers = blocker_masks(&pts, &mut scratch);
        let mut rng = Rng::new(99);
        let mut hsbuf = Vec::new();
        for trial in 0..8 {
            let r = 2 + trial % 2;
            let mut dmask = 0u64;
            while dmask.count_ones() < r {
                dmask |= 1 << rng.below(pts.len());
            }
            // (a) raw mask prediction
            let mut predicted: Vec<usize> = Vec::new();
            // (b) prediction via the hitting-set route used by find_escapes
            let mut via_hs: Vec<usize> = Vec::new();
            for cell in 0..NCELLS {
                if st.is_occupied(cell) || blockers[cell].is_empty() {
                    continue;
                }
                if blockers[cell].iter().all(|&b| b & dmask != 0) {
                    predicted.push(cell);
                }
                hitting_sets(&blockers[cell], 3, &mut hsbuf);
                if hsbuf.iter().any(|&h| h & dmask == h) {
                    via_hs.push(cell);
                }
            }
            // (c) ground truth: rebuild S \ D and ask the engine
            let tpts: Vec<Point> = pts
                .iter()
                .enumerate()
                .filter(|(i, _)| dmask >> i & 1 == 0)
                .map(|(_, &p)| p)
                .collect();
            let dcells: Vec<usize> = pts
                .iter()
                .enumerate()
                .filter(|(i, _)| dmask >> i & 1 == 1)
                .map(|(_, &p)| cell_index(p))
                .collect();
            let st2 = SearchState::from_points(&tpts);
            let engine: Vec<usize> = st2
                .addable_cells()
                .into_iter()
                .filter(|c| !dcells.contains(c))
                .collect();
            assert_eq!(predicted, engine, "dmask={dmask:#x}");
            assert_eq!(via_hs, engine, "dmask={dmask:#x}");
        }
    }

    /// canon_hash is invariant under all 48 cube isometries.
    #[test]
    fn canon_hash_invariant() {
        let pts = s12_points();
        let h0 = canon_hash(&pts);
        // reflection x -> 12 - x
        let refl: Vec<Point> = pts.iter().map(|p| [12 - p[0], p[1], p[2]]).collect();
        assert_eq!(canon_hash(&refl), h0);
        // permutation (x,y,z) -> (z,x,y)
        let perm: Vec<Point> = pts.iter().map(|p| [p[2], p[0], p[1]]).collect();
        assert_eq!(canon_hash(&perm), h0);
        // distinct set should (overwhelmingly) hash differently
        let other: Vec<Point> = pts.iter().map(|p| [p[0], p[1], (p[2] + 1) % 13]).collect();
        assert_ne!(canon_hash(&other), h0);
    }

    /// End-to-end smoke: greedy + escape ascent yields a valid saturated set,
    /// with zero soundness violations and (typically) some applied escapes.
    #[test]
    fn ascend_smoke() {
        let mut rng = Rng::new(0xABCD);
        let mut st = SearchState::new();
        let lim = Limits { rmax: 2, max_ds_checked: 60, ..Default::default() };
        let mut stats = EscapeStats::default();
        greedy_fill(&mut st, &mut rng, false);
        let before = st.len();
        assert!(st.is_valid_set());
        assert!(st.addable_cells().is_empty());
        ascend(&mut st, &lim, &mut rng, &mut stats);
        assert!(st.is_valid_set());
        assert!(st.addable_cells().is_empty());
        assert!(st.len() >= before);
        assert_eq!(stats.violations, 0);
        assert!(find_zero_5subset(st.points()).is_none());
    }
}
