//! F_13 cap assault — attack angle 2 ("finite-field cap assault over F_13").
//!
//! The grid {0..12}^3 is a transversal of F_13^3. If EVERY 5-subset of a set S
//! has lifted 5x5 determinant nonzero **mod 13**, then a fortiori all integer
//! determinants are nonzero, so S is a valid integer certificate. Such an S is
//! exactly an *arc* in PG(4,13) contained in the affine part of the parabolic
//! quadric X0^2+X1^2+X2^2 = X3*X4 (the image of the lift).
//!
//! THEORY CEILING (Ball 2012, MDS conjecture for prime q): every arc in
//! PG(4,13) has at most q+1 = 14 points. Therefore a 34-point mod-13 cap is
//! PROVABLY IMPOSSIBLE; the angle's value is (a) mining *maximum* arcs
//! (size <= 14) whose internal 5-subsets are maximally robust (nonzero in the
//! strongest possible sense), and (b) using their similarity-group orbit
//! (translations + scalings + signed permutations mod 13, order 13^3*12*48)
//! as a structured seed generator for the exact integer ILS.
//!
//! Empirical calibration (computed 2026-06-11, exact arithmetic): the published
//! 33-point record has 18,499/237,336 5-subset dets == 0 mod 13 (random rate
//! 1/13) and 1,337 == 0 mod 169 (random rate 1/169) — record-grade sets are
//! nowhere near the mod-13 subspace, so this module treats arcs strictly as
//! seed material, never as the search space for 34.
//!
//! All validity decisions are exact integer arithmetic (i64 dets reduced
//! mod 13, plus the existing exact integer SearchState). NO floats anywhere
//! in validity logic.
//!
//! Explicit algebraic seed: the curve t -> (t^3 + t, 5*t^3, t^2) mod 13.
//! Its lift spans {1, t, t^2, t^3, t^4}: the t^6 term of x^2+y^2+z^2 dies
//! because 1 + 5^2 = 26 == 0 (mod 13), the t^5 term is absent, and the t^4
//! coefficient is 2+1 = 3 != 0. Hence every 5 distinct-parameter points are
//! independent mod 13 (basis change x Vandermonde): a guaranteed 13-arc.

use crate::ils::canonical_form;
use crate::{cell_index, cell_point, cofactor_vec, det5, find_zero_5subset, Point, SearchState, N, NCELLS};
use std::collections::{HashMap, HashSet};
use std::io::Write as IoWrite;
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const P: i64 = 13;
const MAX_SIZE_STAT: usize = 40;

// --- private copies of two tiny helpers (ils.rs is owned by a sibling
// campaign; we deliberately do not widen its private API) ---

const NKEYS: usize = 12;

/// The 12 sorting keys of the evolved recipe (verbatim from ils.rs).
fn key_tuple(k: usize, p: Point) -> [i64; 5] {
    let (x, y, z) = (p[0] as i64, p[1] as i64, p[2] as i64);
    let r2 = x * x + y * y + z * z;
    let s = x + y + z;
    let mx = x.max(y).max(z);
    let n1 = (N - 1) as i64;
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
        7 => [s % 2, x, y, z, 0],
        8 => [cdist, x, y, z, 0],
        9 => [-cdist, x, y, z, 0],
        10 => [-zeros, x, y, z, 0],
        11 => [-highs, x, y, z, 0],
        _ => unreachable!(),
    }
}

fn sorted_orders() -> Vec<Vec<u16>> {
    (0..NKEYS)
        .map(|k| {
            let mut v: Vec<u16> = (0..NCELLS as u16).collect();
            v.sort_by_key(|&ci| key_tuple(k, cell_point(ci as usize)));
            v
        })
        .collect()
}

fn points_json(pts: &[Point]) -> String {
    let body: Vec<String> =
        pts.iter().map(|p| format!("[{},{},{}]", p[0], p[1], p[2])).collect();
    format!("[{}]", body.join(","))
}

// ----------------------------- RNG (xorshift64*) ----------------------------

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
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
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn randint(&mut self, a: usize, b: usize) -> usize {
        a + self.below(b - a + 1)
    }
    /// branch probabilities only — never validity
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    fn shuffle16(&mut self, v: &mut [u16]) {
        for i in (1..v.len()).rev() {
            v.swap(i, self.below(i + 1));
        }
    }
}

// --------------------------- mod-13 primitives ------------------------------

/// det5 reduced to the canonical residue 0..12.
#[inline]
pub fn det5_mod13(q: &[Point; 4], p: Point) -> i64 {
    det5(q, p).rem_euclid(P)
}

/// Cofactor vector reduced mod 13 (each component in 0..12).
#[inline]
fn cof13(q: &[Point; 4]) -> [i32; 5] {
    cofactor_vec(q).map(|v| v.rem_euclid(P) as i32)
}

/// Brute-force: first 5-subset with det == 0 mod 13, if any.
pub fn find_zero_5subset_mod13(points: &[Point]) -> Option<[Point; 5]> {
    let m = points.len();
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let q = [points[a], points[b], points[c], points[d]];
                    for e in d + 1..m {
                        if det5_mod13(&q, points[e]) == 0 {
                            return Some([points[a], points[b], points[c], points[d], points[e]]);
                        }
                    }
                }
            }
        }
    }
    None
}

/// The guaranteed algebraic 13-arc t -> (t^3 + t, 5 t^3, t^2) mod 13.
pub fn algebraic_seed() -> Vec<Point> {
    (0..13i64)
        .map(|t| {
            let x = (t * t * t + t).rem_euclid(P) as i32;
            let y = (5 * t * t * t).rem_euclid(P) as i32;
            let z = (t * t).rem_euclid(P) as i32;
            [x, y, z]
        })
        .collect()
}

// --------------------------- similarity group --------------------------------

const PERMS: [[usize; 3]; 6] = [
    [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0],
];

/// Apply the similarity p -> r * M(p) + t (mod 13), where M is the signed
/// permutation given by (perm, flips) with flip meaning c -> -c mod 13.
/// Similarities preserve mod-13 sphere/plane incidence, so arc images are arcs.
fn apply_sim(p: Point, perm: [usize; 3], flips: u32, r: i64, t: [i64; 3]) -> Point {
    let mut q = [0i32; 3];
    for a in 0..3 {
        let mut c = p[perm[a]] as i64;
        if flips >> a & 1 == 1 {
            c = -c;
        }
        q[a] = (r * c + t[a]).rem_euclid(P) as i32;
    }
    q
}

/// Canonical form of a set under the full affine similarity subgroup
/// {p -> r*M(p) + t}: because the lex-min sorted cell vector necessarily maps
/// some member to (0,0,0), it suffices to minimize over (r, M, anchor point):
/// 12 * 48 * |S| images instead of 13^3 * 12 * 48.
pub fn canonical13(pts: &[Point]) -> Vec<u16> {
    let mut best: Option<Vec<u16>> = None;
    let mut img: Vec<u16> = vec![0; pts.len()];
    for perm in PERMS {
        for flips in 0..8u32 {
            for r in 1..P {
                for anchor in pts {
                    // translation that sends `anchor` to the origin
                    let a = apply_sim(*anchor, perm, flips, r, [0, 0, 0]);
                    let t = [-(a[0] as i64), -(a[1] as i64), -(a[2] as i64)];
                    for (slot, p) in img.iter_mut().zip(pts.iter()) {
                        *slot = cell_index(apply_sim(*p, perm, flips, r, t)) as u16;
                    }
                    img.sort_unstable();
                    if best.as_ref().is_none_or(|b| img < *b) {
                        best = Some(img.clone());
                    }
                }
            }
        }
    }
    best.unwrap()
}

// --------------------------- incremental arc state ---------------------------

struct QuadF13 {
    members: [u16; 4],
    cells: Vec<u16>,
}

/// Incremental blocked-cell state for the mod-13 arc condition, mirroring
/// `SearchState` exactly but with all zero-tests taken mod 13. Sets here are
/// tiny (<= 14 by Ball's theorem), so the scan is plain scalar code.
pub struct F13State {
    points: Vec<Point>,
    occupied: Vec<bool>,
    blocked: Vec<u32>,
    quads: Vec<QuadF13>,
}

impl F13State {
    pub fn new() -> Self {
        F13State {
            points: Vec::new(),
            occupied: vec![false; NCELLS],
            blocked: vec![0u32; NCELLS],
            quads: Vec::new(),
        }
    }

    pub fn from_points(pts: &[Point]) -> Self {
        let mut s = Self::new();
        for &p in pts {
            s.add_point(p);
        }
        s
    }

    pub fn points(&self) -> &[Point] {
        &self.points
    }

    pub fn len(&self) -> usize {
        self.points.len()
    }

    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    pub fn blocked_count(&self, cell: usize) -> u32 {
        self.blocked[cell]
    }

    pub fn is_addable_cell(&self, cell: usize) -> bool {
        !self.occupied[cell] && self.blocked[cell] == 0
    }

    /// Same member invariant as SearchState::is_valid_set, mod 13: valid arc
    /// iff every member carries exactly the C(s-1,3) trivial self-incidences.
    pub fn is_valid_arc(&self) -> bool {
        let s = self.points.len() as u64;
        let trivial = if s >= 4 { (s - 1) * (s - 2) * (s - 3) / 6 } else { 0 };
        self.points
            .iter()
            .all(|&p| self.blocked[cell_index(p)] as u64 == trivial)
    }

    /// Cells with dot(c, lift(cell)) == 0 (mod 13). A zero cofactor vector
    /// (rank-degenerate mod 13) blocks ALL cells — same trap as over Z, and
    /// it triggers MORE often mod 13 (integer rank 4 can collapse mod 13).
    fn scan_zero_cells(c: [i32; 5], out: &mut Vec<u16>) {
        let mut gx = [0i32; N as usize];
        let mut ty = [0i32; N as usize];
        let mut tz = [0i32; N as usize];
        for v in 0..N {
            let vi = v as i64;
            gx[v as usize] = ((c[0] as i64 * vi + c[3] as i64 * vi * vi + c[4] as i64) % P) as i32;
            ty[v as usize] = ((c[1] as i64 * vi + c[3] as i64 * vi * vi) % P) as i32;
            tz[v as usize] = ((c[2] as i64 * vi + c[3] as i64 * vi * vi) % P) as i32;
        }
        let mut idx = 0u16;
        for x in 0..N as usize {
            for y in 0..N as usize {
                let base = gx[x] + ty[y]; // 0..24
                for z in 0..N as usize {
                    if (base + tz[z]) % 13 == 0 {
                        out.push(idx);
                    }
                    idx += 1;
                }
            }
        }
    }

    pub fn add_point(&mut self, p: Point) {
        assert!(crate::in_grid(p), "point {:?} outside {{0..12}}^3", p);
        let pc = cell_index(p);
        assert!(!self.occupied[pc], "cell {:?} already occupied", p);
        let s = self.points.len();
        for i in 0..s {
            for j in i + 1..s {
                for k in j + 1..s {
                    let q = [self.points[i], self.points[j], self.points[k], p];
                    let c = cof13(&q);
                    let mut cells = Vec::new();
                    Self::scan_zero_cells(c, &mut cells);
                    for &ci in &cells {
                        self.blocked[ci as usize] += 1;
                    }
                    self.quads.push(QuadF13 {
                        members: [
                            cell_index(self.points[i]) as u16,
                            cell_index(self.points[j]) as u16,
                            cell_index(self.points[k]) as u16,
                            pc as u16,
                        ],
                        cells,
                    });
                }
            }
        }
        self.points.push(p);
        self.occupied[pc] = true;
    }

    pub fn remove_point(&mut self, p: Point) {
        let pc = cell_index(p) as u16;
        assert!(self.occupied[pc as usize], "point {:?} not in set", p);
        let mut i = 0;
        while i < self.quads.len() {
            let m = &self.quads[i].members;
            if m[0] == pc || m[1] == pc || m[2] == pc || m[3] == pc {
                let q = self.quads.swap_remove(i);
                for &ci in &q.cells {
                    self.blocked[ci as usize] -= 1;
                }
            } else {
                i += 1;
            }
        }
        let idx = self.points.iter().position(|&q| q == p).unwrap();
        self.points.swap_remove(idx);
        self.occupied[pc as usize] = false;
    }
}

impl Default for F13State {
    fn default() -> Self {
        Self::new()
    }
}

/// Brute-force mod-13 blocked grid (independent of the cofactor path).
pub fn blocked_bruteforce_mod13(points: &[Point]) -> Vec<u32> {
    let mut blocked = vec![0u32; NCELLS];
    let m = points.len();
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let q = [points[a], points[b], points[c], points[d]];
                    for (cell, slot) in blocked.iter_mut().enumerate() {
                        if det5_mod13(&q, cell_point(cell)) == 0 {
                            *slot += 1;
                        }
                    }
                }
            }
        }
    }
    blocked
}

// ------------------------------ arc miner -------------------------------------

pub struct ArcsConfig {
    pub secs: f64,
    pub threads: usize,
    pub seed: u64,
    pub out_dir: String,
}

struct ArcShared {
    max_size: usize,
    hist: Vec<u64>, // maximal-arc size histogram (after plateau)
    restarts: u64,
    /// raw dedup of stored arcs (sorted cell vectors)
    seen: HashSet<Vec<u16>>,
    /// stored arcs per size (size >= POOL_MIN)
    pool: HashMap<usize, Vec<Vec<Point>>>,
    workers_done: usize,
}

const POOL_MIN: usize = 12;
const POOL_CAP_PER_SIZE: usize = 3000;
const PLATEAU_STEPS: usize = 240;

fn greedy_pass_f13(st: &mut F13State, order: &[u16]) {
    for &ci in order {
        if st.is_addable_cell(ci as usize) {
            st.add_point(cell_point(ci as usize));
        }
    }
}

fn restore_f13(st: &mut F13State, target: &[Point]) {
    let cur: Vec<Point> = st.points().to_vec();
    for p in cur {
        if !target.contains(&p) {
            st.remove_point(p);
        }
    }
    for &p in target {
        if !st.occupied[cell_index(p)] {
            st.add_point(p);
        }
    }
}

fn push_arc(shared: &Mutex<ArcShared>, pts: &[Point]) {
    let size = pts.len();
    // Ball's theorem (MDS conjecture, q=13 prime): arcs in PG(4,13) have at
    // most 14 points. Anything larger is an engine bug, not a discovery.
    assert!(size <= 14, "arc of size {size} contradicts Ball's theorem — engine bug");
    let mut sh = shared.lock().unwrap();
    sh.hist[size.min(MAX_SIZE_STAT - 1)] += 1;
    if size > sh.max_size {
        sh.max_size = size;
    }
    if size < POOL_MIN {
        return;
    }
    let mut key: Vec<u16> = pts.iter().map(|&p| cell_index(p) as u16).collect();
    key.sort_unstable();
    if !sh.seen.insert(key) {
        return;
    }
    let v = sh.pool.entry(size).or_default();
    if v.len() < POOL_CAP_PER_SIZE {
        // exact double-check before anything is stored: mod-13 validity AND
        // (implied, but never trusted) integer validity.
        assert!(find_zero_5subset_mod13(pts).is_none(), "stored arc invalid mod 13");
        assert!(find_zero_5subset(pts).is_none(), "mod-13 arc invalid over Z — impossible");
        v.push(pts.to_vec());
    }
}

fn arc_worker(tid: usize, cfg: &ArcsConfig, shared: &Mutex<ArcShared>, deadline: Instant) {
    let mut rng = Rng::new(cfg.seed ^ ((tid as u64 + 1) << 40));
    let curve = algebraic_seed();
    let mut order: Vec<u16> = (0..NCELLS as u16).collect();
    while Instant::now() < deadline {
        let mut st = F13State::new();
        // 15% of restarts: start from a random similarity image of the
        // algebraic 13-arc and let the plateau explore its neighborhood.
        if rng.unit() < 0.15 {
            let perm = PERMS[rng.below(6)];
            let flips = rng.below(8) as u32;
            let r = 1 + rng.below(12) as i64;
            let t = [rng.below(13) as i64, rng.below(13) as i64, rng.below(13) as i64];
            let img: Vec<Point> = curve.iter().map(|&p| apply_sim(p, perm, flips, r, t)).collect();
            for &p in &img {
                st.add_point(p);
            }
            assert!(st.is_valid_arc(), "similarity image of the curve arc not an arc — bug");
        }
        rng.shuffle16(&mut order);
        greedy_pass_f13(&mut st, &order);
        let mut best: Vec<Point> = st.points().to_vec();
        // plateau: remove 1-2 random points, greedy re-fill in a fresh order
        for _ in 0..PLATEAU_STEPS {
            let m = st.len();
            if m < 2 {
                break;
            }
            let r = 1 + (rng.unit() < 0.3) as usize;
            for _ in 0..r {
                let v = st.points()[rng.below(st.len())];
                st.remove_point(v);
            }
            rng.shuffle16(&mut order);
            greedy_pass_f13(&mut st, &order);
            if st.len() >= best.len() {
                best = st.points().to_vec();
                push_arc(shared, &best);
            } else {
                restore_f13(&mut st, &best);
            }
        }
        push_arc(shared, &best);
        let mut sh = shared.lock().unwrap();
        sh.restarts += 1;
    }
    let mut sh = shared.lock().unwrap();
    sh.workers_done += 1;
}

fn unix_now() -> f64 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs_f64()
}

pub fn run_arcs(cfg: &ArcsConfig) -> i32 {
    std::fs::create_dir_all(&cfg.out_dir).expect("cannot create out dir");
    let shared = Mutex::new(ArcShared {
        max_size: 0,
        hist: vec![0; MAX_SIZE_STAT],
        restarts: 0,
        seen: HashSet::new(),
        pool: HashMap::new(),
        workers_done: 0,
    });
    // the guaranteed algebraic arc is always in the pool
    push_arc(&shared, &algebraic_seed());
    let t0 = Instant::now();
    let deadline = t0 + Duration::from_secs_f64(cfg.secs);
    let status_path = format!("{}/STATUS_arcs.json", cfg.out_dir);
    println!("f13arcs: threads={} secs={} out={}", cfg.threads, cfg.secs, cfg.out_dir);

    std::thread::scope(|sc| {
        for tid in 0..cfg.threads {
            let shared = &shared;
            sc.spawn(move || arc_worker(tid, cfg, shared, deadline));
        }
        loop {
            let done = {
                let sh = shared.lock().unwrap();
                let hist: Vec<String> = (0..MAX_SIZE_STAT)
                    .filter(|&i| sh.hist[i] > 0)
                    .map(|i| format!("\"{}\":{}", i, sh.hist[i]))
                    .collect();
                let pool: Vec<String> = {
                    let mut ks: Vec<_> = sh.pool.iter().map(|(k, v)| (*k, v.len())).collect();
                    ks.sort();
                    ks.iter().map(|(k, c)| format!("\"{k}\":{c}")).collect()
                };
                let status = format!(
                    "{{\"unix\":{:.0},\"elapsed_secs\":{:.1},\"budget_secs\":{},\"threads\":{},\"max_size\":{},\"restarts\":{},\"hist\":{{{}}},\"pool\":{{{}}},\"done\":{}}}",
                    unix_now(),
                    t0.elapsed().as_secs_f64(),
                    cfg.secs,
                    cfg.threads,
                    sh.max_size,
                    sh.restarts,
                    hist.join(","),
                    pool.join(","),
                    sh.workers_done == cfg.threads
                );
                let _ = std::fs::write(&status_path, &status);
                sh.workers_done == cfg.threads
            };
            if done {
                break;
            }
            std::thread::sleep(Duration::from_secs(10));
        }
    });

    // harvest: save arcs.json (top sizes), canonical-class counts for max size
    let sh = shared.lock().unwrap();
    let mut sizes: Vec<usize> = sh.pool.keys().copied().collect();
    sizes.sort_unstable_by(|a, b| b.cmp(a));
    let mut arcs_out: Vec<String> = Vec::new();
    for &s in &sizes {
        for arc in &sh.pool[&s] {
            arcs_out.push(points_json(arc));
        }
    }
    let arcs_path = format!("{}/arcs.json", cfg.out_dir);
    std::fs::write(&arcs_path, format!("[{}]", arcs_out.join(",\n"))).expect("write arcs.json");
    // canonical classes at max size (cap the work)
    let mut classes: HashSet<Vec<u16>> = HashSet::new();
    if let Some(top) = sh.pool.get(&sh.max_size) {
        for arc in top.iter().take(500) {
            classes.insert(canonical13(arc));
        }
    }
    println!(
        "f13arcs done: max_size={} restarts={} pool_sizes={:?} canonical_classes_at_max(first500)={} arcs_saved={} -> {}",
        sh.max_size,
        sh.restarts,
        sizes.iter().map(|&s| (s, sh.pool[&s].len())).collect::<Vec<_>>(),
        classes.len(),
        arcs_out.len(),
        arcs_path
    );
    0
}

// --------------------------- seeded ILS comparison ----------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SeedArm {
    Control,
    Free,
    Protected,
}
impl SeedArm {
    fn name(self) -> &'static str {
        match self {
            SeedArm::Control => "control",
            SeedArm::Free => "free",
            SeedArm::Protected => "protected",
        }
    }
    fn idx(self) -> usize {
        match self {
            SeedArm::Control => 0,
            SeedArm::Free => 1,
            SeedArm::Protected => 2,
        }
    }
}

#[derive(Default, Clone)]
struct SeedArmStats {
    iters: u64,
    restarts: u64,
    build_hist: Vec<u64>, // size after a restart build (scratch or seeded)
    ils_trials: u64,
    accepts_improve: u64,
    accepts_equal: u64,
    rejects: u64,
    at33_trials: u64,
    at33_drop: u64,
    at33_same: u64,
    at33_move: u64,
    at33_up: u64,
    core_shrinks: u64,
    subarc_restarts: u64,
    distinct_finds: Vec<u64>, // new canonical classes for this arm's PRIVATE dedup, per size
}

struct FoundSetS {
    ts: f64,
    worker: usize,
    arm: SeedArm,
    size: usize,
    points: Vec<Point>,
}

struct SeedShared {
    best_size: usize,
    seen: HashMap<Vec<u16>, usize>,
    /// private per-arm dedup sets: unbiased per-arm discovery counting
    /// (the global map alone would credit only the first-finding arm)
    seen_arm: [HashSet<Vec<u16>>; 3],
    seen_overflow: u64,
    pending_log: Vec<FoundSetS>,
    logged_per_size: Vec<u64>,
    events: Vec<String>,
    stats: [SeedArmStats; 3],
    candidate34: Option<Vec<Point>>,
    workers_done: usize,
}

const DEDUP_CAP: usize = 500_000;
const LOG_CAP_32: usize = 2_000;
const LOG_CAP_33PLUS: usize = 10_000;

pub struct SeedConfig {
    pub secs: f64,
    pub control: usize,
    pub free: usize,
    pub protected: usize,
    pub seed: u64,
    pub stall: u64,
    pub arcs_path: String,
    pub out_dir: String,
}

/// Parse a depth-3 JSON array [[[x,y,z],...],...] of arcs (same minimal style
/// as the CLI's plain parser).
pub fn parse_arc_pool(s: &str) -> Result<Vec<Vec<Point>>, String> {
    let mut pool: Vec<Vec<Point>> = Vec::new();
    let mut arc: Vec<Point> = Vec::new();
    let mut triple: Vec<i64> = Vec::new();
    let mut cur: Option<i64> = None;
    let mut depth = 0i32;
    for ch in s.chars() {
        match ch {
            '[' => {
                depth += 1;
                if depth > 3 {
                    return Err("nesting deeper than 3".into());
                }
            }
            ']' => {
                if let Some(v) = cur.take() {
                    triple.push(v);
                }
                if depth == 3 {
                    if triple.len() != 3 {
                        return Err("triple of wrong length".into());
                    }
                    if !triple.iter().all(|&v| (0..13).contains(&v)) {
                        return Err(format!("coordinate out of range in {triple:?}"));
                    }
                    let p = [triple[0] as i32, triple[1] as i32, triple[2] as i32];
                    if arc.contains(&p) {
                        return Err(format!("duplicate point {p:?} in arc"));
                    }
                    arc.push(p);
                    triple.clear();
                } else if depth == 2 {
                    if !arc.is_empty() {
                        if arc.len() < 5 {
                            return Err(format!("arc of size {} < 5", arc.len()));
                        }
                        pool.push(std::mem::take(&mut arc));
                    }
                }
                depth -= 1;
                if depth < 0 {
                    return Err("unbalanced brackets".into());
                }
            }
            ',' | ' ' | '\t' | '\r' | '\n' => {
                if let Some(v) = cur.take() {
                    triple.push(v);
                }
            }
            '0'..='9' => {
                cur = Some(cur.unwrap_or(0) * 10 + (ch as i64 - '0' as i64));
            }
            _ => return Err(format!("unexpected character {ch:?}")),
        }
    }
    if depth != 0 {
        return Err("unbalanced brackets".into());
    }
    Ok(pool)
}

struct SeedWorker<'a> {
    tid: usize,
    arm: SeedArm,
    rng: Rng,
    st: SearchState,
    best: Vec<Point>,
    core: Vec<Point>, // protected arm: arc points currently shielded from ruin
    stall: u64,
    stall_limit: u64,
    orders: &'a [Vec<u16>],
    pool: &'a [Vec<Point>],
    shared: &'a Mutex<SeedShared>,
    t0: Instant,
    out_dir: &'a str,
    reached: Vec<bool>,
    local: SeedArmStats,
}

impl<'a> SeedWorker<'a> {
    fn now(&self) -> f64 {
        self.t0.elapsed().as_secs_f64()
    }

    fn greedy_pass(&mut self, order: &[u16]) {
        for &ci in order {
            if self.st.is_addable_cell(ci as usize) {
                self.st.add_point(cell_point(ci as usize));
            }
        }
    }

    fn build_order(&mut self, key_prob: f64) -> Vec<u16> {
        if self.rng.unit() < key_prob {
            self.orders[self.rng.below(self.orders.len())].clone()
        } else {
            let mut order: Vec<u16> = (0..NCELLS as u16).collect();
            self.rng.shuffle16(&mut order);
            order
        }
    }

    /// Restart build. Control: recipe scratch greedy (70% key / 30% shuffled).
    /// Seeded arms: random similarity image of a random pool arc, loaded into
    /// a fresh exact integer state, then greedy-completed the same way.
    fn restart_build(&mut self) {
        self.st = SearchState::new();
        self.core.clear();
        self.stall = 0;
        if self.arm != SeedArm::Control && !self.pool.is_empty() {
            let arc = &self.pool[self.rng.below(self.pool.len())];
            let perm = PERMS[self.rng.below(6)];
            let flips = self.rng.below(8) as u32;
            let r = 1 + self.rng.below(12) as i64;
            let t = [
                self.rng.below(13) as i64,
                self.rng.below(13) as i64,
                self.rng.below(13) as i64,
            ];
            let mut img: Vec<Point> = arc.iter().map(|&p| apply_sim(p, perm, flips, r, t)).collect();
            // exact safety net (cheap: C(14,5) dets): the image must be an arc
            // mod 13, hence valid over Z.
            assert!(
                find_zero_5subset_mod13(&img).is_none(),
                "similarity image not an arc — engine bug"
            );
            // 50% of seeded restarts: random SUB-arc of size 8..len as a more
            // flexible core (subsets of arcs are arcs — hereditary condition).
            if self.rng.unit() < 0.5 && img.len() > 8 {
                for i in 0..img.len() {
                    let j = i + self.rng.below(img.len() - i);
                    img.swap(i, j);
                }
                let keep = self.rng.randint(8, img.len());
                img.truncate(keep);
                self.local.subarc_restarts += 1;
            }
            for &p in &img {
                self.st.add_point(p);
            }
            if self.arm == SeedArm::Protected {
                self.core = img.clone();
            }
        }
        let order = self.build_order(0.7);
        self.greedy_pass(&order);
        let size = self.st.len().min(MAX_SIZE_STAT - 1);
        self.local.restarts += 1;
        self.local.build_hist[size] += 1;
    }

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

    fn record_reached(&mut self) {
        let size = self.best.len();
        for s in 30..=size.min(MAX_SIZE_STAT - 1) {
            if !self.reached[s] {
                self.reached[s] = true;
                let ts = self.now();
                let mut sh = self.shared.lock().unwrap();
                sh.events.push(format!(
                    "{{\"t\":{ts:.1},\"worker\":{},\"arm\":\"{}\",\"what\":\"worker_reached size={s}\"}}",
                    self.tid,
                    self.arm.name()
                ));
            }
        }
    }

    fn push_shared(&mut self, pts: &[Point]) {
        let size = pts.len();
        if size < 31 {
            return;
        }
        if size >= 33 {
            assert!(
                find_zero_5subset(pts).is_none(),
                "INVALID set of size {size} produced by search — engine bug"
            );
        }
        let canon = canonical_form(pts);
        let ts = self.now();
        // ---- candidate-34 alarm FIRST, unconditionally (never behind dedup,
        // never behind the overflow cap — a dropped 34 is the worst failure) ----
        if size >= 34 {
            let path = format!("{}/CANDIDATE34_IMMEDIATE.json", self.out_dir);
            let _ = std::fs::write(&path, points_json(pts));
            eprintln!(
                "!!! CANDIDATE 34-SET FOUND by worker {} ({}) at t={ts:.1}s !!!",
                self.tid,
                self.arm.name()
            );
            let mut sh = self.shared.lock().unwrap();
            if sh.candidate34.is_none() {
                sh.candidate34 = Some(pts.to_vec());
            }
        }
        let mut sh = self.shared.lock().unwrap();
        // per-arm private dedup: unbiased per-arm discovery counting
        let sidx = size.min(MAX_SIZE_STAT - 1);
        if sh.seen_arm[self.arm.idx()].len() < DEDUP_CAP
            && sh.seen_arm[self.arm.idx()].insert(canon.clone())
        {
            sh.stats[self.arm.idx()].distinct_finds[sidx] += 1;
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
            false
        };
        if !is_new {
            return;
        }
        if size > sh.best_size {
            sh.best_size = size;
            sh.events.push(format!(
                "{{\"t\":{ts:.1},\"worker\":{},\"arm\":\"{}\",\"what\":\"new_best size={size}\"}}",
                self.tid,
                self.arm.name()
            ));
        }
        let log_cap = if size >= 33 { LOG_CAP_33PLUS } else { LOG_CAP_32 };
        if size >= 32 && sh.logged_per_size[sidx] < log_cap as u64 {
            sh.logged_per_size[sidx] += 1;
            sh.pending_log.push(FoundSetS {
                ts,
                worker: self.tid,
                arm: self.arm,
                size,
                points: pts.to_vec(),
            });
        }
    }

    fn flush_stats(&mut self) {
        let mut sh = self.shared.lock().unwrap();
        let dst = &mut sh.stats[self.arm.idx()];
        dst.iters += self.local.iters;
        dst.restarts += self.local.restarts;
        for i in 0..MAX_SIZE_STAT {
            dst.build_hist[i] += self.local.build_hist[i];
            // distinct_finds are written directly under the lock in push_shared
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
        dst.core_shrinks += self.local.core_shrinks;
        dst.subarc_restarts += self.local.subarc_restarts;
        self.local = SeedArmStats {
            build_hist: vec![0; MAX_SIZE_STAT],
            distinct_finds: vec![0; MAX_SIZE_STAT],
            ..Default::default()
        };
    }

    fn run(&mut self, deadline: Instant) {
        self.restart_build();
        self.best = self.st.points().to_vec();
        self.record_reached();
        let snapshot = self.best.clone();
        self.push_shared(&snapshot);
        let mut last_flush = Instant::now();

        while Instant::now() < deadline {
            self.local.iters += 1;
            let prev_size = self.best.len();
            let prev_canon33 =
                if prev_size == 33 { Some(canonical_form(&self.best)) } else { None };
            // snapshot the protected core: a REJECTED full restart must restore
            // it together with the point set (Codex review finding #1)
            let saved_core = self.core.clone();
            let saved_stall = self.stall;
            let mut full_restart = self.best.is_empty() || self.rng.unit() < 0.15;

            if !full_restart {
                // ---- ILS ruin-and-rebuild from best (recipe parameters) ----
                let m = self.best.len();
                let removable: Vec<Point> = if self.arm == SeedArm::Protected {
                    self.best.iter().copied().filter(|p| !self.core.contains(p)).collect()
                } else {
                    self.best.clone()
                };
                if removable.len() < 2 {
                    full_restart = true; // nothing to ruin: degenerate, restart
                } else {
                    self.local.ils_trials += 1;
                    let r = self
                        .rng
                        .randint((m / 20).max(1), (m / 4).max(2))
                        .min(removable.len());
                    // r distinct victims from the removable set
                    let mut idx: Vec<u16> = (0..removable.len() as u16).collect();
                    for i in 0..r {
                        let j = i + self.rng.below(removable.len() - i);
                        idx.swap(i, j);
                    }
                    for &i in &idx[..r] {
                        self.st.remove_point(removable[i as usize]);
                    }
                    let order = self.build_order(0.8);
                    self.greedy_pass(&order);
                }
            }
            if full_restart {
                self.restart_build();
            }

            // ---- acceptance (recipe: >= replaces best) ----
            let new_size = self.st.len();
            if prev_size == 33 {
                self.local.at33_trials += 1;
            }
            if new_size >= prev_size && new_size > 0 {
                let result: Vec<Point> = self.st.points().to_vec();
                if new_size > prev_size {
                    self.local.accepts_improve += 1;
                    self.stall = 0;
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
                self.restore_to_best();
                self.core = saved_core;
                self.stall = saved_stall;
            }

            // ---- protected arm: stall-triggered core shrink ----
            if self.arm == SeedArm::Protected && !full_restart {
                self.stall += 1;
                if self.stall >= self.stall_limit && !self.core.is_empty() {
                    let i = self.rng.below(self.core.len());
                    self.core.swap_remove(i);
                    self.local.core_shrinks += 1;
                    self.stall = 0;
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

fn seed_arm_stats_json(s: &SeedArmStats) -> String {
    let hist: Vec<String> = (0..MAX_SIZE_STAT)
        .filter(|&i| s.build_hist[i] > 0)
        .map(|i| format!("\"{}\":{}", i, s.build_hist[i]))
        .collect();
    let finds: Vec<String> = (0..MAX_SIZE_STAT)
        .filter(|&i| s.distinct_finds[i] > 0)
        .map(|i| format!("\"{}\":{}", i, s.distinct_finds[i]))
        .collect();
    format!(
        "{{\"iters\":{},\"restarts\":{},\"build_hist\":{{{}}},\"ils_trials\":{},\"accepts_improve\":{},\"accepts_equal\":{},\"rejects\":{},\"at33_trials\":{},\"at33_drop\":{},\"at33_same\":{},\"at33_move\":{},\"at33_up\":{},\"core_shrinks\":{},\"subarc_restarts\":{},\"distinct_finds\":{{{}}}}}",
        s.iters, s.restarts, hist.join(","), s.ils_trials, s.accepts_improve,
        s.accepts_equal, s.rejects, s.at33_trials, s.at33_drop, s.at33_same,
        s.at33_move, s.at33_up, s.core_shrinks, s.subarc_restarts, finds.join(",")
    )
}

pub fn run_seeded(cfg: &SeedConfig) -> i32 {
    std::fs::create_dir_all(&cfg.out_dir).expect("cannot create out dir");
    let pool_text = std::fs::read_to_string(&cfg.arcs_path).expect("cannot read arcs file");
    let mut pool = parse_arc_pool(&pool_text).expect("cannot parse arcs file");
    // seeded arms are advertised as 13/14-arc cores: enforce it here
    pool.retain(|a| a.len() >= 13);
    assert!(!pool.is_empty(), "empty arc pool (after size>=13 filter)");
    let orders = sorted_orders();
    let threads = cfg.control + cfg.free + cfg.protected;
    let shared = Mutex::new(SeedShared {
        best_size: 0,
        seen: HashMap::new(),
        seen_arm: std::array::from_fn(|_| HashSet::new()),
        seen_overflow: 0,
        pending_log: Vec::new(),
        logged_per_size: vec![0; MAX_SIZE_STAT],
        events: Vec::new(),
        stats: std::array::from_fn(|_| SeedArmStats {
            build_hist: vec![0; MAX_SIZE_STAT],
            distinct_finds: vec![0; MAX_SIZE_STAT],
            ..Default::default()
        }),
        candidate34: None,
        workers_done: 0,
    });
    let t0 = Instant::now();
    let deadline = t0 + Duration::from_secs_f64(cfg.secs);
    let status_path = format!("{}/STATUS.json", cfg.out_dir);
    let jsonl_path = format!("{}/found_sets.jsonl", cfg.out_dir);
    let start_unix = unix_now();
    println!(
        "f13seed: pool={} arcs (sizes {:?}), threads={} (control={} free={} protected={}), secs={}, stall={}, out={}",
        pool.len(),
        {
            let mut h: HashMap<usize, usize> = HashMap::new();
            for a in &pool {
                *h.entry(a.len()).or_default() += 1;
            }
            let mut v: Vec<_> = h.into_iter().collect();
            v.sort();
            v
        },
        threads,
        cfg.control,
        cfg.free,
        cfg.protected,
        cfg.secs,
        cfg.stall,
        cfg.out_dir
    );

    std::thread::scope(|sc| {
        for tid in 0..threads {
            let arm = if tid < cfg.control {
                SeedArm::Control
            } else if tid < cfg.control + cfg.free {
                SeedArm::Free
            } else {
                SeedArm::Protected
            };
            let orders = &orders;
            let pool = &pool;
            let shared = &shared;
            let out_dir = cfg.out_dir.as_str();
            let seed = cfg.seed ^ ((tid as u64 + 1) << 32);
            let stall_limit = cfg.stall;
            sc.spawn(move || {
                let mut w = SeedWorker {
                    tid,
                    arm,
                    rng: Rng::new(seed),
                    st: SearchState::new(),
                    best: Vec::new(),
                    core: Vec::new(),
                    stall: 0,
                    stall_limit,
                    orders,
                    pool,
                    shared,
                    t0,
                    out_dir,
                    reached: vec![false; MAX_SIZE_STAT],
                    local: SeedArmStats {
                        build_hist: vec![0; MAX_SIZE_STAT],
                        distinct_finds: vec![0; MAX_SIZE_STAT],
                        ..Default::default()
                    },
                };
                w.run(deadline);
            });
        }

        let mut jsonl = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&jsonl_path)
            .expect("cannot open jsonl");
        loop {
            let (pending, status, done) = {
                let mut sh = shared.lock().unwrap();
                let done = sh.workers_done == threads;
                let pending: Vec<FoundSetS> = sh.pending_log.drain(..).collect();
                let status = format!(
                    "{{\"start_unix\":{:.0},\"elapsed_secs\":{:.1},\"budget_secs\":{},\"threads\":{},\"arms\":{{\"control\":{},\"free\":{},\"protected\":{}}},\"done\":{},\"best_size\":{},\"candidate34_found\":{},\"seen_total\":{},\"seen_overflow\":{},\"stats_control\":{},\"stats_free\":{},\"stats_protected\":{},\"events\":[{}]}}",
                    start_unix,
                    t0.elapsed().as_secs_f64(),
                    cfg.secs,
                    threads,
                    cfg.control,
                    cfg.free,
                    cfg.protected,
                    done,
                    sh.best_size,
                    sh.candidate34.is_some(),
                    sh.seen.len(),
                    sh.seen_overflow,
                    seed_arm_stats_json(&sh.stats[0]),
                    seed_arm_stats_json(&sh.stats[1]),
                    seed_arm_stats_json(&sh.stats[2]),
                    sh.events.join(",")
                );
                (pending, status, done)
            };
            for f in &pending {
                let line = format!(
                    "{{\"t\":{:.1},\"worker\":{},\"arm\":\"{}\",\"size\":{},\"points\":{}}}\n",
                    f.ts,
                    f.worker,
                    f.arm.name(),
                    f.size,
                    points_json(&f.points)
                );
                let _ = jsonl.write_all(line.as_bytes());
            }
            let _ = jsonl.flush();
            let _ = std::fs::write(&status_path, &status);
            if done {
                break;
            }
            // safety valve: if a worker panicked, workers_done never reaches
            // `threads`; don't spin forever past the budget
            if Instant::now() > deadline + Duration::from_secs(180) {
                eprintln!("WARNING: writer grace deadline exceeded — a worker likely panicked; exiting writer loop");
                break;
            }
            std::thread::sleep(Duration::from_secs(15));
        }
    });

    let sh = shared.lock().unwrap();
    println!(
        "f13seed done: best_size={} candidate34={}",
        sh.best_size,
        sh.candidate34.is_some()
    );
    if let Some(c) = &sh.candidate34 {
        let path = format!("{}/CANDIDATE34_FINAL.json", cfg.out_dir);
        let _ = std::fs::write(&path, points_json(c));
        println!("!!! 34-SET SAVED to {path} !!!");
    }
    0
}

// ------------------------------ tests ----------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_seed_is_13_arc() {
        let arc = algebraic_seed();
        assert_eq!(arc.len(), 13);
        // distinct cells
        let mut cells: Vec<usize> = arc.iter().map(|&p| cell_index(p)).collect();
        cells.sort_unstable();
        cells.dedup();
        assert_eq!(cells.len(), 13);
        assert!(find_zero_5subset_mod13(&arc).is_none(), "curve arc has a zero 5-subset mod 13");
        assert!(find_zero_5subset(&arc).is_none(), "curve arc invalid over Z");
        let st = F13State::from_points(&arc);
        assert!(st.is_valid_arc());
    }

    #[test]
    fn f13_incremental_matches_bruteforce() {
        let mut rng = Rng::new(0xF13F13F13);
        for _ in 0..3 {
            let mut pts: Vec<Point> = Vec::new();
            while pts.len() < 9 {
                let p = [rng.below(13) as i32, rng.below(13) as i32, rng.below(13) as i32];
                if !pts.contains(&p) {
                    pts.push(p);
                }
            }
            let mut st = F13State::from_points(&pts);
            assert_eq!(st.blocked, blocked_bruteforce_mod13(&pts));
            // removes
            let mut cur = pts.clone();
            for victim_idx in [0usize, 3] {
                let victim = cur[victim_idx.min(cur.len() - 1)];
                st.remove_point(victim);
                cur.retain(|&p| p != victim);
                assert_eq!(st.blocked, blocked_bruteforce_mod13(&cur));
            }
        }
    }

    /// TRAP, mod-13 flavor: a quadruple with nonzero integer cofactor vector
    /// that collapses to zero mod 13 must block ALL 2197 cells in F13State,
    /// while the integer engine does NOT block all cells for it.
    #[test]
    fn trap_mod13_only_degenerate_quadruple() {
        let mut rng = Rng::new(0xBA11);
        let mut found = None;
        for _ in 0..2_000_000 {
            let q: [Point; 4] = std::array::from_fn(|_| {
                [rng.below(13) as i32, rng.below(13) as i32, rng.below(13) as i32]
            });
            let cells: HashSet<usize> = q.iter().map(|&p| cell_index(p)).collect();
            if cells.len() != 4 {
                continue;
            }
            let c = cofactor_vec(&q);
            if c != [0i64; 5] && cof13(&q) == [0i32; 5] {
                found = Some(q);
                break;
            }
        }
        let q = found.expect("no mod-13-only degenerate quadruple found — increase trials");
        let st13 = F13State::from_points(&q);
        assert!((0..NCELLS).all(|i| st13.blocked_count(i) >= 1), "mod-13 trap quad must block all cells");
        let stz = SearchState::from_points(&q);
        let nb = (0..NCELLS).filter(|&i| stz.blocked_count(i) >= 1).count();
        assert!(nb < NCELLS, "integer engine must NOT block all cells for this quad");
    }

    #[test]
    fn similarity_image_of_arc_is_arc_and_canonical13_invariant() {
        let arc = algebraic_seed();
        let img: Vec<Point> =
            arc.iter().map(|&p| apply_sim(p, [2, 0, 1], 0b101, 7, [3, 11, 5])).collect();
        assert!(find_zero_5subset_mod13(&img).is_none(), "similarity image lost the arc property");
        assert_eq!(canonical13(&arc), canonical13(&img), "canonical13 not invariant");
        // a genuinely different set should (generically) differ
        let mut other = arc.clone();
        other[0] = [1, 1, 0];
        if find_zero_5subset_mod13(&other).is_none() {
            assert_ne!(canonical13(&other), canonical13(&arc));
        }
    }

    #[test]
    fn parse_arc_pool_roundtrip() {
        let pool = vec![algebraic_seed(), algebraic_seed()[..5].to_vec()];
        let txt = format!(
            "[{}]",
            pool.iter().map(|a| points_json(a)).collect::<Vec<_>>().join(",\n")
        );
        let back = parse_arc_pool(&txt).unwrap();
        assert_eq!(back, pool);
    }
}
