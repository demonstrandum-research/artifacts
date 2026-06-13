//! Exact integer search core for the "no 5 on a sphere or plane" grid problem
//! (AlphaEvolve repository Problem 6.60), n = 13, grid {0..12}^3.
//!
//! All arithmetic is exact integer arithmetic. NO floats anywhere.
//!
//! Forbidden configuration: 5 points p1..p5 with det = 0 of the 5x5 matrix with
//! rows (x, y, z, x^2+y^2+z^2, 1) — covers both cospherical AND coplanar 5-tuples.
//!
//! Incremental engine: for every 4-subset Q of the current set S we keep its
//! *cofactor vector* c_Q in Z^5, defined so that for every point p
//!     dot(c_Q, (x, y, z, x^2+y^2+z^2, 1)) == det5(Q, p).
//! A cell p is addable iff the dot product is nonzero for ALL 4-subsets Q of S.
//!
//! TRAP CASE (unit-tested below): a rank-degenerate quadruple (4 collinear or
//! 4 cocircular points) has c_Q == [0,0,0,0,0], so the dot product is 0 for
//! EVERY p — such a quadruple must block ALL cells. The full-grid zero-scan
//! handles this automatically (every dot product is 0, so every cell is
//! recorded as blocked); sphere-center hashing schemes get this WRONG.
//!
//! Overflow analysis (n = 13, coordinates 0..12, w = x^2+y^2+z^2 <= 432):
//! cofactor components are 4x4 minors of rows (x,y,z,w,1):
//!   |c_0|,|c_1|,|c_2| <= 24*12*12*432   = 1_492_992
//!   |c_3|             <= 24*12*12*12    = 41_472
//!   |c_4|             <= 24*12*12*12*432 = 17_915_904
//! so |dot| <= 3*12*1_492_992 + 432*41_472 + 17_915_904 = 89_579_520 < 2^31:
//! the hot scan runs in i32. Cofactors themselves are computed in i64 and
//! narrowed through a *checked* bound (`narrow_checked`), so the i32 fast path
//! can never silently overflow.


/// Grid size, injected at compile time via the NO5_N environment variable
/// (general-n construct-search build; the original crate hardcoded 13).
/// Range cap 18: the dynamic `narrow_checked` bound stays < 2^29 for n <= 18,
/// so the i32 scan path can never alias the SIMD pad or overflow.
const fn parse_env_i32(s: &str) -> i32 {
    let b = s.as_bytes();
    let mut i = 0;
    let mut v = 0i32;
    while i < b.len() {
        assert!(b[i] >= b'0' && b[i] <= b'9');
        v = v * 10 + (b[i] - b'0') as i32;
        i += 1;
    }
    assert!(v >= 3 && v <= 18);
    v
}
pub const N: i32 = parse_env_i32(env!("NO5_N"));
pub const NCELLS: usize = (N as usize) * (N as usize) * (N as usize);
const WMAX: i64 = 3 * ((N as i64 - 1) * (N as i64 - 1));

pub type Point = [i32; 3];

#[inline]
pub fn in_grid(p: Point) -> bool {
    p.iter().all(|&c| (0..N).contains(&c))
}

#[inline]
pub fn cell_index(p: Point) -> usize {
    debug_assert!(in_grid(p));
    ((p[0] * N + p[1]) * N + p[2]) as usize
}

#[inline]
pub fn cell_point(i: usize) -> Point {
    let i = i as i32;
    [i / (N * N), (i / N) % N, i % N]
}

/// Lift p to (x, y, z, x^2+y^2+z^2, 1).
#[inline]
pub fn lift5(p: Point) -> [i64; 5] {
    let (x, y, z) = (p[0] as i64, p[1] as i64, p[2] as i64);
    [x, y, z, x * x + y * y + z * z, 1]
}

#[inline]
fn det3(m: [[i64; 3]; 3]) -> i64 {
    m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
}

/// Exact 4x4 integer determinant (cofactor expansion along the first row).
pub fn det4(m: [[i64; 4]; 4]) -> i64 {
    let mut det = 0i64;
    for j in 0..4 {
        let mut minor = [[0i64; 3]; 3];
        for r in 1..4 {
            let mut cc = 0;
            for c in 0..4 {
                if c != j {
                    minor[r - 1][cc] = m[r][c];
                    cc += 1;
                }
            }
        }
        let term = m[0][j] * det3(minor);
        det += if j % 2 == 0 { term } else { -term };
    }
    det
}

/// Exact lifted 5-point determinant: det of the 5x5 matrix with rows
/// (lift5(q_i)) for i=0..3 and lift5(p), computed as the equivalent 4x4
/// determinant of lifted differences. Zero iff the 5 points are cospherical
/// or coplanar (including all degenerate cases). Brute-force reference path.
pub fn det5(q: &[Point; 4], p: Point) -> i64 {
    let l0 = lift5(q[0]);
    let mut m = [[0i64; 4]; 4];
    for (r, src) in [q[1], q[2], q[3], p].iter().enumerate() {
        let l = lift5(*src);
        for c in 0..4 {
            m[r][c] = l[c] - l0[c];
        }
    }
    det4(m)
}

/// Cofactor vector c_Q in Z^5 of a 4-subset Q: for every point p,
///     dot(c_Q, lift5(p)) == det5(Q, p).
/// Rank-degenerate quadruples (4 collinear / 4 cocircular) give c_Q == [0;5]:
/// every dot product is then 0, i.e. the quadruple blocks ALL cells.
///
/// Straight-line evaluation via Laplace expansion along rows (0,1) vs (2,3):
/// all twenty 2x2 minors are computed once, then each 4x4 minor D4(a,b,c,d)
/// (columns a<b<c<d of the 4x5 lifted matrix) is
///     m_ab*n_cd - m_ac*n_bd + m_ad*n_bc + m_bc*n_ad - m_bd*n_ac + m_cd*n_ab
/// and c_j = (-1)^j * D4(columns != j). Exact i64; verified against det5 in tests.
pub fn cofactor_vec(q: &[Point; 4]) -> [i64; 5] {
    let r0 = lift5(q[0]);
    let r1 = lift5(q[1]);
    let r2 = lift5(q[2]);
    let r3 = lift5(q[3]);
    macro_rules! m2 {
        ($a:expr, $b:expr) => {
            r0[$a] * r1[$b] - r0[$b] * r1[$a]
        };
    }
    macro_rules! n2 {
        ($a:expr, $b:expr) => {
            r2[$a] * r3[$b] - r2[$b] * r3[$a]
        };
    }
    let (m01, m02, m03, m04) = (m2!(0, 1), m2!(0, 2), m2!(0, 3), m2!(0, 4));
    let (m12, m13, m14) = (m2!(1, 2), m2!(1, 3), m2!(1, 4));
    let (m23, m24, m34) = (m2!(2, 3), m2!(2, 4), m2!(3, 4));
    let (n01, n02, n03, n04) = (n2!(0, 1), n2!(0, 2), n2!(0, 3), n2!(0, 4));
    let (n12, n13, n14) = (n2!(1, 2), n2!(1, 3), n2!(1, 4));
    let (n23, n24, n34) = (n2!(2, 3), n2!(2, 4), n2!(3, 4));
    let d_1234 = m12 * n34 - m13 * n24 + m14 * n23 + m23 * n14 - m24 * n13 + m34 * n12;
    let d_0234 = m02 * n34 - m03 * n24 + m04 * n23 + m23 * n04 - m24 * n03 + m34 * n02;
    let d_0134 = m01 * n34 - m03 * n14 + m04 * n13 + m13 * n04 - m14 * n03 + m34 * n01;
    let d_0124 = m01 * n24 - m02 * n14 + m04 * n12 + m12 * n04 - m14 * n02 + m24 * n01;
    let d_0123 = m01 * n23 - m02 * n13 + m03 * n12 + m12 * n03 - m13 * n02 + m23 * n01;
    [d_1234, -d_0234, d_0134, -d_0124, d_0123]
}

/// Narrow a cofactor vector to i32 with a *proof-checked* bound guaranteeing
/// (a) the i32 dot-product scan over the whole grid can never overflow, and
/// (b) every partial sum stays below 2^29, so the SIMD pad value 2^30 can
/// never alias a genuine zero. For in-grid n=13 quadruples the true bound is
/// <= 89_579_520 < 2^27 (see module docs), so this assert is unreachable.
fn narrow_checked(c: [i64; 5]) -> [i32; 5] {
    let bound = (c[0].abs() + c[1].abs() + c[2].abs()) * (N as i64 - 1)
        + c[3].abs() * WMAX
        + c[4].abs();
    assert!(
        bound < (1i64 << 29),
        "cofactor too large for the i32 scan path (impossible for in-grid n=13 quadruples)"
    );
    [c[0] as i32, c[1] as i32, c[2] as i32, c[3] as i32, c[4] as i32]
}

/// Brute-force full certificate check: returns the first zero 5-subset, if any.
pub fn find_zero_5subset(points: &[Point]) -> Option<[Point; 5]> {
    let m = points.len();
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let q = [points[a], points[b], points[c], points[d]];
                    for e in d + 1..m {
                        if det5(&q, points[e]) == 0 {
                            return Some([points[a], points[b], points[c], points[d], points[e]]);
                        }
                    }
                }
            }
        }
    }
    None
}

/// Brute-force blocked-count grid (independent of the cofactor path; uses det5
/// directly). For each cell, counts 4-subsets Q of `points` with det5(Q,cell)==0.
pub fn blocked_bruteforce(points: &[Point]) -> Vec<u32> {
    let mut blocked = vec![0u32; NCELLS];
    let m = points.len();
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let q = [points[a], points[b], points[c], points[d]];
                    for (cell, slot) in blocked.iter_mut().enumerate() {
                        if det5(&q, cell_point(cell)) == 0 {
                            *slot += 1;
                        }
                    }
                }
            }
        }
    }
    blocked
}

struct Quad {
    /// Cell indices of the 4 member points (stable identifiers).
    members: [u16; 4],
    /// Cells blocked by this quadruple (dot == 0). Always contains the 4 member
    /// cells; contains ALL 2197 cells when the quadruple is rank-degenerate.
    cells: Vec<u16>,
}

/// Incremental blocked-cell search state over {0..12}^3.
pub struct SearchState {
    points: Vec<Point>,
    occupied: Vec<bool>,
    /// blocked[cell] = number of 4-subsets Q of S with dot(c_Q, lift(cell)) == 0.
    /// NOTE for occupied cells: every quad containing point p trivially blocks
    /// p's own cell (repeated-row determinant), contributing C(|S|-1,3) counts.
    blocked: Vec<u32>,
    quads: Vec<Quad>,
    pool: Vec<Vec<u16>>, // recycled cell-list buffers
    /// Statistics: total quadruple-cell zero-tests resolved (2197 per quad scan).
    pub evals: u64,
    /// Statistics: total quadruples processed by add_point.
    pub quads_processed: u64,
}

impl SearchState {
    pub fn new() -> Self {
        SearchState {
            points: Vec::new(),
            occupied: vec![false; NCELLS],
            blocked: vec![0u32; NCELLS],
            quads: Vec::new(),
            pool: Vec::new(),
            evals: 0,
            quads_processed: 0,
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

    pub fn is_occupied(&self, cell: usize) -> bool {
        self.occupied[cell]
    }

    pub fn is_addable_cell(&self, cell: usize) -> bool {
        !self.occupied[cell] && self.blocked[cell] == 0
    }

    pub fn addable_cells(&self) -> Vec<usize> {
        (0..NCELLS).filter(|&i| self.is_addable_cell(i)).collect()
    }

    /// Exact validity of S via the maintained structure: S is valid iff every
    /// member's blocked count equals exactly C(|S|-1, 3) (the trivial
    /// self-incidences of quads containing it) — any excess is a genuine
    /// zero 5-subset inside S.
    pub fn is_valid_set(&self) -> bool {
        let s = self.points.len() as u64;
        let trivial = if s >= 4 { (s - 1) * (s - 2) * (s - 3) / 6 } else { 0 };
        self.points
            .iter()
            .all(|&p| self.blocked[cell_index(p)] as u64 == trivial)
    }

    /// Find one quadruple Q of S that blocks `cell` (det5(Q, cell) == 0), if any.
    pub fn blocking_witness(&self, cell: usize) -> Option<[Point; 4]> {
        let ci = cell as u16;
        self.quads
            .iter()
            .find(|q| q.cells.contains(&ci))
            .map(|q| q.members.map(|m| cell_point(m as usize)))
    }

    /// Scan all 2197 cells for dot(c, lift(cell)) == 0, appending hits to `out`.
    ///
    /// Algebraic factoring: dot = [c0*x + c3*x^2 + c4] + [c1*y + c3*y^2] + [c2*z + c3*z^2],
    /// so a whole (x,y) column is one broadcast-add + compare against the
    /// 13-entry z-table (padded to 16 SIMD lanes with 2^30, which can never
    /// produce a zero since |partial sums| < 2^29 by the narrow_checked bound).
    /// A zero cofactor vector hits EVERY cell (trap case): every lane compares
    /// equal and all 2197 cells get recorded — nothing is ever skipped.
    ///
    /// AVX-512 path, fully branch-free main loops (no data-dependent branches,
    /// hence no mispredict flushes):
    ///   phase 0: base buffer B[col] = gx(x) + ty(y) for all 169 columns,
    ///            built with 13 overlapping 16-lane stores;
    ///   phase 1: one vpbroadcastd(m32) + vpaddd + vpcmpeqd per column, the
    ///            16-bit lane mask (bit i == z coordinate) stored to masks[];
    ///   phase 2: nonzero masks located 16-at-a-time with vptest; hits (avg ~5
    ///            per quadruple, all 2197 for the degenerate trap case) are
    ///            extracted on the rare taken branch.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "avx2"))]
    fn scan_zero_cells(&mut self, c: [i32; 5], out: &mut Vec<u16>) {
        use core::arch::x86_64::*;
        const NU: usize = N as usize;
        if NU > 16 {
            // z-table does not fit one 16-lane vector: exact scalar path
            return self.scan_zero_cells_scalar(c, out);
        }
        let (c0, c1, c2, c3, c4) = (c[0], c[1], c[2], c[3], c[4]);
        const PAD: i32 = 1 << 30;
        let mut tz = [PAD; 16];
        let mut ty = [0i32; 16];
        for v in 0..N {
            tz[v as usize] = c2 * v + c3 * v * v;
            ty[v as usize] = c1 * v + c3 * v * v;
        }
        let mut bbuf = [0i32; NU * NU + 16]; // +16: overlap slack of the last store
        let mut masks = [0u16; NU * NU + 16]; // zero padding for phase 2
        // SAFETY: avx512f/avx2 statically enabled; all loads/stores are within
        // the stack arrays above (bbuf store at x*13 has 64 bytes of room since
        // 12*13 + 16 = 172 <= 172; masks reads stay within 176).
        unsafe {
            let tzv = _mm512_loadu_si512(tz.as_ptr() as *const __m512i);
            let tyv = _mm512_loadu_si512(ty.as_ptr() as *const __m512i);
            let zero = _mm512_setzero_si512();
            for x in 0..N {
                let gx = c0 * x + c3 * x * x + c4;
                let bv = _mm512_add_epi32(_mm512_set1_epi32(gx), tyv);
                // lanes 13..15 are overwritten by the next row's correct values
                _mm512_storeu_si512(bbuf.as_mut_ptr().add(x as usize * NU) as *mut __m512i, bv);
            }
            for col in 0..NU * NU {
                let b = _mm512_set1_epi32(*bbuf.get_unchecked(col));
                let k = _mm512_cmpeq_epi32_mask(_mm512_add_epi32(b, tzv), zero);
                *masks.get_unchecked_mut(col) = k;
            }
            for blk in 0..(NU * NU).div_ceil(16) {
                let v = _mm256_loadu_si256(masks.as_ptr().add(blk * 16) as *const __m256i);
                if _mm256_testz_si256(v, v) == 0 {
                    for col in blk * 16..blk * 16 + 16 {
                        let mut k = *masks.get_unchecked(col);
                        let idx = (col * NU) as u16;
                        while k != 0 {
                            out.push(idx + k.trailing_zeros() as u16);
                            k &= k - 1;
                        }
                    }
                }
            }
        }
        self.evals += NCELLS as u64;
    }

    /// AVX2 path: two 8-lane halves of the padded z-table, vptest for the
    /// (rare) any-hit branch, scalar re-scan only on hits.
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
    fn scan_zero_cells(&mut self, c: [i32; 5], out: &mut Vec<u16>) {
        use core::arch::x86_64::*;
        if N > 16 {
            // z-table does not fit two 8-lane vectors: exact scalar path
            return self.scan_zero_cells_scalar(c, out);
        }
        let (c0, c1, c2, c3, c4) = (c[0], c[1], c[2], c[3], c[4]);
        const PAD: i32 = 1 << 30;
        let mut tz = [PAD; 16];
        let mut ty = [0i32; N as usize];
        for v in 0..N {
            tz[v as usize] = c2 * v + c3 * v * v;
            ty[v as usize] = c1 * v + c3 * v * v;
        }
        // SAFETY: avx2 is statically enabled (cfg target_feature); loads are
        // from properly sized stack arrays.
        unsafe {
            let tz0 = _mm256_loadu_si256(tz.as_ptr() as *const __m256i);
            let tz1 = _mm256_loadu_si256(tz.as_ptr().add(8) as *const __m256i);
            let zero = _mm256_setzero_si256();
            let mut idx = 0u16;
            for x in 0..N {
                let gx = c0 * x + c3 * x * x + c4;
                for y in 0..N as usize {
                    let base = gx + ty[y];
                    let b = _mm256_set1_epi32(base);
                    let e0 = _mm256_cmpeq_epi32(_mm256_add_epi32(b, tz0), zero);
                    let e1 = _mm256_cmpeq_epi32(_mm256_add_epi32(b, tz1), zero);
                    let any = _mm256_or_si256(e0, e1);
                    if _mm256_testz_si256(any, any) == 0 {
                        for (z, &t) in tz.iter().enumerate().take(N as usize) {
                            if base + t == 0 {
                                out.push(idx + z as u16);
                            }
                        }
                    }
                    idx += N as u16;
                }
            }
        }
        self.evals += NCELLS as u64;
    }

    /// Portable scalar fallback of the same column scan (identical semantics).
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
    fn scan_zero_cells(&mut self, c: [i32; 5], out: &mut Vec<u16>) {
        self.scan_zero_cells_scalar(c, out);
    }

    /// Exact scalar column scan (used directly when N > 16, and as the
    /// portable fallback). Identical semantics to the SIMD paths.
    fn scan_zero_cells_scalar(&mut self, c: [i32; 5], out: &mut Vec<u16>) {
        let (c0, c1, c2, c3, c4) = (c[0], c[1], c[2], c[3], c[4]);
        let mut tz = [0i32; N as usize];
        let mut ty = [0i32; N as usize];
        for v in 0..N {
            tz[v as usize] = c2 * v + c3 * v * v;
            ty[v as usize] = c1 * v + c3 * v * v;
        }
        let mut idx = 0u16;
        for x in 0..N {
            let gx = c0 * x + c3 * x * x + c4;
            for y in 0..N as usize {
                let base = gx + ty[y];
                let mut any = 0u32;
                for z in 0..N as usize {
                    any |= ((base + tz[z]) == 0) as u32;
                }
                if any != 0 {
                    for z in 0..N as usize {
                        if base + tz[z] == 0 {
                            out.push(idx + z as u16);
                        }
                    }
                }
                idx += N as u16;
            }
        }
        self.evals += NCELLS as u64;
    }

    /// Diagnostic: run the production zero-scan for an arbitrary cofactor
    /// vector (profiling/validation only).
    #[doc(hidden)]
    pub fn profile_scan(&mut self, c: [i64; 5], out: &mut Vec<u16>) {
        let c = narrow_checked(c);
        self.scan_zero_cells(c, out);
    }

    /// Add point p (must be in-grid, cell unoccupied). Creates C(|S|,3) new
    /// quadruples, computes their exact cofactor vectors, and updates the
    /// blocked grid. p itself may be a blocked cell (the structure stays
    /// consistent; use is_valid_set() to test validity).
    pub fn add_point(&mut self, p: Point) {
        assert!(in_grid(p), "point {:?} outside {{0..12}}^3", p);
        let pc = cell_index(p);
        assert!(!self.occupied[pc], "cell {:?} already occupied", p);
        let s = self.points.len();
        for i in 0..s {
            for j in i + 1..s {
                for k in j + 1..s {
                    let q = [self.points[i], self.points[j], self.points[k], p];
                    let c = narrow_checked(cofactor_vec(&q));
                    let mut cells = self.pool.pop().unwrap_or_default();
                    cells.clear();
                    self.scan_zero_cells(c, &mut cells);
                    for &ci in &cells {
                        self.blocked[ci as usize] += 1;
                    }
                    self.quads.push(Quad {
                        members: [
                            cell_index(self.points[i]) as u16,
                            cell_index(self.points[j]) as u16,
                            cell_index(self.points[k]) as u16,
                            pc as u16,
                        ],
                        cells,
                    });
                    self.quads_processed += 1;
                }
            }
        }
        self.points.push(p);
        self.occupied[pc] = true;
    }

    /// Remove point p from S, retiring every quadruple containing it and
    /// decrementing the blocked counts it contributed.
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
                self.pool.push(q.cells);
            } else {
                i += 1;
            }
        }
        let idx = self.points.iter().position(|&q| q == p).unwrap();
        self.points.swap_remove(idx);
        self.occupied[pc as usize] = false;
    }
}

impl Default for SearchState {
    fn default() -> Self {
        Self::new()
    }
}

// ------------------------------ tests ---------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// xorshift64* — deterministic, no external deps.
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
        fn coord(&mut self) -> i32 {
            (self.next() % N as u64) as i32
        }
        fn point(&mut self) -> Point {
            [self.coord(), self.coord(), self.coord()]
        }
        fn distinct_points(&mut self, m: usize) -> Vec<Point> {
            let mut v: Vec<Point> = Vec::new();
            while v.len() < m {
                let p = self.point();
                if !v.contains(&p) {
                    v.push(p);
                }
            }
            v
        }
    }

    #[test]
    fn det4_known_values() {
        let id = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]];
        assert_eq!(det4(id), 1);
        let m = [[2, 0, 0, 0], [0, 3, 0, 0], [0, 0, 4, 0], [0, 0, 0, 5]];
        assert_eq!(det4(m), 120);
        let singular = [[1, 2, 3, 4], [2, 4, 6, 8], [1, 0, 1, 0], [0, 1, 0, 1]];
        assert_eq!(det4(singular), 0);
        // antisymmetry under row swap
        let a = [[1, 5, 2, 7], [3, 1, 4, 1], [5, 9, 2, 6], [5, 3, 5, 8]];
        let mut b = a;
        b.swap(0, 1);
        assert_eq!(det4(a), -det4(b));
    }

    /// Defining identity of the cofactor vector, on random (incl. degenerate) data.
    #[test]
    fn cofactor_identity_random() {
        let mut rng = Rng(0xDEADBEEF12345678);
        for _ in 0..2000 {
            let q = [rng.point(), rng.point(), rng.point(), rng.point()];
            let p = rng.point();
            let c = cofactor_vec(&q);
            let l = lift5(p);
            let dot: i64 = (0..5).map(|k| c[k] * l[k]).sum();
            assert_eq!(dot, det5(&q, p), "cofactor identity failed for {:?} {:?}", q, p);
        }
    }

    // ---------------- TRAP CASE: rank-degenerate quadruples ----------------
    // 4 collinear or 4 cocircular points => zero cofactor vector => must block
    // ALL cells (the pencil of spheres/planes through them covers all of space).

    fn assert_blocks_all_cells(quad: [Point; 4]) {
        assert_eq!(
            cofactor_vec(&quad),
            [0i64; 5],
            "rank-degenerate quadruple {:?} must have zero cofactor vector",
            quad
        );
        let st = SearchState::from_points(&quad);
        assert_eq!(st.len(), 4);
        // every single cell of the grid is blocked, occupied or not
        assert!(
            (0..NCELLS).all(|i| st.blocked_count(i) >= 1),
            "degenerate quadruple {:?} failed to block every cell",
            quad
        );
        assert!(st.addable_cells().is_empty());
        // cross-check against the det5 brute force on a sample of cells
        for cell in (0..NCELLS).step_by(97) {
            assert_eq!(det5(&quad, cell_point(cell)), 0);
        }
    }

    #[test]
    fn trap_collinear_axis() {
        assert_blocks_all_cells([[0, 0, 0], [1, 0, 0], [2, 0, 0], [3, 0, 0]]);
    }

    #[test]
    fn trap_collinear_skew() {
        // direction (1,2,3), not axis-aligned
        assert_blocks_all_cells([[0, 0, 0], [1, 2, 3], [2, 4, 6], [3, 6, 9]]);
    }

    #[test]
    fn trap_cocircular_unit_square() {
        assert_blocks_all_cells([[0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0]]);
    }

    #[test]
    fn trap_cocircular_rotated_rectangle() {
        // rectangle spanned by u=(4,3,0), v=(-3,4,0) (|u|=|v|=5), shifted into the grid
        assert_blocks_all_cells([[3, 0, 0], [7, 3, 0], [4, 7, 0], [0, 4, 0]]);
    }

    #[test]
    fn trap_cocircular_tilted_plane() {
        // rectangle in the tilted plane z = x: u=(1,0,1), v=(0,1,0)
        assert_blocks_all_cells([[0, 0, 0], [1, 0, 1], [1, 1, 1], [0, 1, 0]]);
    }

    #[test]
    fn nondegenerate_quad_blocks_few_cells() {
        // generic quadruple: nonzero cofactor, blocks its own 4 cells plus the
        // (few) other grid points on its unique sphere/plane — never all cells
        let quad: [Point; 4] = [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 5]];
        let c = cofactor_vec(&quad);
        assert_ne!(c, [0i64; 5]);
        let st = SearchState::from_points(&quad);
        let nblocked = (0..NCELLS).filter(|&i| st.blocked_count(i) >= 1).count();
        assert!(nblocked < NCELLS / 2, "generic quad blocked {} cells", nblocked);
        for p in quad {
            assert!(st.blocked_count(cell_index(p)) >= 1); // members always blocked
        }
    }

    /// Incremental blocked grid == brute-force det5 recount, through adds AND removes.
    #[test]
    fn incremental_matches_bruteforce() {
        for seed in [1u64, 42, 0xABCDEF] {
            let mut rng = Rng(seed | 1);
            let pts = rng.distinct_points(10);
            let mut st = SearchState::from_points(&pts);
            assert_eq!(st.blocked, blocked_bruteforce(&pts), "after build, seed {seed}");
            // remove three points (front, middle, back of the list)
            let mut cur = pts.clone();
            for victim_idx in [0usize, 4, 6] {
                let victim = cur[victim_idx.min(cur.len() - 1)];
                st.remove_point(victim);
                cur.retain(|&p| p != victim);
                assert_eq!(st.blocked, blocked_bruteforce(&cur), "after remove, seed {seed}");
            }
            // re-add a fresh point
            let mut extra = rng.point();
            while cur.contains(&extra) {
                extra = rng.point();
            }
            st.add_point(extra);
            cur.push(extra);
            assert_eq!(st.blocked, blocked_bruteforce(&cur), "after re-add, seed {seed}");
        }
    }

    /// is_valid_set (incremental invariant) == find_zero_5subset (brute force).
    #[test]
    fn validity_invariant_matches_bruteforce() {
        let mut rng = Rng(0x5EED5EED5EED5EED);
        for _ in 0..30 {
            let pts = rng.distinct_points(8);
            let st = SearchState::from_points(&pts);
            let brute_valid = find_zero_5subset(&pts).is_none();
            assert_eq!(st.is_valid_set(), brute_valid, "set {:?}", pts);
        }
        // explicit VALID fixture: first 8 points of the published n=7 record
        // (a subset of a valid set is valid)
        let valid: Vec<Point> = vec![
            [5, 2, 0], [1, 2, 6], [6, 0, 6], [0, 0, 2],
            [5, 6, 3], [5, 6, 5], [1, 6, 6], [0, 1, 6],
        ];
        assert!(find_zero_5subset(&valid).is_none());
        assert!(SearchState::from_points(&valid).is_valid_set());
        // explicit INVALID fixture: 5 coplanar points (z = 0) among 8
        let invalid: Vec<Point> = vec![
            [0, 0, 0], [1, 0, 0], [2, 0, 0], [0, 1, 0], [0, 2, 0],
            [5, 5, 5], [7, 3, 2], [1, 9, 4],
        ];
        assert!(find_zero_5subset(&invalid).is_some());
        assert!(!SearchState::from_points(&invalid).is_valid_set());
    }
}
