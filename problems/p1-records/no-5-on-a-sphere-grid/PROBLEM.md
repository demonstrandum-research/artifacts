# Problem: the "no 5 on a sphere" grid problem (AlphaEvolve Problem 60)

**Slug:** `no-5-on-a-sphere-grid`
**Status:** Gate 0 dossier (deep assessment, 2026-06-11)
**Assessor:** record-assessment subagent; Codex foil thread `019eb971-cd06-7d03-ab15-ea480fd0f055`

---

## 1. Frozen exact statement

Verbatim from arXiv:2511.02864v3 ("Mathematical exploration and discovery at scale",
Georgiev, Gomez-Serrano, Tao, Wagner et al., v3 dated 2025-12-22), Section 6, Problem 6.60
(PDF page 63, extracted 2026-06-11 from the downloaded PDF, `data/paper.pdf`):

> **Problem 6.60.** For n a natural number, let C_6.60(n) denote the size of the largest
> subset of [n]^3 = {1,...,n}^3 such that no 5 points lie on a sphere or a plane. Obtain
> upper and lower bounds for C_6.60(n) that are as strong as possible.

Identical statement on the official problem page (fetched 2026-06-11):
https://google-deepmind.github.io/alphaevolve_repository_of_problems/problems/60.html
(rendered from `problems/60.html` in github.com/google-deepmind/alphaevolve_repository_of_problems).

### Conventions, pinned

- **Grid indexing.** The paper writes [n]^3 = {1,...,n}^3 (1-based); the official notebook
  (`data/no_5_on_a_sphere.ipynb`) uses coordinates in {0,...,n-1}^3. Equivalent: the
  cospherical/coplanar condition is translation-invariant. We standardize on {0,...,n-1}^3.
- **Forbidden configurations.** 5 distinct points p_i=(x_i,y_i,z_i) are forbidden iff
  det M = 0 where M is the 5x5 matrix with rows [x_i, y_i, z_i, x_i^2+y_i^2+z_i^2, 1].
  det = 0 covers BOTH cospherical (5 on a common sphere) and coplanar (5 on a common
  plane) cases; planes are "spheres of infinite radius" here. Official prompt (notebook
  cell 2): "This also forbids the degenerate case where 5 points lie on the same plane."
- **Derived hard facts** (proved by lifted-rank argument; verified computationally):
  - 4 collinear points have lifted affine rank 2, so they + ANY 5th point give det 0.
    A valid set with >= 5 points has at most 3 points per line.
  - 4 cocircular points likewise block EVERY 5th point (pencil of spheres through a
    circle covers space). At most 3 points per circle.
  - Consequence for incremental search code: a rank-degenerate quadruple (4 cocircular /
    collinear) must block ALL candidate cells. Naive "sphere-center hashing" that assigns
    each quadruple a unique sphere is WRONG for these quadruples. The plain
    all-5-subsets determinant certificate is unaffected and complete (Codex confirmed).
- **Score.** |S|. A new record for n=13 is any valid S in {0,...,12}^3 with |S| >= 34.

---

## 2. Current record and provenance

Published lower bounds (no upper bounds beyond 4n are published for small n):

| n | PatternBoost (arXiv:2411.00566) | AlphaEvolve (arXiv:2511.02864v3, Problem 6.60) |
|---|---|---|
| 3..6 | 8, 11, 14, 18 | — |
| 7 | 20 | **21** |
| 8 | 22 | **23** |
| 9 | 25 | **26** |
| 10 | 27 | **28** |
| 11 | — | **31** |
| 12 | — | **33** |
| 13 | — | — (nothing published; inherited C(13) >= C(12) >= 33) |

Paper quote (verbatim, p. 63-64): "Using the search mode of AlphaEvolve, we were able to
obtain the better lower bounds C_6.60(7) >= 21, C_6.60(8) >= 23, C_6.60(9) >= 26, and
C_6.60(10) >= 28 ... We also got the new lower bounds C_6.60(11) >= 31 and
C_6.60(12) >= 33. Interestingly, the setup in [56] for this problem was optimized for a
GPU, whereas here we only used CPU evaluators which were significantly slower. The gain
appears to come from AlphaEvolve exploring thousands of different exotic local search
methods until it found one that happened to work well for the problem."

Admitted harness bug (notebook cell 3, verbatim): "Note: our experiment for this problem
contained a mistake. Due to us misplacing the # EVOLVE-BLOCK-START line, AlphaEvolve
didn't actually have access to the previous best constructions found, so it had to start
its search from scratch every time."

All six record point sets are archived in `data/records.json` (extracted verbatim from the
official notebook) and re-verified with exact integer arithmetic on 2026-06-11: all valid;
min |det| over all 5-subsets is 2 for the n=12 set (the set sits at the very edge of
degeneracy). Independent re-verification by Codex (different implementation): same result.

### Asymptotics (context; touches no small n)

- Thiele 1995: c*sqrt(n) <= C(n) <= 4n. The upper bound 4n is the trivial
  "<= 4 points per plane z=const" count; for n=13 this gives C(13) <= 52.
- Suk-White + arXiv:2412.02866 (note): C(n) >= n^{3/4 - o(1)}.
- Dong-Xu arXiv:2506.18113 (June 2025) and arXiv:2511.03526 (Nov 2025, rational normal
  curves): C(n) >= n - o(n); every hyperplane meets the construction in <= 3 points and
  every sphere in <= 4 points. Asymptotic only — explicitly no small-n values.
- Records sit at C(n)/n ~ 2.75-3.0 for n=7..12, i.e. far above n and far below 4n.
  True asymptotic constant in [1,4] is open.

### Openness evidence (dated 2026-06-11)

- Official problem page + notebook: no n=13 entry, n=12 still 33.
- arXiv searches (AlphaEvolve citing literature: ThetaEvolve 2511.23473, GigaEvo
  2511.17592, OpenEvolve ecosystem): none touch Problem 60.
- Dong-Xu / 2412.02866 / 2509.06935 / 2511.03526: asymptotic only.
- Codex independent web kill-check (2026-06-12 UTC): "no public C(13) lower bound and no
  C(12) >= 34 claim in the official paper/repo, arXiv/web search, GitHub issues/PRs,
  MathOverflow, or EinsteinArena-style searches"; repo has one open unrelated issue, one
  CI-only merged PR.

---

## 3. Exact-arithmetic evaluator (certificate spec)

Candidate certificate = JSON list of m distinct integer triples in {0,...,12}^3 (n=13).
Claim "C(13) >= m" is accepted iff:

1. All coordinates are integers in [0,12]; all m triples distinct; m >= 34.
2. For EVERY 5-subset {p1,...,p5} (C(m,5) of them; 278,256 for m=34):
   lift each point to L(p) = (x, y, z, x^2+y^2+z^2);
   form the 4x4 integer matrix with rows L(p_i) - L(p_1), i = 2..5;
   its determinant, computed by exact integer cofactor expansion, must be nonzero.
   (Equivalent to the 5x5 determinant with the all-ones column, by column elimination.)

Overflow analysis: coordinate diffs <= 12, lifted diffs <= 432 in absolute value; the 4x4
determinant is a sum of 24 terms each <= 12^3 * 432, so |det| <= 24 * 12^3 * 432 =
17,915,904 < 2^25. int64 (or even int32) exact; no rationals needed. Runtime ~1.4 s in
pure Python, milliseconds in C/Rust. The reference float verifier in the official notebook
(np.linalg.det + np.isclose) is NOT a certificate; ours is.

For n=14/15 first-bound claims the same spec applies with the obvious range change
(bounds: diffs <= 14, lifted diffs <= 588, |det| <= 24 * 14^3 * 588 < 2^36 — still int64-safe).

Incremental search evaluation (not part of the certificate): point p is addable to S iff
for every 4-subset Q of S, det of rows L(q)-L(p) is nonzero; equivalently c_Q . (L(p),1)
!= 0 where c_Q in Z^5 is the cofactor vector of Q — one dot product per quadruple,
~40,920 int ops per (cell, set) query at |S|=33.

---

## 4. Structure of the record object (probed 2026-06-11, code in `data/`)

The published 33-point set in {0,...,11}^3:

- **Not structured.** No symmetry, irregular per-axis layer profiles (counts 1..4 per
  layer, max 4 = saturation), 17/33 points on the cube surface, all 8 parity classes
  used (3-5 points each), 85 coplanar quadruples (legal), 0 collinear triples.
  Consistent with the paper's own account: residue of a generic evolved local search.
- **Maximal and sticky in the 13-cube.** Scanned all 2711 candidate cells in
  {-1,...,12}^3 (covers all 8 translates of the 12-cube inside a 13-cube): ZERO addable
  cells. Only 4 cells become addable after deleting one specific point, and their rescue
  sets ({1,7,15,28}, {6}, {4}, {24,32} by point index) are pairwise disjoint — so no
  1-out-2-in move reaches 34 from this exact set. (Independently reproduced by Codex.)
- **Tightness.** min |det| = 2 over all 237,336 5-subsets; 206 subsets have |det| <= 10.
  Records live at the degeneracy edge: near-misses everywhere.
- **Growth trend.** 21, 23, 26, 28, 31, 33 for n=7..12: diffs +2,+3,+2,+3,+2. Next
  diff +3 would give C(13) >= 36; conservative claim target is 34-35.
- **Pilot calibration (this machine).** Naive random greedy on [13]^3: 27-29 in ~25 s
  per run (5 seeds). The 5-6 point gap to record grade is the insight/search layer.
  The published recipe reached 33 on [12]^3 on modest CPU with a harness that restarted
  from scratch every generation; our campaign brings seeded populations + exact repair
  moves + ~1e5-1e6x compute.

Why beatable: the record is generic-search residue produced under an admitted harness
bug, with zero community follow-up in 6+ months, on a problem whose evaluation is exact
integer arithmetic in milliseconds. Why possibly not: the 33-set's total saturation in
the 13-cube shows record-grade sets are deeply locally optimal; 34-sets may be rare.

---

## 5. Attack angles (seed list for the swarm)

1. **Exact blocker-cofactor repair search (Codex angle).** For a set S, precompute the
   cofactor vector c_Q in Z^5 of every 4-subset Q; candidate p is blocked iff
   c_Q . (L(p),1) = 0. Bitset per cell of blocking quadruples turns "what deletion set
   rescues p?" into hitting-set queries. Systematically search r-out/(r+1)-in moves
   (r = 2,3) over a DIVERSE population of inequivalent 33-seeds (and 32-seeds), via
   exact combinatorics / ILP / SAT, not stochastic annealing. We already know r=1 fails
   for the published seed; r>=2 is unexplored territory.
2. **Finite-field cap assault over F_13 (Codex angle).** If all 5x5 lifted determinants
   are nonzero mod 13, the integer determinants are nonzero a fortiori. Search for
   34-point "caps" of the rank-5 lifted matroid on F_13^3 (2197 points) using the much
   larger symmetry group (translations of F_13^3, orthogonal/conformal maps mod 13) for
   canonicalization and orbit-restricted search; lift winners directly to {0,...,12}^3.
   Stronger condition than needed — use as a structured seed generator, not the only path.
3. **Central-inversion symmetric search.** n=13 has a true center c=(6,6,6). Restrict to
   sets invariant under p -> 2c - p (17 orbit-pairs needed for 34 points; center cell
   itself is excluded since center + two orbit-pairs is automatically 5-coplanar). Every
   two orbit-pairs form a parallelogram (coplanar 4-set, legal; cocircular iff a
   rectangle — forbid rectangles). Halves the search dimension and densely pre-saturates
   4-point planes, which is exactly how record sets look. Cheap to test; also applies
   with half-integral center to n=14.
4. **Curve-template unions (Dong-Xu / rational-normal-curve transfer).** arXiv:2511.03526
   constructs sets where planes carry <= 3 and spheres <= 4 points using rational normal
   curves. A single curve gives only ~n points (record needs ~2.75n), so: take unions of
   2-3 algebraically-related curve segments (translates/reflections/modular twists) whose
   cross-degeneracies are controlled, then augment with exact repair (angle 1). Also mine
   the explicit D-X polynomial families for n=13,14,15 as high-quality partial seeds.
5. **Layer-profile constructive assembly.** Fix a per-axis layer profile (13 layer counts
   in {0..4} summing to 34; records favor 3s and 4s) and assemble layer-by-layer with
   beam search / DP, where each layer's 3-4 points are chosen from precomputed
   non-cocircular patterns and cross-layer blocker counts are maintained incrementally
   via cofactor dot products. Converts the global search into structured sequencing.
6. **Reproduce-and-fix the published recipe at scale (credible baseline).** The evolved
   n=12 ILS (ruin-and-rebuild over sorted reinsertion keys; full code in the official
   notebook) is public. Fix the admitted bug (seed with previous bests), port the
   incremental evaluator to C/Rust (~1e3x faster than their numba), run a 32-thread
   population with canonical-form dedup for days. Fallback ladder: C(12) >= 34 sideways,
   C(13) >= 34, first nontrivial C(14)/C(15) bounds (>33 each) — each rung is citable.

---

## 6. Risks

- **Intrinsic hardness (main risk).** C(13) = 33 is conceivable, or 34-sets exist but are
  too rare for our compute. Mitigation: fallback ladder (n=14/15 first bounds are easier:
  more room per layer), sideways C(12)>=34 attempt, and the n=12->13 growth record
  (+2/+3 alternation, total saturation of the 33-set only shows THIS basin is dead).
- **Scoop risk.** DeepMind or a follow-up system (PatternBoost team, evolve-clones) could
  publish n=13 values at any time; the problem is publicly listed as a record problem.
  Mitigation: re-run kill-check immediately before claiming (Framework section 1.6).
- **Degenerate-quadruple bug class.** Any search code that maps quadruples to spheres by
  center/radius will mishandle rank-degenerate quadruples; all 5-subset certificates are
  immune. Mitigation: dual independent checkers + mutation tests at Gate 4.
- **Novelty perception.** A +1 on a small-n grid record is citable (repository invites
  exactly this) but modest; attach the insight layer (symmetric or finite-field
  construction) to raise the contribution above "ran search longer".
- **Float traps.** Official notebook verifier is float-based; never use it as the
  certificate. Our integer spec is overflow-safe (max |det| < 2^25 for n=13).

## 7. Codex foil verdict (2026-06-12, thread 019eb971-cd06-7d03-ab15-ea480fd0f055)

Verbatim core: "I could not kill it. As of June 12, 2026, I found no public C(13) lower
bound and no C(12) >= 34 claim in the official paper/repo, arXiv/web search, GitHub
issues/PRs, MathOverflow, or EinsteinArena-style searches. ... No convention trap found.
... The rank-degenerate quadruple subtlety does not invalidate the certificate. ...
Attack-worthiness: 0.82. Main objection: the target is alive, but the known 33-point set
is an isolated saturated basin, so a campaign that merely polishes that seed is likely to
waste most of its compute."

## 8. Artifacts in this directory

- `data/no_5_on_a_sphere.ipynb` — official notebook (downloaded 2026-06-11).
- `data/records.json` — all six published record sets, verbatim coordinates.
- `data/s12_in_13cube_scan.json` — addable/rescuable-cell scan of the 33-set in the 13-cube.
- `data/paper.pdf` — arXiv:2511.02864v3.
