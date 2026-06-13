# C(13) >= 36 for the "no 5 on a sphere" grid problem (AlphaEvolve Problem 60)

Gate-5 write-up, 2026-06-12. Bundle:
`C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid\`

Prior record: 33 (inherited from C(12) >= 33, AlphaEvolve, Nov 2025; nothing was
published for n = 13). This work: **36**, by an explicit centrally symmetric
36-point set in {0,...,12}^3, exact-integer certified.

---

## Abstract (~130 words)

For the "no 5 on a sphere" problem (AlphaEvolve repository of problems, #60;
arXiv:2511.02864, Problem 6.60) — find the largest subset of the n x n x n grid
with no 5 points on a common sphere or plane — the best published lower bound
relevant to n = 13 was C(13) >= C(12) >= 33 (AlphaEvolve, November 2025). We
raise this to **C(13) >= 36** with an explicit 36-point subset of {0,...,12}^3
that is invariant under the central inversion p -> (12,12,12) - p: 18
point-pairs with pairwise distinct distances from the cube center. It was found
in 841 seconds on 8 CPU threads by an exact-arithmetic iterated local search
restricted to centrally symmetric configurations — symmetry halves the search
dimension and pre-saturates the 4-points-per-plane budget that record sets
exhaust. Verification is a one-minute exact-integer determinant check over all
376,992 5-subsets; three independent checkers (two Python, one Rust) plus a
hostile-referee recheck by a different model family all accept. En route, four
independent search pilots produced thousands of distinct 34- and 35-point sets,
showing the published 33-point regime was far from the truth for n = 13.

---

## Result (claim-standard form, FRAMEWORK.md section 9)

> **Result.** For the problem frozen in `PROBLEM.md` — verbatim from the
> official problem page (fetched live 2026-06-12, see Provenance):
> *"For n a natural number, let C(n) denote the size of the largest subset of
> [n]^3 = {1,...,n}^3 such that no 5 points lie on a sphere or a plane. Obtain
> upper and lower bounds for C(n) that are as strong as possible."* —
> we establish the new lower bound **C(13) >= 36**. The certificate is an
> explicit 36-point subset of {0,...,12}^3 (equivalently {1,...,13}^3 after
> adding 1 to every coordinate; the no-5-cospherical/coplanar condition is
> translation-invariant). Validity means: every one of the C(36,5) = 376,992
> 5-subsets has nonzero determinant of the 5x5 integer matrix with rows
> [x_i, y_i, z_i, x_i^2+y_i^2+z_i^2, 1] — the standard lifted condition that
> simultaneously forbids 5 cospherical and 5 coplanar points (used by both
> prior-art papers; reproduced against all six official record sets, see
> Convention anchor).
>
> **Status before this work.** The AlphaEvolve paper (arXiv:2511.02864v3,
> 2025-12-22, Problem 6.60) and the official repository list lower bounds only
> up to n = 12: "C_6.60(7) >= 21, ..., C_6.60(11) >= 31 and C_6.60(12) >= 33."
> No bound for n = 13 was published anywhere we could find (searches dated
> 2026-06-11 and again 2026-06-12, below); the inherited baseline is
> C(13) >= C(12) >= 33. The official `status.json` (fetched 2026-06-12) still
> lists problem 60 in its `world_record` category, i.e. the repository's own
> n <= 12 sets stand as the world records; the repo's last commit is
> 2026-04-15 and the problem-60 notebook is untouched since 2025-11-05.
>
> **Artifact.** `certificates/record36_centralsym.json` — a JSON list of 36
> integer triples (inline below), sha256
> `333d36ece36e3d845cd2f5bb26e5460f78d881c00418c92cae8bd5215ab0629a`,
> byte-identical to the discovering run's output
> `runs/central-symmetric/main-run/FOUND36_sym.json`. Supporting artifacts:
> 7 distinct 34-point and 7 distinct 35-point certified sets in
> `certificates/` (independent search pilots), plus pooled-set logs in `runs/`.
>
> **Verification (all fresh on 2026-06-12, log: `verification/gate45_report.json`).**
> Route A: `code/check_cert.py` (pure-integer Python, ~30-line core, written by
> the Gate-2 tooling agent; cofactor expansion of the differenced 4x4).
> Route B: `verification/gate45_fresh_verify.py::route_b` (written from scratch
> by the Gate-4/5 agent: Bareiss fraction-free elimination on the full 5x5).
> Route C: `code/core` Rust crate `no5core` (independent implementation,
> AVX-512/scalar paths, 28 unit tests incl. 5 rank-degenerate-quadruple traps —
> re-run fresh 2026-06-12, 28/28 pass).
> All three routes accept all 18 banked certificate files (15 distinct sets:
> 7 x 34, 7 x 35, 1 x 36) and all six official record sets (n = 7..12), and all
> three reject the known-bad 34-set and all 7 targeted mutations of the 36-set
> (duplicate point, coordinate 13, negative coordinate, float coordinate,
> append center cell, replace point by center, append a coplanar grid cell).
> Codex (GPT-5.5, hostile-referee framing, thread
> `019eba69-abb7-7000-b5d5-3b9bb77b1cbc`) wrote its own checker from scratch
> (`verification/codex_hostile_no5sphere_check.py`, strict JSON typing,
> Bareiss elimination; Codex additionally cross-checked in-session with an
> independent 5x5 permutation-expansion formula), confirmed 376,992 nonzero
> determinants, min |det| = 2, central symmetry with 18 pairs and 0 fixed
> points, and returned **"SURVIVES"** after its own convention attack and
> web priority search.
>
> **Openness re-check.** 2026-06-12, this session: 16 documented searches
> (arXiv API + listings, official repo page/status.json/commits/issues/PRs,
> EinsteinArena site + SOTA repo, GitHub global code search, OpenReview,
> general web; plus Codex's independent sweep incl. X/Twitter and news). No
> public claim of C(13) >= 34 — or even C(12) >= 34 — found. Details below.
>
> **What this does not show.** See final section.

---

## Exact statement and provenance

* **Authoritative source (live).** Official problem page, fetched 2026-06-12:
  `https://google-deepmind.github.io/alphaevolve_repository_of_problems/problems/60.html`
  (raw HTML archived at `verification/provenance/problem60_20260612.html`,
  sha256 `0c77502c6361596d1866f8b4c8cc839919ce19eee9f62e62e9fd137e0e76448e`).
  The page's embedded data object (HTML lines 212-219) reads, verbatim:

  > title: "60. The no 5 on a sphere problem"
  > statement: "For $n$ a natural number, let $C(n)$ denote the size of the
  > largest subset of $[n]^3 = \{1,\dots,n\}^3$ such that no 5 points lie on a
  > sphere or a plane. Obtain upper and lower bounds for $C(n)$ that are as
  > strong as possible."

  The Comments block is empty; the page links the official notebook
  (`experiments/no_5_on_a_sphere/no_5_on_a_sphere.ipynb`) and the paper
  arXiv:2511.02864. (The page's link text says "Section 6.40"; the paper
  itself, v3 of 2025-12-22, numbers it **Problem 6.60**, Section 6, p. 63 —
  a stale link-text quirk in the repo, noted to preempt confusion.)
* **Paper statement** (arXiv:2511.02864v3, Problem 6.60, frozen in
  `PROBLEM.md` from `data/paper.pdf`): identical wording.
* **`status.json` (live).** Fetched 2026-06-12 from the repo
  (`verification/provenance/status_20260612.json`, sha256
  `4a2aa43d82d45086caf59355d7cd07628931f66abf19e44899278c7b9096bf9a`);
  problem 60 appears in the `world_record` array. No n = 13 data anywhere in
  the repo.
* **Conventions, pinned** (full discussion in `PROBLEM.md` section 1): grid
  {0,...,n-1}^3 here vs the paper's 1-based [n]^3 — equivalent by translation
  invariance of the determinant condition. "No 5 on a sphere or a plane" =
  for every 5 points, det of the 5x5 lifted matrix [x, y, z, x^2+y^2+z^2, 1]
  is nonzero (planes are spheres of infinite radius; the official notebook
  prompt states the plane case explicitly). Degenerate sub-configurations
  (4 collinear or 4 cocircular points) make EVERY fifth point forbidden; the
  all-5-subsets determinant certificate handles this automatically.
* **Convention anchor (Gate 2, re-run fresh 2026-06-12).** The same checkers
  that accept our 36-set accept **all six official AlphaEvolve record sets**
  (n = 7..12, sizes 21/23/26/28/31/33, extracted verbatim from the official
  notebook into `data/records.json`) and reject a known-bad 34-point set. So
  our evaluator and theirs agree on every published instance — the comparison
  33 -> 36 is under the very convention that produced the 33.

## The certificate

`certificates/record36_centralsym.json` — 36 points in {0,...,12}^3
(add 1 to each coordinate for the paper's [13]^3):

```json
[[0,1,12],[0,3,7],[0,9,10],[0,12,0],[1,4,1],[1,6,4],[1,12,11],[2,6,12],
 [2,8,1],[3,1,10],[3,5,7],[3,7,10],[4,3,5],[4,8,3],[5,0,0],[5,2,2],
 [5,11,3],[6,0,4],[6,12,8],[7,1,9],[7,10,10],[7,12,12],[8,4,9],[8,9,7],
 [9,5,2],[9,7,5],[9,11,2],[10,4,11],[10,6,0],[11,0,1],[11,6,8],[11,8,11],
 [12,0,12],[12,3,2],[12,9,5],[12,11,0]]
```

**Central symmetry (verified explicitly, fresh 2026-06-12).** The set is
invariant under the central inversion sigma(p) = (12,12,12) - p of the
13-cube: sigma maps the set to itself, with **18 orbit pairs and zero fixed
points** (the unique fixed cell (6,6,6) is not in the set — it cannot be: the
center plus any two orbit pairs is automatically 5-coplanar). The 18 pairs
have pairwise distinct squared distances from the center — shells
4|p - c|^2 = 44, 56, 68, 104, 116, 132, 140, 160, 180, 184, 200, 208, 216,
244, 292, 344, 388, 432 — as the search enforces: two orbit pairs on a common
central shell form a rectangle, i.e. a cocircular quadruple, which forbids
every fifth point.

**Structure.** Per-axis layer profiles (counts per coordinate value 0..12),
palindromic by symmetry:
x: [4,3,2,3,2,3,2,3,2,3,2,3,4]; y: [4,3,1,3,3,2,4,2,3,3,1,3,4];
z: [4,3,4,2,2,3,0,3,2,2,4,3,4]. Maximum 4 points per axis-aligned plane (the
trivial bound that gives C(13) <= 52). 16 of 36 points lie on the cube
surface; parity-class profile [4,4,4,4,4,4,6,6].

**Tightness.** Over all 376,992 5-subsets: min |det| = 2, and 200 subsets
have |det| <= 10 (max |det| = 198,750). Like every record set in this
problem, the object sits at the very edge of degeneracy.

**Saturation.** The Rust incremental engine, cross-validated against a
brute-force recount of the full blocked grid (`bruteforce_grid_match=true`),
reports **0 addable cells**: no 37th point of {0,...,12}^3 extends this set.

## Record history and timing (all times local, Ryzen 9 9950X3D, 16C/32T)

| bound | when | by | evidence |
|---|---|---|---|
| C(12) >= 33 (prior art) | Nov 2025 | AlphaEvolve (CPU evaluators, admitted harness bug) | arXiv:2511.02864, official notebook |
| C(13) >= 34 | 2026-06-11 ~23:24 | two pilots independently, within a minute: central-symmetric smoke run (**4 s**, 2 threads) and baseline-ILS smoke run | `certificates/candidate34_*.txt`, `runs/*/smoke/` |
| C(13) >= 35 | 2026-06-11 23:35-23:39 | baseline-ILS main run (t = 538 s; event log) and blocker-repair pilot, independently | `runs/baseline-ils/main/STATUS.json`, `certificates/*35*` |
| **C(13) >= 36** | **2026-06-12 00:29:19** | central-symmetric main run: `symsearch --target 36 --stall 800 --extmin 14 --seed 20260612`, 8 threads, **840.9 s** elapsed, 611,969 ILS iterations, 627 restarts | `runs/central-symmetric/main-run/{FOUND36_sym.json,STATUS.json}` |

Roughly three hours elapsed between freezing the Gate-0 dossier and the 36.
Two further pilots also reached 34 the same night (blocker-repair at ~23:36;
finite-field-F13 arc-seeded ILS, 71 distinct 34-sets). Abundance at the new
levels is extreme — distinct certified sets logged across pilots:

| pilot | distinct 34s | distinct 35s | 36 |
|---|---|---|---|
| baseline-ILS (22-min snapshot; 182 of the 34s from the fixed-bug arm) | 198 | 1 | — |
| blocker-repair (3 runs) | 4068 + 1655 + 1031 | 20 + 23 + 43 | — |
| central-symmetric (symmetric sets only, 14 min) | 4126 | n/a (odd size needs an asymmetric point) | **1** |
| finite-field-F13 (arc-seeded) | 71 | — | — |

(Each pooled set was exact-verified in-process before logging; the banked
`certificates/` files — 7 distinct 34s, 7 distinct 35s, the 36 — were each
re-verified by all three routes on 2026-06-12.)

By contrast, the published 33-point n = 12 record is **totally saturated** in
the 13-cube: re-verified fresh 2026-06-12, the Rust engine reports **0 addable
cells for all 8 translates** of the 12-cube inside the 13-cube
(shift000...shift111 all 0; shift000 cross-checked brute-force), covering the
dossier's full 2711-cell {-1,...,12}^3 scan. The published record was a dead
local optimum; the 34/35/36 region was simply unexplored.

## Method sketch: central-inversion symmetric search (attack angle 3)

Full run log: `runs/central-symmetric/README.md`; search binary
`symsearch.rs` (snapshot in `runs/central-symmetric/crate/`, mirrored at
`code/core/src/bin/symsearch.rs`).

* **Idea.** n = 13 has a true center c = (6,6,6). Search only sets invariant
  under sigma(p) = 2c - p, i.e. unions of orbit pairs {p, sigma(p)}. This
  halves the search dimension (36 points = 18 pair choices), and every two
  orbit pairs form a parallelogram — a coplanar (legal) quadruple — densely
  pre-paying the 4-points-per-plane budget that record-grade sets are
  empirically built from. The grid is the exact-integer lift; no floats
  anywhere.
* **Exact pair-addability** for candidate pair (p, q = sigma(p)) against a
  symmetric set S, three exhaustive layers: (1) both cells unblocked in the
  incrementally maintained cofactor grid — covers every zero 5-subset with
  >= 4 old points, including all rank-degenerate old quadruples; (2)
  cofactor_vec(x, y, p, q) != 0 over all member 2-subsets {x,y} — covers
  rank-degenerate quadruples containing both new points (central-line
  collinearity, off-center cocircularity); (3) det5({x,y,z,p}, q) != 0 over
  all member 3-subsets — covers every zero 5-subset containing both new
  points. An exact shell filter (equal central shells <=> rectangle <=>
  cocircular) prunes pairs early; `is_valid_set()` is asserted after every
  pair add, and a full degenerate-quadruple sweep runs every 512 iterations.
* **Search loop.** Greedy randomized fill over pair-orbits; ruin-and-rebuild
  ILS (remove r in {1,2,3} random pairs, tabu rebuild, accept-if-not-worse,
  restart after 800 non-improving iterations). At rich local optima a greedy
  *asymmetric* extension is measured (path to odd sizes) and reverted. The
  36 = 18 symmetric pairs appeared on thread 3 of 8 after ~14 minutes.
* **Why it wins.** The asymmetric pilots plateaued hard at 35 (blocker-repair
  logged 510 dead-ends at 34 and 18 at 35 in its first hour; 35s appeared at
  a rate of ~1 per 200+ distinct 34s). The symmetric subspace is exponentially
  smaller and structurally pre-aligned with how dense sets must look; within
  it, 34s are mass-produced (4126 in 14 minutes) and one run pushed straight
  through to 18 pairs.
* **Supporting pilots** (independent code paths, all exact-integer): faithful
  port of the published evolved n = 12 ILS recipe with the paper's admitted
  harness bug fixed (`code/core/src/ils.rs`); exact blocker-cofactor repair
  search over hitting sets (`repair.rs`); finite-field F_13 arc mining
  (Ball's theorem caps mod-13 arcs at 14 points, so mod-13 structure serves
  as seed diversity, not as a direct construction — `f13.rs`).

## Verification detail

All of the following re-run fresh on 2026-06-12 by the Gate-4/5 agent (who
wrote none of the search code); console log in this bundle's
`verification/gate45_report.json`:

1. **Three routes x 18 certificate files** (15 distinct sets): Route A
   (`code/check_cert.py`, Python, int-only, distinctness + range + all-5-subset
   determinant), Route B (fresh Bareiss-elimination checker inside
   `verification/gate45_fresh_verify.py`, written for this gate), Route C
   (Rust `no5core check`, independent codebase). 18/18 x 3 PASS; per-file
   sha256 recorded in the report.
2. **Central symmetry of the 36-set**: sigma-invariance, 18 pairs, 0 fixed
   points, center cell absent, 18 pairwise-distinct shells. PASS.
3. **Mutation testing**: 7 targeted corruptions of the 36-set (duplicate
   point; coordinate 13; coordinate -1; float 5.0; append (6,6,6); replace a
   point by (6,6,6); append the in-range, non-member coplanar cell (1,8,0),
   which completes a zero 5-subset with the orbit pairs {(0,12,0),(12,0,12)}
   and {(6,0,4),(6,12,8)}). Every route rejects every corruption (the Rust
   parser is integer-only by design, so the float case applies to A/B). PASS.
4. **Saturation of the 36-set**: 0 addable cells, incremental grid ==
   brute-force det5 recount. PASS.
5. **Convention anchor**: official records n = 7..12 accepted by all three
   routes; known-bad 34 rejected by all three; 33-set saturation re-confirmed
   for all 8 translates. PASS.
6. **Rust unit tests**: 28/28 fresh (19 lib + 4 repair + 5 symsearch),
   including the 5 degenerate-quadruple trap tests and incremental ==
   brute-force cross-validation under production compile flags.
7. **Hostile referee (different model family).** Codex, GPT-5.5, full shell +
   network, instructed to kill the claim. Verbatim core of the verdict
   (thread `019eba69-abb7-7000-b5d5-3b9bb77b1cbc`): *"SURVIVES. ... 5-subsets
   tested: 376,992; Zero lifted determinants: 0; min |det| = 2; Central
   symmetry: yes ... 18 reflection pairs, 0 fixed points. Convention attack
   did not kill it. ... Priority check: I found no public claim of
   C(13) >= 34 or C(12) >= 34 through arXiv, official repo/status/issues/PRs,
   GitHub code search, OpenReview, EinsteinArena, Axiom/Axplorer, blogs/news,
   or X/Twitter."* Its from-scratch checker is banked at
   `verification/codex_hostile_no5sphere_check.py` (strict JSON typing,
   Bareiss determinants); Codex reported an additional in-session recheck via
   an independent 5x5 permutation-expansion formula.
8. **Chain of custody**: the banked certificate is byte-identical (sha256
   `333d36ec...`) to the discovering run's `FOUND36_sym.json` and
   `best_sym.json`; the run verified the set in-process at discovery time
   (brute-force `find_zero_5subset` assertion) before writing.

Earlier, independent verification during the campaign (2026-06-11/12): each
pilot's first 34/35 sets were checked by Python + Rust + an exact-rational
Gaussian-elimination route and a separate Codex adversarial thread
(`019eb9ef-f590-71b3-9b90-fb73475e9558`,
`runs/central-symmetric/adversarial_check_no5.py`).

## How to verify (under a minute; Python 3 only)

```
cd problems/p1-records/no-5-on-a-sphere-grid
python code/check_cert.py certificates/record36_centralsym.json 13
# expect: VALID m=36 n=13, exit code 0   (~2 s)
```

Full battery (three routes on everything, symmetry, mutations, saturation,
anchor; needs the Rust binary `code/core/target/release/no5core.exe`,
`cargo build --release` if absent; a few minutes):

```
python verification/gate45_fresh_verify.py
# expect: GATE-4/5 FRESH VERIFICATION PASSED, exit code 0
python verification/codex_hostile_no5sphere_check.py
# Codex's independent checker; expect JSON with "tested_5_subsets": 376992,
# "zero_determinant_count_first_10": 0, "min_abs_det": 2, "central_symmetry": true
```

A skeptic should re-implement the 30-line condition independently: lift each
point (x,y,z) to (x, y, z, x^2+y^2+z^2, 1); for all 376,992 5-subsets the 5x5
determinant must be nonzero. Max |det| < 2^25 here, so any integer arithmetic
is exact; never use the float verifier from the official notebook.

## Final kill-check (Gate-5, dated 2026-06-12)

Searches run this session, after verification, looking for ANY public claim of
C(13) >= 34 (or C(12) >= 34) for this problem:

1. Web: `"no 5 on a sphere" grid problem record 2026 AlphaEvolve` — paper,
   repo, journalism, OpenEvolve ecosystem; no n = 13. **Nothing.**
2. Web: `AlphaEvolve problem 60 "no 5 points" sphere plane lower bound n=13`
   — paper + PatternBoost + Tao's blog post; explicit confirmation the
   published list stops at C(12) >= 33. **Nothing.**
3. Web: `"no-five-in-a-sphere" OR "no 5 on a sphere" n=13 OR "C(13)" 34
   points grid` — PatternBoost (records to n = 10), Tammes-problem noise.
   **Nothing.**
4. Web: `einsteinarena no 5 on a sphere AlphaEvolve record` — located the
   EinsteinArena venue (AI-vs-records leaderboard), checked next. **Nothing
   direct.**
5. `einsteinarena.com` (live fetch): 17 listed problems (circle packing,
   kissing numbers, Tammes, Thomson, Heilbronn, autocorrelation, ...) — this
   problem is **not on the platform**.
6. `github.com/togethercomputer/EinsteinArena-new-SOTA` (live fetch, last
   update 2026-04-01): 14 problem directories, none is this problem.
   **Nothing.**
7. Web: `arXiv 2026 "no 5 on a sphere" / "cospherical" grid lower bound` —
   only Dong-Xu arXiv:2506.18113 (asymptotic n - o(n), explicitly no small-n
   values). **Nothing.**
8. Web: `"2511.02864" problem 6.60 2026` — no follow-up improving 6.60.
   **Nothing.**
9. Web: `PatternBoost "no 5 on a sphere" 2026 13x13x13` — nothing newer than
   the two known papers. **Nothing.**
10. Web: `OpenEvolve OR ThetaEvolve OR GigaEvo "no_5_on_a_sphere"` — the
    evolve-clone ecosystem does not report this problem. **Nothing.**
11. arXiv API (`all:"no 5 on a sphere" OR all:"cospherical"`, 15 newest):
    nothing after 2506.18113 (June 2025) that is on-topic. **Nothing.**
12. arXiv math.CO recent listing (June 2026 scan): no related submissions.
    **Nothing.**
13. GitHub official repo, live API: last commit 2026-04-15 (unrelated
    problems); the problem-60 notebook untouched since the initial commit
    2025-11-05; `status.json` still lists 60 under `world_record`; all 3
    issues/PRs ever opened are unrelated (archived under
    `verification/provenance/`). **Nothing.**
14. GitHub global code search (`gh search code no_5_on_a_sphere`): only the
    official repo, a problem-definition library (vicruz99/autoresearch-problems,
    "Known best: open", evaluator only) and an RL-environment mirror
    (bertmiller/auto-rl, statements only) — both inspected, neither claims any
    value. **Nothing.**
15. OpenReview API (`no 5 on a sphere grid`): only grid-computing noise.
    **Nothing.**
16. Web: `"36 points" OR "35 points" OR "34 points" "13" grid no five points
    sphere plane record June 2026` — sports noise. **Nothing.**

Plus Codex's independent hostile sweep (item 7 of Verification detail; arXiv,
official repo, GitHub code search, OpenReview, EinsteinArena, Axiom/Axplorer,
blogs/news, X/Twitter): *"no public claim of C(13) >= 34 or C(12) >= 34"* as
of 2026-06-12. **Conclusion: the record stands as of 2026-06-12.** Residual
risk: private/unpublished runs (DeepMind or evolve-clone users) that have not
surfaced anywhere indexable; the problem page invites exactly this kind of
record-chasing, so the claim should be published promptly.

## What this does not show

* **The exact value of C(13) is unknown.** This is a lower bound only. The
  best upper bound remains the trivial 4-per-plane count C(13) <= 52. We do
  not claim 36 is optimal.
* **36 is not claimed maximal even empirically.** Our searches are heuristic;
  the 36-set admits no 37th grid point (saturation check), but other 36-sets
  or larger sets may exist in unexplored basins. No exhaustive search of any
  kind is claimed.
* **Nothing is claimed for other n.** In particular we do not claim
  C(12) >= 34 (we did not find one), nor any n = 14/15 bounds. The trivial
  monotone consequence C(n) >= 36 for all n >= 13 follows by inclusion, but
  records for n >= 14 should cite their own constructions.
* **No structural theorem.** Central symmetry was a search heuristic that
  worked; we prove nothing about symmetric sets being optimal or about the
  asymptotics of C(n) (the true growth constant in [1,4]·n remains open).
* **Priority is "no public claim found", not a guarantee.** The kill-check
  covers indexable sources as of 2026-06-12; concurrent unpublished work
  cannot be excluded.

## Artifacts index

| path | content |
|---|---|
| `PROBLEM.md` | frozen statement, provenance, prior art, conventions (Gate 0) |
| `certificates/record36_centralsym.json` | **the 36-point certificate** |
| `certificates/*34*`, `*35*` | 7 + 7 distinct supporting 34/35-point sets |
| `code/check_cert.py` | Route-A checker (Python, exact int) |
| `code/core/` | Rust crate: Route-C checker, incremental engine, searchers, 28 tests |
| `code/out/gate2_status.json` | Gate-2 validation (2026-06-11): known-case reproduction |
| `verification/gate45_fresh_verify.py` | this gate's fresh battery (Route B inside) |
| `verification/gate45_report.json` | fresh-run results, per-file sha256, 2026-06-12 |
| `verification/codex_hostile_no5sphere_check.py` | Codex's from-scratch checker |
| `verification/provenance/` | live-fetched problem page, status.json, repo commits/issues (2026-06-12) |
| `runs/central-symmetric/` | discovering pilot: README (method), STATUS, FOUND36, pools |
| `runs/{baseline-ils,blocker-repair,finite-field-f13}/` | supporting pilots' logs and pools |
| `data/` | official notebook, records.json, paper PDF |
