# CONSTRUCTION.md — synthesis of the mining + construction campaign

Date: 2026-06-12. Problem: C(n) = max |S|, S subset of {0..n-1}^3 with no 5 points on a
common sphere or plane (exact criterion: every 5-subset of lifted rows
(x, y, z, x^2+y^2+z^2, 1) has nonzero 5x5 determinant). Independent exact checker:
`C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid\code\check_cert.py`.

This file is the consolidated answer to: what structure was found, what constructions
work, what is proved vs. empirical, and what belongs in the record paper. Inputs: the
symmetry miner (`mining/symmetry/`), the algebraic miner (`mining/algebraic/`), the
literature miner (`mining/literature/LITERATURE.md`), the algebraic constructor
(`mining/construct-algebraic/`, canonical entry `CONSTRUCTION.py`), and the search
constructor (`mining/construct-search/`). All numbers below were re-verified on
2026-06-12 by re-running `mining/construct-search/harvest.py` (every certificate
re-checked by the exact independent checker) and by direct `check_cert.py` calls on the
n=11/12 run outputs.

---

## 1. Verified results table (the bottom line)

Every entry below is an explicit point set re-verified by `code/check_cert.py`
(exact integer arithmetic). The four new record certificates were additionally verified
by the in-process Rust brute force at discovery, by `harvest.py`'s re-check, and by a
from-scratch exact checker written independently by Codex (GPT-5.5) — four independent
verifiers, zero discrepancies.

| n  | deterministic CC(n) (zero search) | cone-pool ILS | SYM(n) ILS (best verified) | best known overall | status |
|----|-----------------------------------|---------------|----------------------------|--------------------|--------|
| 11 | 26                                | 26            | 30                         | 31 (published, AlphaEvolve) | published record NOT beaten |
| 12 | 26                                | 28            | 32 sym / **33 asym**       | 33 (published)     | published record TIED (independent certificate) |
| 13 | 28                                | 30            | **36**                     | **36 (ours)**      | held world record, 18 antipodal pairs |
| 14 | 30                                | 32            | **38**                     | **38 (ours)**      | NEW BOUND (beats inclusion 36); 19 pairs |
| 15 | 34                                | 36            | **40**                     | **40 (ours)**      | NEW BOUND; 20 pairs |
| 16 | 34                                | 36            | **42**                     | **42 (ours)**      | NEW BOUND (first-ever n=16 value); 21 pairs |
| 17 | 36                                | 40            | **44**                     | **44 (ours)**      | NEW BOUND; 22 pairs |
| 18 | 36                                | —             | —                          | 44 (inclusion from n=17) | CC demo only — below inclusion bound |
| 19 | 40                                | —             | —                          | 44 (inclusion)     | CC demo only |
| 20 | 42                                | —             | —                          | 44 (inclusion)     | CC demo only |
| 21 | 44                                | —             | —                          | 44 (inclusion, tied by CC) | CC demo only |

Key certificate files:
- `certificates/record36_centralsym.json` (n=13, m=36, perfectly centrally symmetric)
- `mining/construct-search/cert_n14_m38.json`, `cert_n15_m40.json`, `cert_n16_m42.json`,
  `cert_n17_m44.json` (all perfectly centrally symmetric, one antipodal pair per shell)
- `mining/construct-search/runs/main_n12/best_total.json` (n=12, m=33, asymmetric,
  verified 2026-06-12 — ties the published record; independent certificate, not a new bound)
- `mining/construct-algebraic/CC_best_n{7..21}_m*.json` + `MANIFEST.json`
  (219/219 files re-verified valid, 0 invalid)

Honesty notes on the table:
- C(n) is monotone in n (grid inclusion), so the deterministic CC values at n=18..21
  (36/40/42/44) are all at or below the inherited bound C(18..21) >= 44 from
  cert_n17_m44. They are construction demonstrations, NOT new bounds. The earlier
  constructor framing "first instance bounds" is superseded.
- Per Codex's literature check (arXiv:2511.02864v3 and a 2026 citation scan), nothing
  beyond C(12) >= 33 is published. So C(14) >= 38, C(15) >= 40, C(16) >= 42, C(17) >= 44
  beat every previously known value, including inclusion/embedding bounds. Recommended
  wording: "apparently the first public explicit certificates at these n".
- n=11/12 SYM runs targeted 32/34 and plateaued at 30/33 — the symmetric template is
  provably blind to odd-size records (a perfectly symmetric set has even size, and the
  grid center cannot be used), and appears genuinely short at n=11-12.

---

## 2. Structure found (what the miners proved)

### 2.1 The antipodal-pair calculus (the central discovery)

For sets symmetric about c = ((n-1)/2)(1,1,1), write points as c +- e/2 with e the
doubled centered coordinates. The lifted determinants then factor by symmetry class of
the 5-subset:

- **Lemma 1 ((2,2,1) class; sympy-proved + exhaustively verified on all 4098 symmetric
  34-sets, zero violations):**
  `det5(a,-a,b,-b,w) = -4 (|a|^2 - |b|^2) det3[a,b,w]`.
  Hence a valid symmetric set REQUIRES (C1) pairwise distinct pair-norms — i.e. exactly
  one antipodal pair per shell — and (C2) no three pair-directions coplanar with the
  center; conversely C1 + C2 kill the entire (2,2,1) class. This also proves no large
  valid set is a union of orbits of any group larger than {I,-I}.
- **Lemma 3 ((2,1,1,1) class; Cayley-Menger / power-of-a-point specialization, verified
  3000/3000):** `det5(a,-a,p,q,r) = 2(|a|^2 (a.u) - a.w)`, reducing this class to four
  signed sums A+B+C, A-B-C, B-A-C, C-A-B of (norm-gap) x (3x3-bracket) terms. These
  additive sign conditions are THE obstruction to a full proof (see Section 4).
- **Parity theorem (universal):** every lifted 5x5 determinant on the integer grid is
  even, so the observed min |det| = 2 across record sets is the global arithmetic floor.
- **Scaled-shell lemma (even n; Codex independently exhausted n=14,16,18, no
  counterexample):** about the half-integral center, equal scaled shells
  sum (2p_i-(n-1))^2 correspond exactly to rectangle/cocircular degeneracies, so the
  one-pair-per-shell filter is exactly lossless for BOTH parities. This is what made the
  even-n generalization of the record search valid.

### 2.2 Symmetry is capped — and records sit exactly at the cap

n-independent theorem (symmetry miner): any valid set with >= 7 points has point-symmetry
group of order <= 4; the only groups beyond {I,-I} are V4/C4 rotations. The 36-record's
stabilizer is exactly {I,-I}; all 35s are trivial. Every new record (n=14..17) is again
perfectly centrally symmetric with exactly m/2 distinct shells, one pair each. The
V4_coord quarter-dimension template reaches 36 points quickly at n=14/16 but stalls at
the 10th orbit — V4 matches -I early, never beats it.

### 2.3 Records are algebraically generic; single-prime certificates are dead

- The 36-set lies on no quadric or cubic over Q or F_13; its determinants are mod-p
  generic for every p >= 5. There is no one-prime certificate of the record.
- **Ball's theorem (JEMS 2012, prime-field MDS):** any set whose 5-subset lifted dets are
  all nonzero mod p is an arc in PG(4,p), hence has at most p+1 points. This kills the
  F_13-cap attack (max 14 points), explains the n+o(n) plateau of ALL published curve
  constructions (Dong-Xu arXiv:2506.18113, Szabo arXiv:2511.03526), and proves that any
  construction beating (1+eps)n must combine several primes or archimedean structure.
- Confirmed empirically: closed-form monomial families lift(c t^k (1,t,t^2)) mod p cap at
  4-8 pairs (~n points — exactly the published-construction scale); the isotropic cone
  x^2+y^2+z^2 == 0 mod p is provably capped (Lemma 4, caps hit exactly).

### 2.4 Records are saturated, isolated, and non-nesting — no smooth formula hits them

Zero addable cells for the 36 and 400/400 sampled symmetric 34s; zero pair-swaps for the
36; zero addable pairs for the 36 even inside the 15- and 17-cubes; six of seven 35s
saturated even in the 14-cube. Records do not nest upward or downward. Conclusion (load-
bearing): the general-n product is necessarily an ALGORITHM that emits verified
instances, not a closed formula for the exact optimum. Smooth families top out around 2n.

### 2.5 The empirical scaling law

C(n) = floor((5n+7)/2) now fits all EIGHT record-grade values n=7..14 exactly
(21, 23, 26, 28, 31, 33, 36, 38). It predicts 41/43/46 at n=15/16/17; our verified
40/42/44 are 1-2 short, consistent with compute scaling (each +1 historically costs 1-2
orders of magnitude of search). The law implies C(n)/n -> 5/2, far above the best
published asymptotic n - o(n) and below the trivial 4n cap. Treat strictly as a
conjecture; n=15..17 values may still move up.

---

## 3. The constructions

### 3.1 SYM(n) — the record-grade algorithm (the real general-n product)

One-pair-per-shell, central-inversion ILS with exact incremental cofactor arithmetic
(Rust crate `mining/construct-search/crate`, compile-time NO5_N, per-n binaries in
`mining/construct-search/bins/`). The mined laws of Section 2 are its hard constraints:
the shell filter is exactly lossless (Lemma 1 + scaled-shell lemma), so no valid
symmetric set is excluded. Produces the record at n=13 and all four new bounds n=14..17
in ~35 minutes each on idle threads. This is a uniform, parameterized procedure for every
n >= 5 (both parities) whose outputs are instantly certifiable — the honest sense in
which we have a "general-n construction".

### 3.2 CC(n; F, p, order) — the deterministic ~2n congruence construction

`mining/construct-algebraic/CONSTRUCTION.py` (engine `conelib.py`). Zero randomness,
reproducible from (n, F, p, order) alone: pool E = {e == (n-1) mod 2 coordwise,
0 < |e|_inf <= n-1, Q(e) == 0 mod p for some Q in F}, default F the coordinate-symmetric
triple-Veronese union {xy-z^2, yz-x^2, zx-y^2}, greedy in descending |e|^2 with exact
validity checks; S = {c+e/2, c-e/2}. Yields 2.0n-2.4n at every tested n in 7..21 —
roughly DOUBLE the best published general-n density. The (2,2,1) layer holds BY
CONSTRUCTION (Lemma 1 + the conic-arc Lemma 2: three distinct nonzero projective classes
on a nondegenerate conic mod p are never collinear; verified on all 125,728 pool triples
at (13,11)). Every instance additionally admits a compact two-prime certificate —
validity follows from congruences mod p (conic layer) plus one prime q ~ 10^4 for all
remaining 5-subsets (e.g. deterministic n=17/36 points: mod 13 + mod 15107;
`second_prime_cert.py`). Cone-pool ILS on the same pools adds +2..+4 and matches
unrestricted search at n=17.

### 3.3 Negative results (provably or empirically dead ends)

- Single closed-form monomial/curve families: capped at ~n points (matches published
  constructions; Ball explains why).
- Isotropic-cone template: provably capped (Lemma 4), caps attained exactly.
- Any single-prime-certified set: <= p+1 points (Ball). A 2n-point set can never have a
  one-prime certificate.
- Groups beyond {I,-I}: order <= 4 cap; V4 stalls at 36.
- Formula for exact optima: excluded by saturation/isolation/non-nesting (2.4).
- Cone-restricted search at n=13 plateaus at 30 across 11 runs vs record 36: the last
  ~0.5n-0.8n of density is algebraically generic and search-only.

---

## 4. Honest verdict

**(a) Is there a general-n theorem?** Not yet a full one. What IS proved:

- **Theorem (finite, certificate-backed):** C(n) >= 2n + 10 for 13 <= n <= 17, witnessed
  by explicit verified sets, each perfectly centrally symmetric about ((n-1)/2)(1,1,1)
  with exactly one antipodal pair per scaled shell. In particular C(13) >= 36,
  C(14) >= 38, C(15) >= 40, C(16) >= 42, C(17) >= 44, all strictly above every previously
  known value. (This is unconditional — five computer-verified certificates — but it is a
  finite statement, not a general-n theorem.)
- **Theorem (layer certificate, general n; the honest form endorsed by the Codex audit):**
  for odd prime p, nondegenerate ternary Q over F_p, and any pool E satisfying C1
  (distinct integer norms) and C2' (distinct nonzero projective classes on the conic
  {Q=0} in PG(2,p)), the symmetric set S built from E has NO forbidden (2,2,1)
  configuration — that entire 5-subset class is nonzero by construction (Lemmas 1+2).
- **Supporting general theorems:** symmetry cap (order <= 4), parity floor (all dets
  even), scaled-shell losslessness, Ball single-prime cap, isotropic-cone cap.

**What is missing for a full general-n lower bound (e.g. C(n) >= 2n for all n):** control
of the (2,1,1,1) class — the four signed sums A+-B+-C of (norm-gap) x (bracket) terms
(Lemma 3) — and the (1^5) class. Codex's audit isolated the clean obstruction: "nonzero
triple determinants do not prevent additive cancellation"; no conic/single-prime argument
controls these archimedean sign conditions, and by Ball's theorem none can for a set of
size > p+1. A proof must either (i) choose a second prime q adaptively so all signed sums
are nonzero mod q (partially explored, works instance-by-instance — the two-prime
certificates — but no uniform choice of q is proved to exist), or (ii) an archimedean
size/ordering argument on the descending-norm greedy. Until then, "C(n) >= 2n for all
n >= 11, witnessed by CC(n)" is a CONJECTURE with verified instances at every
n in 11..21.

**(b) Empirical construction worth a paper section?** Yes, clearly. CC(n) is a
deterministic, reproducible, congruence-defined construction achieving ~2n at every
tested n — double the published n - o(n) density — with a proved layer and compact
two-prime certificates. Together with the obstruction analysis (Ball + signed sums), it
is a publishable section even without the full proof.

**(c) Search guidance?** The mined laws ARE what produced the records: one pair per
shell, distinct norms, no-3-coplanar directions, boundary bias, small shells forbidden,
exact cofactor incremental checking. SYM(n) packages them as a uniform algorithm that
delivered four new bounds in under an hour each. This is the strongest practical product.

**Overall:** (a) is partially achieved (finite certificate theorem + general layer
theorem with a precisely named gap), (b) is solidly achieved, and the work product
exceeds (c). The right paper framing is: new exact lower bounds C(13..17) with a
structure-theorem package, plus a general-n construction section at density 2n with the
proof gap stated openly.

---

## 5. What goes into the record paper vs. what needs more work

### Goes in now (ready, verified, citable)

1. **The bounds + certificates:** C(13)>=36, C(14)>=38, C(15)>=40, C(16)>=42, C(17)>=44;
   four-verifier chain; certificate JSONs as ancillary files. Footnote the independent
   n=12 33-point certificate (ties AlphaEvolve). Publish the sequence
   8,11,14,18,21,23,26,28,31,33,36,38,40,42,44 (n=3..17) — not in OEIS as of 2026-06-12;
   submitting it is a free contribution.
2. **The structure-theorem package (all proved):** Lemma 1 factorization + one-pair-per-
   shell law; scaled-shell lemma (even n); symmetry cap <= 4; parity floor; Lemma 3
   reduction of (2,1,1,1) to four signed sums; Ball-theorem consequence (no single-prime
   certificate beyond p+1 — explains the published n+o(n) plateau and why our sets must
   be, and are, mod-p generic).
3. **The SYM(n) algorithm** as the uniform general-n procedure, with the empirical
   observation that all five records sit exactly at the symmetry cap with exactly m/2
   shells.
4. **The CC(n) construction section:** definition, layer-certificate theorem, the
   deterministic 2n-2.4n table for n=7..21, two-prime certificate format, and the
   conjecture C(n) >= 2n with the named obstruction. Use Codex's wording discipline:
   layer certificate, not "proves valid"; "apparently first public explicit certificates".
5. **Saturation/isolation findings** (records totally saturated, non-nesting) as the
   structural explanation of why the problem resists closed-form constructions.
6. **The scaling conjecture** C(n) = floor((5n+7)/2), stated as exactly fitting n=7..14
   and as the source of the n=15..17 targets 41/43/46 — clearly labeled empirical.

### Needs more work (do NOT claim in the paper beyond conjecture status)

1. **Proving C(n) >= 2n for all n:** the adaptive-second-prime route on the signed sums
   A+-B+-C is the concrete open problem (Codex's proposal, partially explored in
   `second_prime_cert.py`). This would be a genuine standalone theorem strictly above
   Dong-Xu/Szabo.
2. **Closing the law at n=15..17** (41/43/46): longer SYM runs; the n=15..17 pools
   (`runs/main_n*/pool_sym.jsonl`, ~50k-140k sets each) are fresh seeds. Also a seeded
   push from the 19-pair n=14 set toward 20 pairs (40).
3. **n=11/12 deficits:** symmetric template is one pair short of the published records;
   beating 31/33 likely requires an asymmetric or near-symmetric search mode.
4. **Upper bound:** nothing below 4n exists for d=3; adapting Thiele's d=2 argument is an
   open, citable derivative target — untouched here.
5. **V4-template Rust race** at fair budget (cheap, but only worth a remark unless it
   wins).

---

## 6. Artifact index (absolute paths)

- Checker: `...\no-5-on-a-sphere-grid\code\check_cert.py`
- New record certificates: `...\mining\construct-search\cert_n14_m38.json`,
  `cert_n15_m40.json`, `cert_n16_m42.json`, `cert_n17_m44.json`; verification log
  `...\mining\construct-search\RESULTS.json` (re-generated 2026-06-12 via `harvest.py`)
- n=13 record: `...\certificates\record36_centralsym.json`
- n=12 tie: `...\mining\construct-search\runs\main_n12\best_total.json` (m=33, verified)
- Generalized Rust searcher: `...\mining\construct-search\crate\` (+ `bins\symsearch_n*.exe`)
- Deterministic construction: `...\mining\construct-algebraic\CONSTRUCTION.py`,
  `conelib.py`, flagship sets `CC_best_n{7..21}_m*.json`, `MANIFEST.json` (219/219 valid),
  `RESULTS.json`, two-prime certificates `*_2prime_p*.json`, `second_prime_cert.py`
- Lemma verification + pool laws: `...\mining\symmetry\factor_lemma.py`,
  `pool_laws.py`, `even_n_sym.py`, `maximality_scan.py`, `aug_scan.py`
- Algebraic genericity / identities: `...\mining\algebraic\` (analyze_36, pool_invariants,
  det census)
- Literature dossier: `...\mining\literature\LITERATURE.md` (+ `fit_results.json`)
- Codex audit threads: 019ebab1-579e-7321-a274-f349f47e1437 (algebraic),
  019ebab8-1c70-7920-99ee-09079d4c2d0e (search/certificates)

(`...` = `C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid`)
