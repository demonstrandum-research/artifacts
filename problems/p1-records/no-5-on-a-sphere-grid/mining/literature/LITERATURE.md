# Literature + scaling-law findings (lens: published constructions & growth fits)

Date: 2026-06-12. Companion data: `fit_results.json`, script `analyze_scaling_structure.py`.
Problem: C(n) = max |S|, S in {0..n-1}^3, no 5 points on a common sphere or plane
(= generalized Erdos-Purdy problem, ex([n]^d; d+2) with d=3 in the literature's notation).

---

## 1. State of the published art (verified 2026-06-12)

Chain of asymptotic lower bounds for ex([n]^d; d+2), d=3 specialization in brackets:

| Year | Source | Bound (d=3) | Method |
|---|---|---|---|
| 1995 | Thiele, PhD thesis "Geometric selection problems and hypergraphs" (FU Berlin) | Omega(n^{1/2}) | algebraic |
| 2024 | Suk-White, arXiv:2412.02866 (SoCG 2025) | n^{3/4 - o(1)} | random + deletion |
| 2025 | Ghosal-Goenka-Keevash, arXiv:2509.06935 | (improves Thiele d=2 circle case and Suk-White d>=4; not the d=3 leader) | deletion + incidence geometry |
| 2025 | **Dong-Xu, arXiv:2506.18113** | **n - o(n)** | rational curve mod p (see below) |
| 2025 | Szabo, arXiv:2511.03526 | n - o(n), stronger regularity: <=3 per plane, <=4 per sphere/Q-quadric | rational normal curves; finite-field analogues |

**Best published lower bound: C(n) >= n - o(n)** (Dong-Xu; Szabo variant).
**Best published upper bound: C(n) <= 4n (trivial).** Nobody has anything below (d+1)n for
d>=3. For d=2 Thiele proved 5n/2 - 3/2 < 3n, so a sub-trivial upper bound is plausibly
provable for d=3 too — an open, citable derivative target (adapt Thiele's d=2 argument).

Citation scan (Semantic Scholar, 2026-06-12): arXiv:2506.18113 has exactly 3 citers
(2511.03526, 2509.06935, 2601.14465). **No 2026 paper improves n - o(n) or 4n.** The
asymptotic constant is wide open in [1,4]; our records sit at ~2.77.

Numerical records: PatternBoost (arXiv:2411.00566) n=3..10: 8,11,14,18,20,22,25,27;
AlphaEvolve (arXiv:2511.02864 §6.60) n=7..12: 21,23,26,28,31,33 (+1 over PatternBoost at
every overlapping n); ours n=13: 36. The sequence 8,11,14,18,21,23,26,28,31,33(,36) is
**not in OEIS** (checked 2026-06-12) — publishing it is a free side contribution.

### Dong-Xu construction, pinned (their Thm 2 / Thm 4)
Over F_p with p ≡ 1 (mod 4) and **p > (d+1)! = 24**: polynomials f1,f2,f3,g,h with
f1^2+f2^2+f3^2 = g·h, degrees (3,3,3,2,4); point set = the rational curve
{(f1(t)/h(t), f2(t)/h(t), f3(t)/h(t))} ⊂ F_p^3, minus o(p) bad points. Validity is
certified **mod p**. Built from a near-diagonal matrix over F_p using α with α^2 = -1.
Consequences for us:
- Smallest usable prime for d=3 is **p=29** (needs p>24, p≡1 mod 4). The construction
  produces literally nothing at n=13,14,15; at n=29 it would give <=29 points where the
  empirical record trend predicts ~77. It is an asymptotic device, not a small-n competitor.
- Suk-White §4 also note a "modular moment curve" (x, x^2, x^3 mod n) giving Omega(n)
  points but with only the weaker guarantee no-(2d)=6-on-a-sphere — insufficient for us.

---

## 2. Headline negative theorem: the mod-p world is capped at p+1 points

**Ball's theorem** (S. Ball, JEMS 2012; MDS conjecture for prime fields; see also
Ball-Lavrauw survey "Arcs in finite projective spaces", arXiv:1908.10772): for prime p and
4 <= k <= p, every arc of PG(k-1, p) (set of vectors with every k-subset a basis) has at
most **p+1** points.

Apply with k=5: the exact validity criterion is that all 5x5 determinants of rows
(x, y, z, x^2+y^2+z^2, 1) are nonzero. If a construction certifies this **mod p** (as all
single-prime curve constructions do), the lifted vectors form an arc in PG(4,p), hence:

> **Any subset of F_p^3 whose 5-subset lifted determinants are all nonzero mod p has at
> most p+1 points.** At p=13: at most 14 points.

Consequences:
1. **PROBLEM.md attack angle 2 (34-point caps over F_13) is mathematically impossible** —
   the true maximum of that relaxation is <=14. Kill it in its pure form. (Salvage: a
   13-14 point arc skeleton as a high-quality partial seed is still legal.)
2. It explains the n + o(n) plateau of every published construction: Dong-Xu sets are
   arcs on the mod-p paraboloid, and the mod-p (torus) version of the problem is
   essentially **closed**: between p - o(p) (Dong-Xu) and p+1 (Ball).
3. **Any construction beating (1+eps)n must break the single-prime identification** —
   integer/archimedean structure, several primes (CRT), or torus-unwrapping with p ~ n/c
   (Section 4). This is the sharpest structural guidance the literature gives.
4. Empirical cross-check: our record36 has 30,032 of 376,992 five-subset dets ≡ 0 mod 13
   (7.97% ≈ 1/13 = 7.7%); pool-34 sample mean 8.1%. Record sets are **mod-13 generic** —
   zero mod-13 structure to mine. (Also: rank of quadric monomials = 10/10 over Q and
   F_13, cubic monomials 20/20 mod 13 — record sets lie on no quadric or cubic surface.)

---

## 3. Scaling law and C(14)/C(15) predictions

Data n=3..13: 8, 11, 14, 18, 21, 23, 26, 28, 31, 33, 36 (lower bounds; n>=7 are
"record-grade"). Diffs since n=7: 2,3,2,3,2,3 — perfect alternation, slope 5/2.

**Empirical law: C(n) = floor((5n+7)/2) matches ALL seven record-grade values n=7..13
exactly** (21, 23, 26, 28, 31, 33, 36). Fits (see fit_results.json):
- linear n=7..13: 2.500n + 3.286 (max residual 0.29) -> C(14)=38.3, C(15)=40.8
- linear n=3..13: 2.764n + 0.527 (max residual 1.13) -> C(14)=39.2, C(15)=42.0
- density C(n)/n drifts in 2.75-3.0 with no clear trend; 36/13 = 2.769 = 69% of the 4n cap.

**Predictions / campaign targets:**
- **C(14): 38** (formula and alternation; stretch 39). Note 38 = 2 x 19 antipodal pairs —
  n=14 has a half-integral center (6.5,6.5,6.5), p -> (13,13,13)-p, so the
  central-symmetric search transfers verbatim and the parity matches.
- **C(15): 41** (formula; stretch 42). Caveat: at n=15 the center (7,7,7) is a grid point
  but cannot be used (center + two antipodal pairs is 5-coplanar), so perfectly symmetric
  sets have even size (40/42); 41 requires a near-symmetric or asymmetric set.
- Caution: every value is a search lower bound; AlphaEvolve beat PatternBoost by exactly
  +1 at all four overlapping n. C(13)=37 is not excluded; rarity gradient in our pools
  (4126 34-sets -> 7 35s -> one 36) suggests each +1 costs 1-2 orders of magnitude.

---

## 4. Construction templates vs. what the pools actually show

Measured structure (record36 + 150-set sample of pool_34; fit_results.json):
- **Plane saturation**: record36 has 241 planes with exactly 4 points (max legal),
  pool mean 211 (range 184-244). Max points on any plane = 4 (saturated).
- **Central symmetry**: record36 and 100% of pool_34 (that run) are symmetric; of the 241
  4-point planes, exactly **153 = C(18,2) are parallelograms {p, p', q, q'}** — i.e.
  every pair of antipodal pairs spans its own distinct plane, all pre-saturated for free.
  The asymmetric-run 35s have 0 parallelogram-type planes and fewer 4-planes (98-180):
  different, weaker basin. Symmetry = free plane saturation is the empirical winning trick.
- **Zero collinear triples** in record36 and in the whole pool sample (3-in-line is legal
  but never used — a 3-point line wastes plane capacity). Records are "curve-like" locally.
- Not on any quadric/cubic; not mod-13 structured; 36 > 14 = max single-curve/arc size,
  so any curve decomposition needs >= 3 curves.

Template verdicts:
1. **Szabo/Dong-Xu single RNC (<=3 per plane)**: INCOMPATIBLE with the dense regime —
   records exploit 4-point planes massively (241 of them); <=3-per-plane sets cap near n.
   Use only as skeleton/seed material.
2. **Pure finite-field caps**: DEAD (<=14 points, Section 2).
3. **Group-orbit / centrally-symmetric templates: STRONGLY SUPPORTED** by the data.
   Literature analogue: extremal no-3-in-line configurations are symmetric (Flammenkamp);
   Hall-Jackson-Sudbery-Wild's 3n/2 construction is a symmetric algebraic orbit. Larger
   point-group orbits than Z/2 mostly create rectangles (= cocircular 4-sets, forbidden);
   inversion is the safe subgroup — consistent with what search found.
4. **HJSW torus-unwrapping (the most promising route to a (1+c)n theorem)**: the no-3-in-
   line analogue of our problem was solved to 3n/2 in 1975 by taking a conic mod p with
   p ~ n/2 and keeping ~3 of the 4 unwrapped copies (hyperbola xy ≡ k mod p). Transfer
   sketch for d=3: take the Dong-Xu/Szabo curve mod p, p ~ n/2, lift each residue point to
   2-3 of its 8 copies in {0..n-1}^3. A real sphere/plane through 5 construction points
   reduces mod p to a sphere/plane (or degenerates only if p | all of a,b,c,d of the
   primitive equation); <=4 residues per mod-p sphere forces two of the 5 points to be
   congruent mod p, i.e. differ by p·eps, eps in {-1,0,1}^3 — so validity reduces to
   finitely many local copy-selection constraints, a small CSP per residue. Target:
   provable 1.5n - 2n for all large n. This is the parameterized-construction candidate
   most compatible with both the literature and our record structure (symmetric, plane-
   saturated, multi-curve). Compare Kovacs-Nagy-Szabo arXiv:2508.07632, who get
   (1-2/k)·kn for no-(k+1)-in-line by randomized algebraic constructions — k=4 analogue
   would read "2n for no-5-on-a-plane-like constraints", exactly the density scale our
   data says is beatable.
5. **Analogy table** (trivial UB / small-n records / best general construction / conj.):
   - no-3-in-line, d=2: 2n / 2n exactly (n<=46+) / 1.5n (HJSW 1975) / ~1.814n (Guy-Kelly)
   - no-4-on-circle, d=2: 3n, improved UB 2.5n-1.5 (Thiele) / ? / n - o(n) (Dong-Xu) / open
   - no-5-on-sphere, d=3 (ours): 4n / ~2.77n (us) / n - o(n) / open
   The no-3-in-line history says: small-n saturation need not persist asymptotically, and
   constant>1 theorems come from algebraic orbits on tori, not from single curves.

## 5. Risk + opportunity notes
- **Scoop watch**: the Budapest group (Nagy, Szabo, Kovacs, Janosik, ...; arXiv:2508.07632,
  2511.03526, 2601.14465) is actively publishing on exactly this template family; a
  (1+c)n construction for spheres from them is plausible within months.
- **Open citable side-theorems within reach**: (a) C(n) <= (4-c)n by adapting Thiele's
  d=2 upper-bound argument; (b) the mod-p ceiling corollary of Ball's theorem (Section 2)
  appears unobserved in the literature — worth a remark in any write-up; (c) the OEIS
  sequence; (d) the exact mod-p torus problem being squeezed to [p - o(p), p+1].
