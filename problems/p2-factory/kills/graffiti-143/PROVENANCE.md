# Provenance — Graffiti Conjecture 143 (Gate-4 clean-room verification)

Verification date: 2026-06-11. Verifying agent: Gate-4 clean-room subagent
(independent of the discovery session; no code reused from `.scratch` or
`verify_kills.py`).

## Authoritative statement

Source PDF: `wow-july2004.pdf`
URL: https://raw.githubusercontent.com/RoucairolMilo/refutation-COCOON2022/master/wow-july2004.pdf
(S. Fajtlowicz, "Written on the Wall" — Graffiti conjecture list, July 2004
compilation; the same file cited by Roucairol & Cazenave.)
Accessed: 2026-06-11. SHA256 recorded in `verification_log.txt`.

The PDF uses dvips Type-3 bitmap fonts without ToUnicode maps; extracted text
shows glyph names `/XY`. Decoding (verified on the document title and body):
glyph name = two base-36 digits, `char = chr(36*idx(X) + idx(Y) - 360)`.
Decoder: `decode_wow.py` step inside this directory (output
`wow_decoded_test.txt`).

Verbatim decoded line (p. 65 region, conjecture block 140–146):

> 142. minimum positive eigenvalue ≤ n / average distance.
> **143. variance of positive eigenvalues ≤ size / average distance.**
> 144. variance of positive eigenvalues ≤ size − matching.

The inequality glyph is `/AK` = char 0x14 = `\leq` in TeX cmsy encoding:
**non-strict** ≤. A counterexample therefore needs strict `>`.

No resolver annotation is attached to 143 (compare 108 "Disproved by William
Staton", 138 "[FMS2] proved that this conjecture is true for all graphs but
K2"). The bare "[FMS2], December 89" sits after 145. WoW also records (p. ~45)
a list of conjectures that "passed the test" of a refutation effort (~200
tested, >40 refuted, attributed [BDF], Aug '90–Aug '91) — 143 is in the
"passed" list.

## Definitional conventions (from the same document)

* Intro: "G always denotes a graph, n the number of its vertices and
  eigenvalues (unless it is explicitly stated) denote eigenvalues of the
  **adjacency matrix** of G."
* Intro: "All conjectures are restricted to graphs in which all involved
  concepts are well defined, so for example conjectures involving distance
  are only for **connected** graphs."
* Comment to conjectures 4–6: "All **statistical invariants** like for example
  variance are derived from the degree sequence or other functions by treating
  them as random variables on **uniform sample spaces**" → *population*
  variance (divide by k), k = number of strictly positive adjacency
  eigenvalues counted with multiplicity.
* "size" = number of edges m (usage consistent across 144, 146, 213).
* "average distance": two standard machine readings exist —
  - **N2**: mean of all n² ordered-pair entries of the distance matrix
    (diagonal included) = 2W/n². This is exactly what the Roucairol–Cazenave
    search code uses (see below), and gives the LARGER right-hand side
    m·n²/(2W) — the harder target.
  - **PAIRS**: mean over distinct pairs = 2W/(n(n−1)) (Aouchiche–Hansen
    convention; WoW elsewhere says "average distance between its distinct
    vertices"), RHS = m·n(n−1)/(2W).
  The kill certifies violation of **both** readings (instances n=39,40,48);
  additional smaller instances (n=37,38) violate the PAIRS reading only.

## Openness evidence

* Roucairol & Cazenave, "Refutation of Spectral Graph Theory Conjectures with
  Search Algorithms", ECAI 2025 (arXiv:2409.18626, fetched 2026-06-11):
  results table row: `143 O 100 any & tree  - - - - - - - -`
  → status **O**pen, searched up to size 100, none of their 8 algorithms
  found a counterexample (in graphs and trees).
* Their formalization, repo `RoucairolMilo/refutationGBR`,
  `models/conjectures/GenerateGraph.rs` (fetched 2026-06-11), `CONJECTURE == 143`
  branch: mean distance = mean over all n² entries of the BFS distance matrix
  (diagonal included); positive eigenvalues = `> 0.0001`; variance =
  `std_dev(eig_pos)^2` with `std`/`std_dev` dividing by the list length
  (population variance, `tools/calc.rs`); violation flagged when
  `v - m/mean_dist > 1e-5`. Comment line 17: `// ... 143 NO` (their searches
  failed).
* WoW itself (2004) lists 143 unresolved; conjecture 143 "passed" the [BDF]
  refutation effort c. 1990–91.

## What the certificate shows

Connected graphs violating conjecture 143 under the formalizations above:

| instance | n | m | W | k | var_pos (certified) | margin N2 | margin PAIRS |
|---|---|---|---|---|---|---|---|
| dumbbell(20,8,20) | 48 | 389 | 6568 | 6 | 69.63496324… | **+1.40597** | +2.82741 |
| dumbbell(8,12,20) | 40 | 231 | 5372 | 8 | 34.89276446… | **+0.49217** | +1.35218 |
| dumbbell(7,12,20) | 39 | 224 | 4976 | 8 | 34.31513047… | **+0.08040** | +0.95822 |
| dumbbell(6,12,20) | 38 | 218 | 4581 | 8 | 33.95737902… | −0.40106 | **+0.50311** |
| dumbbell(6,12,19) | 37 | 199 | 4383 | 8 | 30.31239262… | −0.76575 | **+0.07420** |

dumbbell(t1,p,t2) = K_t1 and K_t2 joined by a path with p internal vertices
(one attachment vertex per clique). All margins are exact rational lower
bounds certified by interval arithmetic at width ≤ 2^-70 on isolated roots of
the integer characteristic polynomial (two independent exact routes; see
`checker_g143.py`).

Float-level exhaustive scan of the whole dumbbell family (all t1,t2 ≥ 1,
p ≥ 0, n ≤ 48): smallest violation of the N2 reading is n=39 (7,12,20);
smallest violation of the PAIRS reading is n=37 (6,12,19); no dumbbell with
n ≤ 36 comes within 0.35 of either bound (≫ float noise). A simulated-
annealing probe outside the family at n ≤ 38 (N2) / n ≤ 36 (PAIRS) found no
violation (heuristic evidence only).
