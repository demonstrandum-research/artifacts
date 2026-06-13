# Refutation of Graffiti Conjecture 143 (Fajtlowicz, "Written on the Wall")

Gate-5 write-up, 2026-06-11. Bundle:
`C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\graffiti-143\`

---

## Abstract (~120 words)

Graffiti Conjecture 143 (S. Fajtlowicz, "Written on the Wall"; July 2004
compilation) asserts that in every connected graph the variance of the
positive adjacency eigenvalues is at most size / average distance. It was
listed open in Roucairol & Cazenave (ECAI 2025), who searched graphs and
trees to size 100 with eight algorithms without finding a counterexample. We
refute it with dumbbell graphs: two cliques joined by a path. The smallest
certified counterexample, dumbbell(7,12,20) on n = 39 vertices, violates the
conjecture under both standard readings of "average distance" (2W/n² and
2W/(n(n−1))); dumbbell(6,12,19) on n = 37 violates the distinct-pairs
reading. All violations carry exact rational certificates (interval
arithmetic on integer characteristic polynomials); verification is a
one-minute Python run. Asymptotically the LHS/RHS ratio tends to 2 along
balanced dumbbells.

---

## Result (claim-standard form, FRAMEWORK.md §9)

> **Result.** Graffiti Conjecture 143 — verbatim from the frozen source
> (`PROVENANCE.md`, decoded from `wow-july2004.pdf`, p. 65 region):
> *"143. variance of positive eigenvalues ≤ size / average distance."*
> (≤ = TeX cmsy glyph 0x14, non-strict) — is **FALSE** for connected graphs,
> under both standard machine readings of "average distance": the
> ordered-pairs-with-diagonal mean 2W/n² (the reading hard-coded in the
> Roucairol–Cazenave ECAI 2025 search code, the larger RHS and hence the
> harder target) and the distinct-pairs mean 2W/(n(n−1)) (Aouchiche–Hansen
> convention). "Variance" is population variance (WoW's "uniform sample
> spaces" doctrine; also the Roucairol `calc.rs` std(), which divides by the
> list length); "size" is m = |E|. The violations are strict, as a
> counterexample to a non-strict ≤ requires.
>
> **Status before this work.** Open. Roucairol & Cazenave, *Refutation of
> Spectral Graph Theory Conjectures with Search Algorithms*, ECAI 2025
> (arXiv:2409.18626, still v1 of 2024-09-27 as of 2026-06-11): results-table
> row `143 O 100 any & tree - - - - - - - -` — open, searched to size 100,
> none of their 8 algorithms found a counterexample. WoW (July 2004) attaches
> no resolver annotation to 143 and lists it among conjectures that "passed"
> the [BDF] refutation effort of c. 1990–91. Codex (GPT-5.5) prior-art search
> (FMS 1993/1995, arXiv, MATCH) found no prior resolution. Fresh kill-check
> 2026-06-11: see below — nothing found.
>
> **Artifact.** `certificate_g143.json` — five dumbbell instances with
> explicit edge lists, integer invariants (n, m, W, k), exact rational RHS
> values, certified rational variance intervals (width ≤ 2⁻⁷⁰·poly), and
> exact rational lower bounds on every claimed violation margin.
> `build_certificate.py` regenerates it deterministically.
>
> **Verification.** Checker `checker_g143.py` (Python, written from scratch
> by the Gate-4 clean-room agent, independent of the discovery pipeline)
> verifies every instance by **two independent exact routes** and accepts
> only if both certify the strict inequality: Route A — sympy integer
> charpoly + exact real-root isolation (`Poly.intervals`, eps = 2⁻⁷⁰);
> Route B — pure stdlib (`fractions` only): own Berkowitz characteristic
> polynomial, equitable-partition quotient check via the exact integer
> identity charA(x) = charB(x)·(x+1)^(t1+t2−4), Yun squarefree decomposition,
> Sturm-chain isolation, bisection refinement to width 2⁻⁷⁰, rational
> interval arithmetic for the variance. No floats anywhere on the accept
> path. Cross-demands: identical charpolys, trace/edge coefficient checks,
> agreeing k, intersecting variance intervals, connectivity, recomputed W, m,
> RHS fractions, canonical-dumbbell edge-list equality. Mutation testing:
> `mutation_tests.py`, 10 targeted corruptions, all REJECTed, pristine
> ACCEPTed (re-run fresh 2026-06-11: `MUTATION TESTS: ALL KILLED`).
> Independent confirmations: the orchestrator's `../../verify_kills.py`
> §4 rebuilds dumbbell(20,8,20) from the construction description (not the
> agent's edge list) and confirms violation of both conventions at float
> level; Codex (GPT-5.5, hostile-referee framing, full shell access)
> independently recomputed all five instances with numpy/mpmath, matched
> every certificate field, attacked alternate readings (sample variance,
> size = n, average eccentricity — all still violated), and returned
> **"VERDICT: ACCEPT (kill stands)"** after one bundle fix (UTF-8 stdout
> reconfigure for cp1252 consoles) and two hygiene patches, all re-tested.
> Fresh-run log with sha256 hashes: `verification_log.txt`.
>
> **Openness re-check.** 2026-06-11, this session (queries and results in
> "Final kill-check" below): no prior or concurrent resolution found.
>
> **What this does not show.** See final section.

---

## Exact statement and provenance

* **Source:** S. Fajtlowicz, "Written on the Wall" (the Graffiti conjecture
  list), July 2004 compilation. PDF fetched 2026-06-11 from
  `https://raw.githubusercontent.com/RoucairolMilo/refutation-COCOON2022/master/wow-july2004.pdf`
  (the file cited by Roucairol & Cazenave),
  sha256 `d2c779d2c28418b30ab1b4f84bf7112c0e000bca1f2d6a3c48d0baba78af7733`.
* The PDF uses dvips Type-3 bitmap fonts without ToUnicode maps; the decode
  chain (glyph name = two base-36 digits, `char = chr(36*idx + idx − 360)`)
  is `decode_wow.py` → `wow_decoded_test.txt`, validated against the document
  title and surrounding conjectures (142, 144). Verbatim:
  **"143. variance of positive eigenvalues ≤ size / average distance."**
* Conventions, all fixed from the same document (full quotes in
  `PROVENANCE.md`): adjacency-matrix eigenvalues; connected graphs only
  (distance must be defined); statistical invariants on "uniform sample
  spaces" → population variance over the k strictly positive eigenvalues
  counted with multiplicity; "size" = m. The only genuine ambiguity is
  "average distance"; **both** standard readings are violated:
  * **N2**: l = 2W/n² (mean over all n² ordered pairs incl. diagonal) —
    RHS = m·n²/(2W). This is exactly the Roucairol–Cazenave formalization
    (`GenerateGraph.rs`, `CONJECTURE == 143` branch, in this bundle).
  * **PAIRS**: l = 2W/(n(n−1)) — RHS = m·n(n−1)/(2W) (Aouchiche–Hansen).

## The counterexamples

dumbbell(t1, p, t2) = K_t1 and K_t2 joined by a path with p internal
vertices, attached at one vertex of each clique. Canonical labels: clique
K_t1 on {0,…,t1−1}, path on {t1,…,t1+p−1}, clique K_t2 on {t1+p,…,n−1},
chain 0 − t1 − t1+1 − ⋯ − t1+p−1 − t1+p. Explicit edge lists are in
`certificate_g143.json`.

| instance | n | m | W | k | var_pos (certified) | RHS_N2 (exact) | RHS_PAIRS (exact) | margin ≥ (N2) | margin ≥ (PAIRS) |
|---|---|---|---|---|---|---|---|---|---|
| dumbbell(20,8,20) | 48 | 389 | 6568 | 6 | 69.63496324… | 56016/821 ≈ 68.2290 | 54849/821 ≈ 66.8076 | **+1.405974206** | **+2.827411478** |
| dumbbell(8,12,20) | 40 | 231 | 5372 | 8 | 34.89276446… | 46200/1343 ≈ 34.4006 | 45045/1343 ≈ 33.5406 | **+0.492168780** | **+1.352183672** |
| **dumbbell(7,12,20)** | **39** | 224 | 4976 | 8 | 34.31513047… | 10647/311 ≈ 34.2347 | 10374/311 ≈ 33.3569 | **+0.080403779** | **+0.958217284** |
| dumbbell(6,12,20) | 38 | 218 | 4581 | 8 | 33.95737902… | 157396/4581 ≈ 34.3584 | 153254/4581 ≈ 33.4543 | — (not violated) | **+0.503111388** |
| **dumbbell(6,12,19)** | **37** | 199 | 4383 | 8 | 30.31239262… | 272431/8766 ≈ 31.0781 | 14726/487 ≈ 30.2382 | — (not violated) | **+0.074199602** |

All margins are **exact rational lower bounds** (the rationals themselves are
stored in the certificate), certified via 2⁻⁷⁰-width interval arithmetic on
Sturm-isolated roots of the integer characteristic polynomial — not floats.

Smallest certified counterexample under both readings: **n = 39**,
dumbbell(7,12,20). Under the distinct-pairs reading alone: **n = 37**,
dumbbell(6,12,19). (The discovery-session claim record listed n = 40 as the
minimal known; the Gate-4 pass improved this to 39 / 37.)

**Mechanism.** A dumbbell has k positive eigenvalues: two large ≈(t−1)
"clique" eigenvalues plus k−2 small "path" eigenvalues, so
var ≈ 2t²(k−2)/k², while m/l ≈ 2m/diam ≈ t²/k grows only half as fast in k;
the LHS/RHS ratio → 2 as the family scales. E.g. dumbbell(40,10,40) (n = 90)
violates the harder N2 reading by margin ≈ +59.7, ratio ≈ 1.26 (float-level
color, not part of the certificate). The conjecture does not fail by a hair;
it fails structurally. Roucairol–Cazenave-style edge-by-edge Monte-Carlo
search plausibly missed these because two-cliques-plus-long-path states are
deep, low-scoring intermediates.

**Float sanity check** (independent of all bundle code; population variance,
both conventions; tested 2026-06-11, prints
`8 4976 34.31513046745225 34.234726688102896 33.356913183279744`):

```python
import numpy as np, itertools
from collections import deque
t1, p, t2 = 7, 12, 20; n = t1 + p + t2          # dumbbell(7,12,20), n=39
E  = list(itertools.combinations(range(t1), 2))                 # K_7
E += list(itertools.combinations(range(t1 + p, n), 2))          # K_20
chain = [0] + list(range(t1, t1 + p)) + [t1 + p]                # joining path
E += list(zip(chain, chain[1:]))
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
W = 0                                            # Wiener index by BFS
for s in range(n):
    d = [-1] * n; d[s] = 0; q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0: d[w] = d[u] + 1; q.append(w)
    W += sum(d)
W //= 2
A = np.zeros((n, n))
for u, v in E: A[u, v] = A[v, u] = 1
pos = np.linalg.eigvalsh(A); pos = pos[pos > 1e-9]
m, var = len(E), pos.var()                       # population variance
print(len(pos), W, var, m*n*n/(2*W), m*n*(n-1)/(2*W))
```

var_pos ≈ 34.3151 strictly exceeds both 34.2347 (N2) and 33.3569 (PAIRS).
(The certificate checker is the authoritative verification; this snippet is
orientation only.)

## How to verify (under a minute; Python 3 + sympy + numpy)

```
cd problems/p2-factory/kills/graffiti-143
python checker_g143.py certificate_g143.json   # expect: CHECKER VERDICT: ACCEPT, exit 0
python mutation_tests.py                       # expect: MUTATION TESTS: ALL KILLED
```

Both re-run fresh on 2026-06-11 (this Gate-5 pass): ACCEPT / ALL KILLED.
Orchestrator-level independent rebuild: `python ../../verify_kills.py`
(section `[143]`) reconstructs dumbbell(20,8,20) from the construction
description and confirms both violations. Hashes of every artifact:
`verification_log.txt`.

## Extension findings (beyond the claim record)

* **Smaller counterexamples.** The claim record's minimal n = 40 is
  superseded: n = 39 (both readings) and n = 37 / n = 38 (pairs reading),
  all exactly certified in this bundle.
* **Family-exhaustive minimality.** `scan_dumbbells.py`: float-exhaustive
  scan of the entire dumbbell family (all t1 ≥ 1, t2 ≥ t1, p ≥ 0, n ≤ 48)
  shows n = 39 (7,12,20) is family-minimal for the N2 reading and n = 37
  (6,12,19) for the PAIRS reading; no dumbbell with n ≤ 36 comes within 0.35
  of either bound (≫ float noise).
* **Beyond-family probe.** `local_search_probe.py`: simulated annealing
  (24 restarts × 3000 iters per task, plus a bounded re-run) at n = 37–38
  (N2) and n = 35–36 (PAIRS) found no violation (best margins −0.57 to
  −1.32). Heuristic evidence only.
* **Robust-reading checks (Codex).** Sample variance (divide by k−1):
  violation becomes *stronger*. size = n: still violated. Average
  eccentricity in place of average distance: still violated. Only
  illegitimate readings (e.g. variance of *all* eigenvalues) rescue the
  inequality.
* **Asymptotics.** LHS/RHS → 2 along balanced dumbbells (n = 90 instance
  ≈ 26% violation, float-level).

## Final kill-check (Gate-5, dated 2026-06-11)

Searches run this session, after verification, looking for any prior or
just-published resolution of WoW Conjecture 143:

1. Web search `Graffiti conjecture 143 "variance of positive eigenvalues"
   counterexample refuted` → only FMS 1993/1995 Graffiti papers (nearby
   conjectures, not 143), arXiv:2409.18626 (lists 143 Open), and the
   unrelated Graffiti.pc list. **Nothing.**
2. Web search `"Written on the Wall" Fajtlowicz conjecture 143 eigenvalues
   "average distance"` → WoW background, Aouchiche–Hansen distance papers;
   nothing on 143. **Nothing.**
3. Web search `arXiv 2025 2026 refutation Graffiti conjecture spectral
   "average distance" counterexample dumbbell` → arXiv:2409.18626 (refutes
   197, lists 143 open), 2207.03343, 2306.07956, Optimist 2411.09158.
   **Nothing on 143.**
4. Web search `"conjecture 143" Graffiti eigenvalues 2026` → only
   Graffiti.pc #143 (girth/induced-triangle statement — a *different list
   with different numbering*; noted to avoid confusion). **Nothing.**
5. Web search `Roucairol Cazenave Graffiti 143 open conjecture counterexample
   2025 2026` → no work newer than ECAI 2025. **Nothing.**
6. Web search `"variance of the positive eigenvalues" graph conjecture` →
   only the s⁺ (sum of squares of positive eigenvalues) literature (Elphick
   et al.), a different quantity. **Nothing.**
7. Web search `refute "Graffiti" conjecture eigenvalue 2026 "open"
   Fajtlowicz counterexample new` → Graffiti 137/301 refutations (Roucairol
   line of work); nothing on 143. **Nothing.**
8. arXiv abs page for 2409.18626 → still **v1 (2024-09-27)**; no revision
   announcing new refutations.
9. arXiv full-text search (`"Graffiti" conjecture eigenvalue`, newest
   first) → one 2025 hit (2509.05814, graph-energy SDP, unrelated).
   **Nothing.**
10. arXiv export API and Semantic Scholar API direct queries: rate-limited
    (HTTP 429/503) at run time; coverage substituted by searches 1–9.

Also standing from Gate-4 (2026-06-11): Codex hostile-referee prior-art
search (FMS 1993, arXiv, MATCH) found no earlier resolution; ECAI 2025 table
explicitly lists `143 O 100`. **Conclusion: no prior or concurrent
resolution found. The kill stands as of 2026-06-11.** Residual risk, as
flagged by Codex: bibliographic completeness of pre-web Graffiti
correspondence (WoW resolver annotations are the only systematic record).

## What this does not show

* **No general minimality.** Minimality is established only within the
  dumbbell family (float-exhaustive, n ≤ 48). Non-dumbbell counterexamples
  with n < 37 are not excluded; the annealing probe below the records is
  heuristic, not exhaustive.
* **The n = 90 asymptotic example is float-level color**, not certified;
  the certified claims are exactly the five certificate instances.
* **Reading dependence is fully disclosed:** under the N2 reading the
  certified record is n = 39; n = 37/38 violate only the distinct-pairs
  reading. Both readings are standard and both are killed, but a third,
  non-standard reading of "average distance" is conceivable in principle
  (none found in WoW or the formalization literature).
* **Nothing is claimed about conjectures 142, 144, or any other WoW item**
  beyond what their own bundles certify.
* The historical "[BDF] passed" note means a c. 1990 refutation *search*
  failed on 143; it is evidence of openness, not of truth.

## Publication grouping

This kill belongs with **graffiti-154** (the two Graffiti "Written on the
Wall" spectral kills: same source document, same decode/provenance chain,
same Roucairol–Cazenave openness anchor, same exact-spectral certification
machinery) — natural single short note, e.g. as a direct follow-up to
Roucairol & Cazenave (ECAI 2025). Separate bundles: the three solubilizer
kills (solubilizer-a1, -a13, -a16; finite group theory) and the two
TxGraffiti-family kills (davila-conj9, pandey-parity).
