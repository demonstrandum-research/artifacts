# Refutation of Graffiti Conjecture 154 (deviation of eigenvalues ≤ n / average distance) under the standard-deviation reading

**Slug:** `graffiti-154` · **Status:** verified kill (Gate 4 passed 2026-06-11; Gate 5 this document, 2026-06-11)

---

## Abstract (~120 words)

We refute Graffiti Conjecture 154 (S. Fajtlowicz, *Written on the Wall*, c. 1988):
"deviation of eigenvalues ≤ n / average distance", under the standard-deviation reading
of "deviation" — the reading of Favaron–Mahéo–Saclé (1993) and of the only known machine
formalization (Roucairol–Cazenave 2024/2025) — and under **both** standard conventions
for average distance. Counterexamples are lollipop graphs (clique K_t plus pendant path
P_p): the adjacency spectrum has mean 0 and population standard deviation exactly
√(2m/n), so violation reduces to the pure integer inequality 8mW² > n⁵(n−1)² (distinct
pairs) or 8mW² > n⁷ (all n² entries), with W the Wiener index. lollipop(72,72) (n = 144)
violates both with an 11% margin, and the violation ratio is unbounded as t = p → ∞.
The conjecture had survived eight-algorithm searches to size 50 (IASE workshop at
ECAI 2025). Under the mean-absolute-deviation reading these instances provably do *not*
violate the inequality.

---

## 1. Result (claim standard, FRAMEWORK §9)

> **Result.** Graffiti Conjecture 154 is **false** for connected graphs under the
> standard-deviation reading of "deviation", under both standard conventions for
> "average distance".
>
> Verbatim conjecture (WoW July 2004 compilation, glyph-decoded; frozen 2026-06-11):
> *"154. deviation of eigenvalues <= n / average distance."*
> WoW preamble (verbatim, decoded): *"G always denotes a graph, n the number of its
> vertices and eigenvalues (unless it is explicitly stated) denote eigenvalues of the
> adjacency matrix of G."* No exclusions or extra quantifiers attach to 154;
> connectivity is implicit in "average distance" being defined.
>
> Operationally: for every connected graph G on n vertices with m edges and Wiener
> index W, the conjecture asserts √(2m/n) ≤ n/ℓ, where √(2m/n) is the population
> standard deviation of the adjacency spectrum (exact, since tr A = 0 and tr A² = 2m)
> and ℓ is the average distance — either ℓ = 2W/(n(n−1)) (distinct ordered pairs, the
> convention of WoW's own usage and of FMS 1993) or ℓ = 2W/n² (mean over all n² distance-
> matrix entries, the convention of the Roucairol–Cazenave search code). It fails for
> lollipop graphs from n = 118 (distinct pairs) / n = 120 (both conventions) onward.
>
> **Status before this work.** Open. WoW itself lists 154 among the conjectures that
> *passed* the 1990–91 Brewster–Dinneen–Faber computational attack (~200 conjectures
> tested, 40+ refuted); the published subset (Discrete Math. 147 (1995) 35–55) does not
> resolve it. Roucairol–Cazenave, *Refutation of Spectral Graph Theory Conjectures with
> Search Algorithms* (arXiv:2409.18626, Sep 2024; published at the IASE 2025 workshop at
> ECAI 2025), Table 1 row "154 O 50 any & tree − − − − − − − −": status **Open**,
> searched to size 50 on general graphs and trees with 8 search algorithms, no
> counterexample. (First violations start at n = 118 — beyond every prior search
> horizon.) Fresh kill-checks at selection time and again at Gate 5 (both 2026-06-11,
> §7) found no prior or concurrent refutation.
>
> **Artifact.** `certificate.json` (this directory): three certified instances
> lollipop(48,70), lollipop(50,70), lollipop(72,72) with all integer quantities, the
> integer violation forms, the exhaustive minimality scan, and exact-arithmetic MAD
> non-violation enclosures. Supporting provenance: `PROVENANCE.txt`, archived sources
> `wow-july2004.pdf` + `wow-decoded.txt`, `bdf1995.pdf`, `rc2024-search-algorithms.pdf`,
> `rc-ecai2025.pdf`, `GenerateGraph.rs`/`calc.rs` (the R–C formalization).
>
> **Verification.** Checker A: `check_graffiti154.py` (Python, clean-room Gate-4 agent;
> integer-only accept path for the kill; run log `checker_run.log`, all-PASS). Checker B:
> `codex_referee_audit.py` (independently written by the hostile Codex referee, GPT-5.5,
> different model family; pure integer inequalities, BFS Wiener index). Orchestrator
> cross-check: `..\..\verify_kills.py` section "[154]" (independent rebuild from the
> construction description). Mutation tests: six targeted corruptions, all rejected
> (§5). Codex verdict: **KILL CONFIRMED** (verbatim in `CODEX_VERDICT.txt`, thread
> 019eb9b1-0fa3-7870-bf5f-e42d2cb3ac68; its four nits were all fixed/dispositioned).
>
> **Openness re-check.** 2026-06-11 (Gate 5, this document, §7): six independent
> searches (web, arXiv API, Semantic Scholar citation graph of arXiv:2409.18626) found
> no published or preprint refutation of conjecture 154.
>
> **What this does not show.** See §8. In particular the kill is claimed **only** under
> the standard-deviation reading of "deviation"; under the mean-absolute-deviation
> reading these instances provably satisfy the inequality.

---

## 2. Provenance of the statement (frozen)

- Source: S. Fajtlowicz, *Written on the Wall* (the Graffiti conjecture compilation),
  July 2004 version. URL (accessed 2026-06-11):
  `https://raw.githubusercontent.com/RoucairolMilo/refutation-COCOON2022/master/wow-july2004.pdf`
  (archived here as `wow-july2004.pdf`, 907,641 bytes).
- The PDF's Type-3 fonts carry no ToUnicode maps; glyphs are named `/XY` with X,Y in
  0–9A–Z and decode as `chr((digit36(X)−10)·36 + digit36(Y))`; "<=" renders as glyph
  `/AK`. Full decoded text: `wow-decoded.txt`. Codex independently *rendered* the PDF
  pages (its `codex_wow_page67.png`, `codex_wow_page98.png`) and confirmed the decoded
  statement pixel-for-pixel, and that 154 does **not** sit under the later
  "triangle-free graphs" section heading.
- Convention "deviation" (the load-bearing one): WoW uses *variance* (conj. 38, 143) and
  *deviation* (conj. 39, 40, 140, 154, 244, 253) as distinct invariants and spells out
  "standard deviation" for degree sequences (conj. 27, 812, 813) — reading: deviation =
  √variance = population standard deviation. Favaron–Mahéo–Saclé, *Some eigenvalue
  properties in graphs (conjectures of Graffiti — II)*, Discrete Math. 111 (1993)
  197–220 (the historical treatment of WoW "deviation of eigenvalues" conjectures;
  Academia.edu mirror, accessed 2026-06-11 by both this pipeline and Codex) defines the
  eigenvalue "deviation" by an RMS/square-root formula — standard deviation, not mean
  absolute deviation — and defines mean distance over ordered **distinct** vertex pairs.
  The only public machine formalization (Roucairol–Cazenave `refutationGBR`,
  `models/conjectures/GenerateGraph.rs`, `CONJECTURE == 154` block; archived here)
  computes the population standard deviation of all adjacency eigenvalues
  (`tools/calc.rs` `std`: divide by len, then sqrt).
- Convention "average distance": WoW's own comment on conjecture 536 ("The average
  distance of this graph is 3/2", Paley graphs) holds only under the distinct-pairs
  convention ℓ = 2W/(n(n−1)); the R–C code instead uses ℓ = 2W/n² (all n² entries,
  zero diagonal included). Both conventions are refuted by lollipop(50,70) and
  lollipop(72,72), so the ambiguity is immaterial to the result.
- Full provenance trail with verbatim quotes: `PROVENANCE.txt`.

---

## 3. The counterexamples (inline)

**Family.** lollipop(t,p): complete graph K_t on vertices 0..t−1; path on vertices
t..t+p−1; one bridge edge (0,t). Then n = t+p, m = t(t−1)/2 + p, connected, and

    W = C(t,2) + Σ_{k=1..p} [k + (t−1)(k+1)] + C(p+1,3)

(clique pairs + clique-to-path pairs + path-internal pairs; re-verified by all-pairs BFS
on the explicit edge list in every checker run).

**Exact violation test (pure integers, no floating point anywhere).** Squaring
√(2m/n) ≤ n/ℓ (all quantities positive):

- distinct-pairs convention (DP): violation ⇔ **8mW² > n⁵(n−1)²**
- all-n²-entries convention (N2): violation ⇔ **8mW² > n⁷**

| instance | n | m | W | 8mW² | n⁵(n−1)² (DP) | n⁷ (N2) | verdict |
|---|---|---|---|---|---|---|---|
| lollipop(48,70) | 118 | 1198 | 180853 | 313,471,628,124,656 | 313,171,159,328,352 | 318,547,390,056,832 | violates DP (margin 300,468,796,304); not N2 (short 5,075,761,932,176) |
| lollipop(50,70) | 120 | 1295 | 186060 | 358,645,832,496,000 | 352,370,995,200,000 | 358,318,080,000,000 | violates **both** (margins 6,274,837,296,000 / 327,752,496,000) |
| lollipop(72,72) | 144 | 2628 | 259080 | 1,411,182,313,113,600 | 1,266,148,181,016,576 | 1,283,918,464,548,864 | violates **both** (margins 145,034,132,097,024 / 127,263,848,564,736) |

For lollipop(72,72): std-dev = √36.5 = 6.0415…, against n/ℓ = 5.7226… (DP) and
5.7627… (N2) — an ≈ 11% violation under the squared comparison. (Decimals are
informational; the verdict is the integer inequality above.)

**Asymptotics.** For t = p → ∞: √(2m/n) ~ √(t/2) → ∞ while n/ℓ stays bounded (≈ 6), so
the violation ratio is unbounded — the std-dev reading fails catastrophically, not
marginally. Dumbbells (two cliques joined by a path) also violate.

**Minimality within the family (exhaustive integer scan, all t ≥ 3, p ≥ 1, n ≤ 130;
Codex re-ran it allowing degenerate t = 1, 2 as well).** No lollipop with n ≤ 117
violates either convention. At the minimal order n = 118 there are exactly **four** DP
violators: (48,70), (49,69), (50,68), (51,67); at the minimal order n = 120 exactly
**two** both-convention violators: (50,70), (51,69). Every N2 violator is automatically
a DP violator since n⁷ > n⁵(n−1)².

**One-minute spot check** (stranger-verifiable; integers only):

```python
t, p = 72, 72
n, m = t+p, t*(t-1)//2 + p
W = t*(t-1)//2 + sum(k + (t-1)*(k+1) for k in range(1, p+1)) \
    + (p+1)*p*(p-1)//6
assert 8*m*W*W > n**5 * (n-1)**2     # distinct-pairs convention
assert 8*m*W*W > n**7                # all-n^2-entries convention
print("Graffiti 154 (std-dev reading) refuted:", n, m, W)
```

---

## 4. Why the std-dev is exactly √(2m/n)

tr A = 0 (no loops) and tr A² = 2m (sum of degrees), so the population variance of the
n adjacency eigenvalues is (1/n)Σλᵢ² − ((1/n)Σλᵢ)² = 2m/n exactly. The kill therefore
needs **no floating point and no eigenvalue computation at all**. The checkers
additionally reproduce both trace identities numerically on the actual 144×144 (etc.)
adjacency matrices at float64 and at mpmath dps = 60, as a sanity cross-check only.

---

## 5. Verification procedure

All commands run from this directory (`problems\p2-factory\kills\graffiti-154`);
Python 3.11 with numpy/mpmath/sympy (the latter only for the spectral cross-checks and
the exact MAD side-claim — the kill verdict itself is stdlib integers).

1. **Checker A (clean-room, Gate-4 author ≠ discoverer):**
   `python check_graffiti154.py` → must end `OVERALL: ALL CHECKS PASS`. It rebuilds the
   three lollipops from scratch, verifies m and the degree sequence, computes W by
   all-pairs BFS **and** by the closed form (must agree), evaluates the integer
   violation forms, reproduces every integer in the claim record, reruns the exhaustive
   n ≤ 130 minimality scan, proves the MAD side-claim in exact arithmetic two
   independent ways (Sturm-certified rational energy enclosures of width ~2.5·10⁻¹⁷ via
   the degree-(t+2) equitable-quotient characteristic polynomial, e.g.
   energy(lollipop(72,72)) ∈ [233.576286493359, 233.576286493359]; plus an
   exact-rational Koolen–Moulton route), and cross-checks the certified spectrum against
   numpy. Archived log: `checker_run.log`.
2. **Checker B (independent, different model family):** `python codex_referee_audit.py`
   — written by the hostile Codex referee during Gate 4; independently rebuilds the
   lollipop, BFS Wiener index, closed form, and pure integer inequalities; reproduced
   all margins and the n ≤ 117 non-violation.
3. **Orchestrator cross-check:** `python ..\..\verify_kills.py` — section `[154]`
   rebuilds lollipop(72,72) from the construction description alone and re-asserts
   8mW² > n⁷ and 8mW² > n⁵(n−1)².
4. **Mutation tests** (inside `check_graffiti154.py`, must all be rejected — and are):
   lollipop(47,70) (n = 117) claimed to violate DP; (48,70) claimed to violate N2;
   (72,72) with W corrupted by −1; degenerate path-only P₁₄₄ and clique-only K₁₄₄
   claimed as violators; corrupted closed form W+1 vs BFS.
5. **Hostile referee:** Codex (GPT-5.5, full shell+network) — verdict **KILL
   CONFIRMED**, verbatim in `CODEX_VERDICT.txt`; it independently re-rendered the WoW
   PDF pages, re-derived the inequalities, re-ran the family scan with degeneracies,
   audited Checker A for acceptance bugs (found none fatal), and ran its own live
   openness search. Its four nits (a bogus `fms1993.pdf` artifact, one over-strong
   check label, "smallest found" non-uniqueness, venue precision IASE-workshop-at-ECAI)
   were all fixed or dispositioned in this bundle (see the disposition section of
   `CODEX_VERDICT.txt`).

---

## 6. Extension findings (beyond the discovery-session claim record)

1. **Minimal instances are correct but not unique** (the claim record said "smallest
   found", which was accurate): four DP violators at n = 118 and two both-convention
   violators at n = 120, listed in §3; nothing below n = 118 in the family.
2. **Convention robustness is structural:** every N2 violator is a DP violator
   (n⁷ > n⁵(n−1)²), so the weaker distinct-pairs threshold is the binding one and the
   "average distance" ambiguity cannot save the conjecture at (50,70)/(72,72).
3. **MAD side-claim upgraded from numerical to proven:** non-violation under the
   mean-absolute-deviation reading at all three instances is now proven in exact
   arithmetic two independent ways (Sturm-certified rational energy enclosures via the
   equitable quotient + the −1 eigenvalue of multiplicity t−2, verified by explicit
   eigenvectors and both trace identities; and an exact-rational Koolen–Moulton bound),
   in addition to mpmath dps = 60 sign separation (gaps +2.95 to +4.14).
4. **Convention provenance independently re-fetched:** FMS 1993 (Academia.edu mirror)
   pins both the distinct-pairs mean distance and the RMS "deviation"; WoW's own conj.
   536 comment pins distinct-pairs as the document's usage.
5. **Venue correction:** arXiv:2409.18626 was published at the **IASE 2025 workshop at
   ECAI 2025** (archived `rc-ecai2025.pdf`, identical Table 1 row for 154), not
   main-track ECAI as the discovery-session record implied.

---

## 7. Openness re-check (Gate-5 kill-check, dated 2026-06-11)

Searches run this session, independent of the Gate-4 searches earlier the same day:

1. Web search `Graffiti conjecture 154 "deviation of eigenvalues" refuted OR
   counterexample` — only the known corpus (FMS 1993; BDF 1995; R–C arXiv:2409.18626;
   Vito–Stefanus AMCS 2023). No refutation of 154.
2. Web search `Fajtlowicz "Written on the Wall" conjecture 154 average distance
   eigenvalues` — related distance-spectra literature only; nothing on 154.
3. Web search `refutation Graffiti spectral conjecture 2025 2026 lollipop "standard
   deviation" eigenvalues "average distance"` — R–C line of work refutes 197/289 etc.;
   nothing touches 154.
4. arXiv abstract page for 2409.18626 (fetched 2026-06-11): still v1 (27 Sep 2024);
   abstract claims only conjecture 197 as the newly refuted one; 154 remains "O" in
   Table 1.
5. Semantic Scholar citation graph of arXiv:2409.18626: 4 citing works (Angileri et
   al., Machine Learning 2025, Brouwer's conjecture; Taieb–Roucairol–Cazenave et al.,
   LION 2025, maximum Laplacian eigenvalue, + its preprint; "Spectral Graph Theory
   Conjecture Generation"). None mentions conjecture 154 or eigenvalue deviation.
6. arXiv API queries: recent math.CO papers matching "Graffiti" (latest 2025-09-06, a
   graph-energy SDP paper — unrelated); `all:"Written on the Wall" AND all:Fajtlowicz`
   → 0 results; `abs:"conjecture 154"` → 0 results.

**Conclusion: no prior or concurrent refutation of Graffiti Conjecture 154 exists in
the literature as of 2026-06-11. The kill stands.**

---

## 8. What this does not show

- **It does not refute the mean-absolute-deviation reading.** No surviving source
  defines "deviation" next to conjecture 154 itself. If Graffiti's "deviation" meant
  MAD (= energy/n here, since the spectral mean is 0), the lollipop family does **not**
  violate the conjecture — proven in exact arithmetic at all three instances (§5–6).
  The kill is claimed only under the standard-deviation reading, which is the reading
  of FMS 1993 and of every known machine formalization. This residual interpretive risk
  is documented, quantified, and confined.
- It does not determine the minimum order of a counterexample over **all** connected
  graphs — only within the lollipop family (n = 118 / 120); a smaller non-lollipop
  violator may exist between 51 and 117 (the prior search horizon was 50).
- It says nothing about the neighboring WoW conjectures (150, 152, 153, 155) or about
  Laplacian/distance-matrix variants of 154; conjecture 143 (variance of *positive*
  eigenvalues) is a separate kill with its own bundle (`graffiti-143`).
- It does not claim the lollipop family is the extremal violator class — dumbbells also
  work, and no optimality is asserted.

---

## Publication grouping

Bundle with **`graffiti-143`** (variance of positive eigenvalues ≤ size/average
distance, dumbbell counterexamples) as the natural unit: the **two Graffiti spectral
kills** share the same frozen source (WoW July 2004 + the same glyph-decode chain), the
same openness baseline (R–C ECAI/IASE 2025 Table 1), the same clique-plus-path
counterexample mechanism (std dev / variance grows as √(2m/n) while n/ℓ stays bounded),
and the same convention-provenance work (FMS 1993, R–C code audit) — a single short
paper, e.g. "Counterexamples to two spectral conjectures of Graffiti". Distinct sibling
bundles in this factory: the three solubilizer kills (`solubilizer-a1`,
`solubilizer-a13`, `solubilizer-a16`) and the two TxGraffiti-family kills
(`davila-conj9`, `pandey-parity`).
