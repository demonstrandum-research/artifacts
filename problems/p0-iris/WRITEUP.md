# Refutation of IRIS Conjecture 6.1 ("NuevaMirada"): counterexamples among simple 3-polytopes with 10 faces

Campaign: `problems/p0-iris` (Demonstrandum). Date of this write-up and of the final kill-check: **2026-06-11**.

---

## 1. Claim (FRAMEWORK.md section 9 standard)

> **Result.** Conjecture 6.1 ("NuevaMirada") of the IRIS paper — *"If P is a simple 3-polytope with
> face vector (p3, p4, . . . , pm), such that sum_{k>=7} pk >= 3, then
> p6 >= 39/20 + p3/2 - p5/4 - sum_{k>=7} pk."* (verbatim from the camera-ready PDF,
> OpenReview id v6Ulp3U1ZT; pk = number of k-gonal 2-faces of P) — is **false as printed**.
> There are exactly **5** counterexamples with 10 faces, and none with fewer (10 faces is minimal);
> the complete census of counterexamples among all simple 3-polytopes with n <= 16 faces is
> 0, 0, 0, 0, 0, 0, 5, 27, 108, 357, 1149, 3766, 12078 for n = 4..16 (17,490 in total).
> The smallest counterexamples have p6 = 0 against a conjectured lower bound of 1/5; the cleanest
> has face vector p3 = 4, p5 = 3, p7 = 3 (only triangles, pentagons and heptagons).
>
> **Status before this work.** Open. The paper (Davila, De Loera, Eddy, Fang, Lu, Yang;
> ICML 2025 Workshop on AI for Math, non-archival poster) presents Section 6 as "formally stating
> several open conjectures"; the OpenReview forum (https://openreview.net/forum?id=v6Ulp3U1ZT,
> "Published: 09 Jul 2025, Last Modified: 25 Jul 2025") carries no comments, errata or revisions;
> dated openness sweeps at selection time (scouting + Codex GPT-5.5 hostile referee, 2026-06-11,
> recorded in `scouting/scout-results.json`, entry `iris-p6-polytope`) and again at write-up time
> (Section 6 below, same date) found no refutation, erratum, withdrawal or follow-up anywhere.
>
> **Artifact.** `certificates/cex10.txt` — 5 lines, each `<n> <rotation>`: a plantri ascii (`-a`)
> rotation system of a planar triangulation T on n = 10 vertices whose planar dual G (a 3-connected
> cubic simple planar graph; by Steinitz the graph of a simple 3-polytope with 10 faces and
> 16 vertices) violates the conjecture. The five lines are reproduced inline in Section 3.
>
> **Verification.** Checker A (Python, `verification/checker_py/verify_counterexample.py`, written
> in the vetting phase independently of the search code); Checker B (Rust,
> `verification/checker_rs/`, written by a separate agent from the specification only, without
> consulting Checker A). Both build the dual explicitly and re-prove planarity, 3-regularity and
> 3-connectivity from scratch; both accept all 5 certificates (fresh re-run 2026-06-11).
> Mutation testing: 33 targeted corruptions, including 11 valid triangulations failing only the
> mathematical conditions, all rejected by both checkers (`verification/mutation_report.md`).
> Independent re-derivation: a from-scratch filter on a freshly downloaded plantri 5.8 reproduced
> the entire census n = 4..16, cross-checked the generation totals against OEIS A000109, verified
> the dual-degree equivalence by explicit dual construction, and matched the 5 minimal violations
> to the certificates 5/5 with zero extras by canonical-form isomorphism
> (`verification/rederivation/counts.log`).
>
> **Openness re-check.** 2026-06-11 (same day as claim): 8 web searches + OpenReview forum and
> revisions pages + arXiv math.CO recent listing; zero hits for any refutation, erratum,
> withdrawal, comment, or citing follow-up. Full query log in Section 6.
>
> **What this does not show.** This refutes a machine-generated conjecture as printed in a
> non-archival workshop poster — modest mathematical weight (erratum-note scale). Barnette's 1969
> theorem is untouched. The integer-rounded weakening p6 >= floor(RHS) survives the entire census
> to 16 faces, as does the same inequality with constant 19/20 in place of 39/20. Nothing is
> claimed for polytopes with >= 17 faces, and nothing about the paper's other conjectures — in
> particular the body's 5/3 zero-forcing variant remains open. Details in Section 7.

---

## 2. The conjecture: frozen statement and provenance

Source of record: the camera-ready PDF on OpenReview, id **v6Ulp3U1ZT** —
"Inequality Ranking and Inference System (IRIS): Giving Mathematical Conjectures Numerical Value",
Randy Davila, Jesus A. De Loera, et al. (Eddy, Fang, Lu, Yang), ICML 2025 Workshop AI4MATH
(non-archival workshop poster; there is no arXiv version).
URL: https://openreview.net/forum?id=v6Ulp3U1ZT (PDF: https://openreview.net/pdf?id=v6Ulp3U1ZT).
Accessed and quoted verbatim at selection time and again on 2026-06-11.

> **Conjecture 6.1 (NuevaMirada).** If P is a simple 3-polytope with face vector
> (p3, p4, . . . , pm), such that sum_{k>=7} pk >= 3, then
> p6 >= 39/20 + p3/2 - p5/4 - sum_{k>=7} pk.

Conventions, resolved at vetting (`scouting/scout-results.json`, entry `iris-p6-polytope`):

- pk = number of k-gonal 2-faces of P. Confirmed by the paper itself: Section 5.1, Table 2 context
  and the Figure 5 caption restate the same inequality with the identical constants
  39/20, 1/2, -1/4, -1.
- The inequality is over the reals as printed (no rounding). Since every pk is an integer and
  20 * RHS = 39 + 10*p3 - 5*p5 - 20*S is an integer (S := sum_{k>=7} pk), a counterexample is
  exactly: **S >= 3 and 20*p6 < 39 + 10*p3 - 5*p5 - 20*S**, checked in exact integer arithmetic.
- By Steinitz's theorem, simple 3-polytopes correspond exactly to 3-connected cubic simple planar
  graphs; by Whitney's theorem the planar embedding of a 3-connected planar graph is
  combinatorially unique, so the face vector is well defined from the graph.
- Context in the paper: Theorem 5.1 quotes Barnette (1969):
  p6 >= 2 + p3/2 - p5/2 - sum_{k>=7} pk under the same hypothesis. Conjecture 6.1 strictly
  strengthens Barnette whenever p5 > 0. The conjecture was produced by IRIS's convex-hull fitting
  over 496 curated instances (437 from the Coolsaet-Goedgebeur planar-graph database + 59 random),
  of which only 171 satisfy the hypothesis S >= 3.

The hostile-referee cross-examination at vetting (Codex GPT-5.5, 2026-06-11, verdict recorded
verbatim in the scouting entry) specifically attacked and dismissed the two escape routes:
a plantri-vs-paper convention mismatch ("That fails") and an intended-rounding defense
("The paper states a real inequality, not floor(RHS)").

## 3. The counterexamples (certificates, inline)

File: `C:\Users\jacks\source\repos\maths\problems\p0-iris\certificates\cex10.txt`.
Each line is `<n> <rotation>` in plantri ascii (`-a`) format: n comma-separated adjacency lists in
rotation (cyclic embedding) order, vertices `a`, `b`, `c`, ...; the line encodes a planar
**triangulation** T on n = 10 vertices. The counterexample polytope graph G is the **planar dual**
of T (16 vertices, 24 edges, 10 faces): the k-gonal faces of G are exactly the degree-k vertices
of T. Both checkers construct G explicitly rather than trusting this equivalence.

```
10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
10 bcdefghi,aigdc,abd,acbgjfe,adf,aedjg,afjdbih,agi,ahgb,dgf
10 bcdefghi,aijc,abjifed,ace,adcf,aecig,afih,agi,ahgfcjb,bic
10 bcdefghi,aihfjdc,abd,acbjfe,adf,aedjbhg,afh,agfbi,ahb,bfd
10 bcdef,afghc,abhgied,ace,adcigjf,aejgb,bfjeich,bgc,cge,egf
```

Verified face vectors of the dual polytopes and the exact violation
(RHS = 39/20 + p3/2 - p5/4 - S; violation iff 20*p6 < 20*RHS):

| # | face vector of G                 | S | RHS (exact) | p6 | 20*p6 | 20*RHS = 39+10p3-5p5-20S |
|---|----------------------------------|---|-------------|----|-------|---------------------------|
| 1 | p3=3, p4=3, p5=1, p7=2, p8=1     | 3 | 1/5         | 0  | 0     | 4                         |
| 2 | p3=4, p4=1, p5=2, p7=2, p8=1     | 3 | 9/20        | 0  | 0     | 9                         |
| 3 | p3=3, p4=3, p5=1, p7=2, p8=1     | 3 | 1/5         | 0  | 0     | 4                         |
| 4 | p3=5, p5=1, p6=1, p7=2, p8=1     | 3 | 6/5         | 1  | 20    | 24                        |
| 5 | p3=4, p5=3, p7=3                 | 3 | 1/5         | 0  | 0     | 4                         |

Every line satisfies the hypothesis (S = 3) and strictly violates the conjectured bound. All five
also satisfy Barnette's theorem (lines 1-4 with equality), and all satisfy the Euler p-vector
identity sum_k (6-k) pk = 12 — both checked as built-in sanity cross-checks. Lines 1 and 3 share a
face vector but are non-isomorphic (distinct canonical forms; see Section 5.3).

## 4. Census (complete to 16 faces)

Exhaustive sweep over **all** simple planar triangulations on n vertices (plantri's default class
`-c3m3`: 3-connected planar triangulations, whose duals are exactly the simple 3-connected planar
cubic graphs, i.e. the graphs of simple 3-polytopes with n faces), n = 4..16:

| n (faces of P) | triangulations (= simple 3-polytopes) | hypothesis S >= 3 | violations of Conj. 6.1 |
|----------------|----------------------------------------|--------------------|--------------------------|
| 4              | 1                                      | 0                  | 0                        |
| 5              | 1                                      | 0                  | 0                        |
| 6              | 2                                      | 0                  | 0                        |
| 7              | 5                                      | 0                  | 0                        |
| 8              | 14                                     | 0                  | 0                        |
| 9              | 50                                     | 0                  | 0                        |
| 10             | 233                                    | 16                 | **5**                    |
| 11             | 1,249                                  | 266                | 27                       |
| 12             | 7,595                                  | 3,120              | 108                      |
| 13             | 49,566                                 | 30,145             | 357                      |
| 14             | 339,722                                | 259,193            | 1,149                    |
| 15             | 2,406,841                              | 2,087,267          | 3,766                    |
| 16             | 17,490,241                             | 16,264,573         | 12,078                   |

- Generation totals match OEIS **A000109** (simple planar triangulations) exactly for all n,
  a full-coverage cross-check of the enumeration.
- **Minimality:** zero violations for all n <= 9, so the five 10-face polytopes are the smallest
  counterexamples. (For n <= 7 the hypothesis S >= 3 is unsatisfiable outright.)
- Total: 17,490 counterexamples with at most 16 faces. The violating triangulation lines for
  n = 10..13 are stored in `verification/rederivation/violations_n{10..13}.txt`; the n = 14..16
  files (1,149 / 3,766 / 12,078 lines) are regenerable in seconds (Section 5.3 command).
- **Margin analysis** (computed 2026-06-11 from the violation files): the maximum of
  20*(RHS - p6) over all 17,490 violations is 9 (n <= 13), 14 (n = 14, 15), 19 (n = 16) — always
  < 20. Hence **no** polytope in the census violates the integer-rounded variant
  p6 >= floor(RHS) (equivalently: the inequality with 39/20 weakened to 19/20 survives to
  16 faces). See Section 7.

Discovery pipeline (corroboration, not load-bearing): `code/iris_filter.c`, a plantri PLUGIN
filter (degree counts of the triangulation = face vector of the dual; exact integer test), run via
`code/run_iris.sh` against plantri 5.5. The independent re-derivation (Section 5.3) used a fresh
plantri 5.8 and a from-scratch filter.

## 5. Verification procedure

A hostile skeptic needs only one certificate line from Section 3 plus either checker; everything
else is redundancy. Acceptance semantics are exactly those used in the mutation tests.

### 5.1 Checker A — Python (dependency-free)

Path: `C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_py\verify_counterexample.py`
(~150 lines, standard library only; written during vetting, independently of the plantri filter).

Per line it: parses the rotation system; asserts simplicity and adjacency symmetry; traces faces
and asserts every face is a triangle and Euler V - E + F = 2 (genus-0, so the rotation system is a
planar embedding); builds the dual G explicitly with its rotation system; asserts G is 3-regular,
3-connected (brute force over all single- and pair-deletions), and planar by the same
Euler/face-trace criterion; computes the p-vector of G from traced face sizes; asserts the
hypothesis S >= 3; and checks 20*p6 < 39 + 10*p3 - 5*p5 - 20*S in exact integers, plus the
Barnette and sum(6-k)pk = 12 sanity identities.

Command (one certificate line as the single argument):

```
python "C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_py\verify_counterexample.py" "10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf"
```

**ACCEPT iff stdout contains `COUNTEREXAMPLE CONFIRMED`.** Caveat (documented in the mutation
report): this checker exits 0 even when printing `not a counterexample`; the string, not the exit
code, is the acceptance signal.

### 5.2 Checker B — Rust (independent implementation)

Path: `C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\`
(no dependencies outside std; i64 with overflow checks enabled in release; written by a separate
agent from the specification only, without consulting Checker A — see its README.md for the full
per-line check list, which includes dual simplicity: no loops and no multi-edges in G).

```
cargo build --release --manifest-path "C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\Cargo.toml"
"C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\target\release\checker_rs.exe" "C:\Users\jacks\source\repos\maths\problems\p0-iris\certificates\cex10.txt"
```

**ACCEPT iff exit code 0 and `COUNTEREXAMPLE CONFIRMED` is printed for every line.** Any failed
check prints a reason and exits nonzero.

**Fresh run, 2026-06-11 (write-up day):** Checker B on `certificates/cex10.txt` -> 5 x
`COUNTEREXAMPLE CONFIRMED`, exit 0; Checker A on each of the 5 lines -> `COUNTEREXAMPLE CONFIRMED`
each time, with face vectors identical between checkers and matching Section 3's table.

### 5.3 Independent re-derivation (full census, from scratch)

Directory: `verification\rederivation\` (log: `counts.log`). All code there was written from
scratch without reading or running `code/iris_filter.c` / `code/run_iris.sh`. Generator: plantri
5.8, downloaded fresh from https://users.cecs.anu.edu.au/~bdm/plantri/plantri58.tar.gz
(sha256 `e78a944116fec9f2c9f5e484206276cc2b0043bae803e9815f4b2683614629b8`), built in WSL Ubuntu
with `gcc -O3`. Exact invocation per n: `plantri -a <n> | rederive_filter`, driven by

```
./run_rederive.sh <plantri_binary> <outdir> 4 16
```

Results: the census table of Section 4 in full, including the OEIS A000109 totals match.
Additionally:

- **Dual-degree equivalence verified, not assumed:** `verify_dual.py` builds the planar dual
  face-by-face from the rotation system for all 14 triangulations at n = 8 and all 5 violating
  triangulations at n = 10, traces the dual's faces, and confirms each dual face surrounds a
  unique primal vertex with face size = primal degree (19/19 PASS).
- **Certificate matching:** `match_certs.py` canonicalizes embeddings (lexicographic-minimum BFS
  code over all starting darts and both orientations; a complete isomorphism invariant for
  3-connected planar graphs by Whitney). Result: the 5 re-derived minimal violations match
  `certificates/cex10.txt` **5/5, with zero extra violations** at n = 10.

### 5.4 Mutation testing of both checkers

Report: `verification\mutation_report.md` (2026-06-11). 33 mutants across 8 categories:
single-character adjacency edits, rotation swaps (same graph, corrupted embedding), deleted or
duplicated darts, asymmetric adjacency, wrong headers, parser garbage, and — critically —
**11 structurally perfect triangulations** that fail only the mathematics: 7 whose dual polytope
fails the hypothesis (tetrahedron through octagonal bipyramid, including the S = 2 boundary case)
and 4 whose dual satisfies the hypothesis but not the violation (including `g4` with margin
exactly 1: 20*p6 = 20 vs RHS-side 19).

**All 33 mutants rejected by both checkers; all 5 originals accepted by both.** A mirrored
embedding of certificate line 1 (control, a genuine counterexample) is accepted by both,
confirming the embedding-corruption rejections are not orientation pickiness. The category e/g
results demonstrate the mathematical checks, not just the parser, are load-bearing.

## 6. Openness evidence and final kill-check (2026-06-11)

**Selection-time evidence** (recorded in `scouting/scout-results.json`, entry `iris-p6-polytope`,
dated 2026-06-11): OpenReview forum shows "Published: 09 Jul 2025, Last Modified: 25 Jul 2025"
with no comments or errata, and the PDF presents Section 6 as "formally stating several open
conjectures"; WebSearch sweeps for {"NuevaMirada" + polytope}, {IRIS 39/20 p6 counterexample
refuted}, {Davila De Loera IRIS cited/resolved}, {p6 Barnette refinement counterexample 2026}
returned zero relevant hits; OpenAlex has no record of the paper (no citation trail); Codex
(GPT-5.5, hostile-referee mode with network access) independently searched Google Scholar, arXiv
and domain-limited sources and reported "no public prior refutation or corrected newer version as
of my searches on June 11, 2026".

**Fresh kill-check at write-up time (this document), 2026-06-11.** Queries and results:

| # | Query / fetch | Result |
|---|---------------|--------|
| 1 | WebSearch: `IRIS conjecture "NuevaMirada" counterexample polytope` | Only Hirsch-conjecture literature; nothing on IRIS/NuevaMirada |
| 2 | WebSearch: `"Inequality Ranking and Inference System" IRIS conjecture refuted counterexample 2026` | No relevant hits (unrelated 2026 Erdos-unit-distance news only) |
| 3 | WebSearch: `Davila "De Loera" IRIS conjectures simple 3-polytope p6 Barnette` | Finds the paper's own OpenReview PDF + unrelated Barnette-Hamiltonicity literature; no refutation |
| 4 | WebSearch: `"NuevaMirada"` | Only unrelated Spanish-language media/film entities; no mathematical usage |
| 5 | WebSearch: `arXiv counterexample "Conjecture 6.1" IRIS automated conjecturing polytope face vector p6` | No matches |
| 6 | WebSearch: `"v6Ulp3U1ZT" OR "IRIS: Giving Mathematical Conjectures" comment refutation erratum` | Only the paper itself; no comments/errata reported |
| 7 | WebSearch: `Davila De Loera Eddy Fang Lu Yang IRIS conjectures 2026 cited follow-up` | No follow-up or citing refutation found |
| 8 | WebSearch: `counterexample simple 3-polytope hexagonal faces conjecture 2025 2026 "39/20"` | Nothing relevant |
| 9 | WebFetch: https://openreview.net/forum?id=v6Ulp3U1ZT | "Published: 09 Jul 2025, Last Modified: 25 Jul 2025"; **no comments, replies, errata or notes displayed** |
| 10 | WebFetch: https://openreview.net/revisions?id=v6Ulp3U1ZT | Page is JS-rendered, revision list not retrievable; the forum's last-modified date (25 Jul 2025) stands as the operative evidence |
| 11 | WebFetch: https://arxiv.org/list/math.CO/recent (June 10-11, 2026 listing) | No paper mentioning IRIS, NuevaMirada, or a p6/face-vector counterexample |

**Kill-check verdict: NEGATIVE — no refutation, erratum, correction, withdrawal, or even a
comment on Conjecture 6.1 has been posted anywhere findable as of 2026-06-11.** The conjecture
stood publicly unrefuted at claim time. (Caveat: the refutation costs milliseconds of plantri
time; openness of this kind is fragile, which is why the claim is being filed the same day.)

## 7. What this does not show

1. **Scope and weight.** This refutes a conjecture *as printed* in a non-archival ICML 2025
   workshop poster, generated by IRIS's convex-hull fitting over 496 instances (171 meeting the
   hypothesis). No human-named conjecture falls. The appropriate genre is an erratum-scale note /
   OpenReview comment plus a cautionary datapoint for ML conjecture pipelines: the conjecture
   dies at 10 faces, i.e. within seconds of exhaustive stress-testing that the pipeline did not
   perform. We claim modest mathematical weight, nothing more.
2. **Barnette's theorem is untouched.** All 17,490 counterexamples satisfy Barnette's bound
   p6 >= 2 + p3/2 - p5/2 - S (as they must; it is a theorem). Four of the five minimal ones meet
   it with equality. The failure is specific to IRIS's strengthened constants (the -p5/4 term and
   the 39/20 constant).
3. **The integer-rounded variant is NOT refuted.** As printed the inequality is over the reals,
   and the hostile review explicitly rejected rounding as a defense of the printed statement.
   Nevertheless: every violation in the census has 20*(RHS - p6) <= 19 < 20, so **no** polytope
   with <= 16 faces violates p6 >= floor(39/20 + p3/2 - p5/4 - S); equivalently, weakening the
   constant 39/20 to 19/20 yields an inequality with no counterexample up to 16 faces. If the
   authors amend the conjecture in either way, our objects say nothing against the amended form.
   (The maximum margin grows with n — 9/20 at n <= 13, 14/20 at n = 14..15, 19/20 at n = 16 — so
   the floored variant may well fail at larger n, but we have not shown that.)
4. **Nothing about the paper's other conjectures**, in particular the zero-forcing family. For
   the record, status per the vetted scouting intel (`scout-results.json`, entry
   `iris-62-zeroforcing-domination`, dated 2026-06-11): printed Conjecture 6.2
   (Z(G) <= (5/4)*gamma(G) + 4/3 for connected G with max degree <= 3) is refuted by K3,3
   (Z = 4 > 23/6), and printed Conjecture 6.3 (Z <= 2*gamma, no Kn exclusion) by K4 — but the
   paper's own body (Section 5.2, Figure 6, Table 3) states the intended **5/3 variant**
   Z(G) <= (5/3)*gamma(G) + 4/3, of which the printed 5/4 is almost certainly a transcription
   typo. **That 5/3 variant remains open as of 2026-06-11**: it has no counterexample among all
   112 connected subcubic graphs on <= 7 vertices, K4 attains it with equality, and
   Davila-Henning (J. Comb. Optim. 41:553-577, 2021) proved Z <= 2*gamma for connected cubic
   G != K4, so any cubic counterexample to the 5/3 form needs gamma >= 5. The present polytope
   result has no bearing on any of this.
5. **Census horizon.** The exhaustive sweep stops at 16 faces. Violation counts for n >= 17 are
   not determined here (an extension to n = 20 is ~4 CPU-hours at measured plantri rates but was
   not run).
6. **No structural theorem.** We observe (vetting-phase window analysis, consistent with the
   data) that a violation with p5 = 1 forces p3 odd and p6 = (p3+3)/2 - S exactly, i.e. is
   Barnette-tight; this is reported as an observation about the found objects, not claimed as a
   classified characterization of all counterexamples.

## 8. Abstract (150 words, for an arXiv note / OpenReview comment)

> We refute Conjecture 6.1 ("NuevaMirada") of the IRIS automated-conjecturing paper (Davila,
> De Loera, Eddy, Fang, Lu, Yang; ICML 2025 AI4Math workshop), which asserts that every simple
> 3-polytope with at least three faces of size 7 or more satisfies
> p6 >= 39/20 + p3/2 - p5/4 - sum_{k>=7} pk, where pk counts the k-gonal faces. Exhaustively
> generating all simple 3-polytopes with at most 16 faces (as duals of plantri-generated planar
> triangulations), we find that the conjecture first fails at 10 faces: there are exactly five
> 10-face counterexamples, and 17,490 in total through 16 faces. The smallest have p6 = 0 against
> a conjectured bound of 1/5; the cleanest has face vector p3 = 4, p5 = 3, p7 = 3. All
> certificates pass two independent, mutation-tested checkers (Python and Rust), and the census
> was re-derived independently. Barnette's 1969 bound is untouched, and the integer-rounded
> weakening p6 >= floor(RHS) survives the entire census.

## 9. File manifest

All paths under `C:\Users\jacks\source\repos\maths\problems\p0-iris\`:

| Path | Role |
|------|------|
| `certificates\cex10.txt` | The 5 minimal counterexample certificates (load-bearing artifact) |
| `verification\checker_py\verify_counterexample.py` | Checker A (Python, dependency-free) |
| `verification\checker_rs\` (`src\main.rs`, `README.md`, `Cargo.toml`) | Checker B (Rust, independent; README documents semantics and results) |
| `verification\mutation_report.md` | Mutation-test report: 5/5 originals accepted, 33/33 mutants rejected by both checkers |
| `verification\mutation_work\` | Mutation generator/driver and mutant lines |
| `verification\rederivation\counts.log` | Independent re-derivation log (plantri 5.8, census, OEIS cross-check, dual verification, canonical matching) |
| `verification\rederivation\rederive_filter.c`, `run_rederive.sh`, `verify_dual.py`, `match_certs.py` | Re-derivation code (written without reading the discovery code) |
| `verification\rederivation\violations_n10.txt` .. `violations_n13.txt` | Census violation lines, n = 10..13 (n = 14..16 regenerable in seconds) |
| `code\iris_filter.c`, `code\run_iris.sh` | Discovery pipeline (plantri PLUGIN filter; corroboration, not load-bearing) |
| `WRITEUP.md` | This document |

External: `C:\Users\jacks\source\repos\maths\scouting\scout-results.json` (entries
`iris-p6-polytope` and `iris-62-zeroforcing-domination`: statement provenance, openness evidence,
Codex hostile-referee verdicts, all dated 2026-06-11);
`C:\Users\jacks\source\repos\maths\FRAMEWORK.md` (claim standard, Section 9).
