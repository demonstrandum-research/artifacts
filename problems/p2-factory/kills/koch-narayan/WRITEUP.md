# Refutation of Conjecture 1 of arXiv:2511.01719 (Koch–Narayan, "Maximal bipartite graphs with a unique minimum dominating set")

**Slug:** `koch-narayan` · **Status:** verified kill (Gate 4 passed 2026-06-11; Gate 5 this document, 2026-06-12). Bundle:
`C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\koch-narayan\`

---

## Abstract (~120 words)

We refute Conjecture 1 of G. Koch and D. Narayan, *Maximal bipartite graphs
with a unique minimum dominating set* (arXiv:2511.01719, v1, Nov 2025): a
bipartite graph without isolated vertices, with domination number γ ≥ 2,
a unique minimum dominating set, and n ≥ 3γ vertices, has at most m(n, γ)
edges. The smallest counterexample — unique up to isomorphism, found by
exhaustive `geng` sweep — has n = 13, γ = 4 and 22 > 21 = m(13,4) edges; it
exploits a vertex adjacent to two same-side dominators, a feature absent
from the paper's tightness construction. An explicit "unbalanced-split"
family extends the failure (26 verified instances, γ = 4, 5, 6, n ≤ 26),
indicating failure for every γ ≥ 4. The printed bound has a sign typo in Φ;
both readings are violated. Verification: two clean-room exact checkers,
mutation tests, hostile Codex recomputation. The conjecture is exhaustively
true for n ≤ 12, and the γ = 2 (paper-proven) and γ = 3 strips survive.

---

## Result (claim-standard form, FRAMEWORK.md §9)

> **Result.** Conjecture 1 of arXiv:2511.01719 is **FALSE**. Verbatim
> (frozen 2026-06-11 from the arXiv v1 LaTeX source, `PaperDraft.tex`
> lines 145–148, in this bundle and in `../../attacks/koch-narayan/src/`):
>
> *"Let G be a bipartite graph without isolated vertices with order n and
> dominating number γ. Let G have a unique minimum dominating set. If
> γ ≥ 2 and n ≥ 3γ, then the size of G, s(G), is bounded **above** by*
>
> m(n,γ) = 2γ + 2⌈γ/2⌉⌊γ/2⌋ + min{n−3γ, 2⌈γ/2⌉−⌊γ/2⌋+1}·(2⌈γ/2⌉+1)
> + Σ_{i=1}^{Φ} ( (2⌈γ/2⌉+1) + ⌈i/2⌉ )
>
> *where Φ(n,γ) = max(0, n−3γ−2⌈γ/2⌉−⌊γ/2⌋+1)."*
>
> The printed Φ contains a sign typo (see "Both Φ readings" below); the
> refutation is **reading-independent**: every certificate violates the
> bound under both the literal printed Φ and the construction-consistent
> (typo-corrected) Φ' = max(0, n−3γ−2⌈γ/2⌉+⌊γ/2⌋−1), which coincide (both 0)
> at every certificate cell. The smallest counterexample has n = 13, γ = 4,
> s(G) = 22 > 21 = m(13,4); five further certificates cover γ = 4, 5, 6 up
> to n = 20, all with exhaustively certified γ and unique minimum dominating
> set. The violations are strict, as required against a non-strict ≤.
>
> **Status before this work.** Open. arXiv:2511.01719 was still v1
> (submitted 2025-11-03) with **zero citing papers** (Semantic Scholar API,
> checked 2026-06-12); the paper proves only the γ = 2 and n = 3γ cases and
> explicitly leaves the general bound as Conjecture 1 ("the bipartite
> bound"). No refutation, follow-up, or revision found at selection time
> (2026-06-11) or at the fresh kill-check (2026-06-12, below).
>
> **Artifact.** Six certificate JSON files in this bundle —
> `certificate_13_4.json` (primary, smallest), `certificate_14_4.json`,
> `certificate_15_4.json`, `certificate_15_4_max.json`,
> `certificate_18_5.json`, `certificate_20_6.json` — each with explicit
> edge list and graph6 string; the family certificates also carry labeled
> constructions and the claimed unique minimum dominating set. The full
> n = 13 certificate is reproduced inline below.
>
> **Verification.** Two independent clean-room checkers, both pure Python 3
> exact integer arithmetic, no third-party libraries, no attacker code
> reused: `independent/indy_check.py` (Gate-4 first pass; rebuilds the
> n = 13 graph from its textual description, decodes graph6 with its own
> decoder, exhaustive domination enumeration over all C(n,k) subsets) and
> `independent/cleanroom_check.py` (Gate-4 second pass, written from
> scratch by a different agent; same conclusions). Both anchor the formula
> transcription against the paper's own values (m(6,2)=6, m(7,2)=9, the
> γ=2 closed form n(n−2)/4 / (n−1)²/4 for n = 6..40, m(10,3)=15, the n=3γ
> simplification for γ = 2..11), under both Φ readings. Logs:
> `independent/verify.log`, `independent/cleanroom_verify.log`, both
> regenerated fresh inside this bundle on 2026-06-12. Mutation testing
> (added Gate 5, 2026-06-12): `independent/mutation_tests.py`, 10 targeted
> corruptions of the n = 13 certificate (edge removed → bound met; isolated
> vertex; two non-bipartite edge additions; an edge addition and a rewiring
> that each break MDS uniqueness; wrong γ claim; padded order; duplicate
> edge; out-of-range vertex) — **all REJECTED, pristine ACCEPTED**.
> Attacker-side (Gate 3/4): `checker.py` and `verify2.py` (independent
> second implementation, different algorithm) agree on all 26 family hits;
> the exhaustive sweep used nauty `geng -b -d1` piped through `domfilter.c`
> (C, third implementation of the domination count). Codex (GPT-5.5, xhigh,
> hostile-referee audit, 2026-06-11): see verbatim verdict below.
>
> **Openness re-check.** 2026-06-12 (this document, "Final kill-check"):
> arXiv abs page still v1, Semantic Scholar citationCount = 0, web searches
> for refutations/counterexamples of the bipartite bound found nothing.
>
> **What this does not show.** See final section.

---

## Exact statement and provenance

* **Source:** arXiv:2511.01719 v1 (Garrison Koch, Darren Narayan, Rochester
  Institute of Technology), submitted 2025-11-03. The arXiv LaTeX source
  tarball is `paper.tar.gz` in this bundle; the conjecture is the paper's
  only `\begin{con}` environment, `PaperDraft.tex` lines 145–148, quoted
  verbatim above. "Size" s(G) = number of edges; domination is standard
  closed-neighborhood domination; the paper imposes no connectivity,
  balanced-bipartition, or edge-maximality hypothesis in Conjecture 1
  (confirmed line-by-line by the Codex audit).
* The paper proves the γ = 2 case (their Statement 12 simplification:
  m(n,2) = n(n−2)/4 for n even, (n−1)²/4 for n odd, n ≥ 6) and the n = 3γ
  case, and gives a construction (their Theorem 4) claimed to meet m(n,γ)
  with equality. Conjecture 1 is the general statement; killing it is the
  paper's central open question.

### Both Φ readings

The printed upper limit of the tail sum is

* **literal:** Φ = max(0, n − 3γ − 2⌈γ/2⌉ − ⌊γ/2⌋ + 1).

But the paper's own tightness construction (Theorem 4 Case 3,
`PaperDraft.tex` line 388) adds exactly
|R| = n − (3γ + 2⌈γ/2⌉ − ⌊γ/2⌋ + 1) tail vertices, i.e. it implies

* **corrected:** Φ' = max(0, n − 3γ − 2⌈γ/2⌉ + ⌊γ/2⌋ − 1)

— the printed formula fails to distribute the minus sign over the last two
terms. The readings coincide identically for γ ∈ {2, 3} and at every cell
with n ≤ 15; they first diverge at (n,γ) = (16,4), where the **paper's own
construction produces 37 edges > 31 = m_literal(16,4)**, so the literal
reading is self-refuting and the corrected reading is the only defensible
one. Since Φ' ≥ Φ pointwise, m_corrected ≥ m_literal everywhere; every
certificate below exceeds the **larger** (corrected) bound, hence kills
both readings. At all six certificate cells Φ = Φ' = 0, so the certified
violations do not depend on the typo question at all.

---

## The primary counterexample: n = 13, γ = 4, 22 edges

The unique smallest counterexample (up to isomorphism; see sweep section).
Bipartition **A = {0,…,5}, B = {6,…,12}**; every edge joins A to B.

**Edge list** (22 edges, = `certificate_13_4.json`):

```
(0,6)  (1,7)  (2,8)  (3,8)  (4,9)  (5,9)
(0,10) (2,10) (3,10) (4,10) (5,10)
(1,11) (2,11) (3,11) (4,11) (5,11)
(0,12) (1,12) (2,12) (3,12) (4,12) (5,12)
```

**graph6:** `L??CA?oBDwN_~?`  (decodes to exactly this labeled graph;
verified by two independently written decoders, plus NetworkX in the Codex
audit).

Equivalently, by B-side neighborhoods: 6 → {0}; 7 → {1}; 8 → {2,3};
9 → {4,5}; 10 → {0,2,3,4,5}; 11 → {1,2,3,4,5}; 12 → {0,1,2,3,4,5}.

**Unique minimum dominating set witness:** D = **{0, 1, 8, 9}** (0, 1 ∈ A;
8, 9 ∈ B). N[0] ⊇ {0,6,10,12}, N[1] ⊇ {1,7,11,12}, N[8] = {2,3,8},
N[9] = {4,5,9} — union = V, so D dominates. Exhaustive enumeration of all
C(13,1) + C(13,2) + C(13,3) + C(13,4) = 1092 subsets of size ≤ 4 shows no
dominating set of size ≤ 3 exists and **(0,1,8,9) is the only one of size
4**. Hence γ = 4 ≥ 2, the minimum dominating set is unique, the graph is
bipartite with no isolated vertices (it is even connected, though
Conjecture 1 does not require it), and n = 13 ≥ 12 = 3γ: **every hypothesis
holds**.

**The bound:** m(13,4) = [2·4 + 2·2·2] + [min(13−12, 2·2−2+1)·(2·2+1)] +
[empty tail, Φ = Φ' = max(0,−2) = 0] = 16 + 5 = **21 < 22 = s(G)**, under
both Φ readings.

**Mechanism.** Each dominator keeps two exterior private neighbors
(0: {6,10}; 1: {7,11}; 8: {2,3}; 9: {4,5}) — the unique-MDS skeleton the
paper builds from — but vertex 12 is adjacent to **both** A-side dominators
0 and 1, so it is a private neighbor of nobody. The paper's tightness
construction never creates a vertex adjacent to two same-side dominators;
this extra freedom buys the 22nd edge while uniqueness survives.

**Inline verification snippet** (pure stdlib, runs in ~1 s; executed
2026-06-12, prints `[(0, 1, 8, 9)]` and `s(G) = 22 > m(13,4) = 21`):

```python
from itertools import combinations
n = 13
E = [(0,6),(1,7),(2,8),(3,8),(4,9),(5,9),
     (0,10),(2,10),(3,10),(4,10),(5,10),
     (1,11),(2,11),(3,11),(4,11),(5,11),
     (0,12),(1,12),(2,12),(3,12),(4,12),(5,12)]
assert len(set(E)) == 22 and all(u < 6 <= v for u, v in E)  # simple; bipartite A|B
N = [1 << v for v in range(n)]                              # closed nbhd bitmasks
for u, v in E: N[u] |= 1 << v; N[v] |= 1 << u
assert all(N[v] != 1 << v for v in range(n))                # no isolated vertices
full = (1 << n) - 1
def doms(k):
    out = []
    for S in combinations(range(n), k):
        m = 0
        for v in S: m |= N[v]
        if m == full: out.append(S)
    return out
assert not doms(1) and not doms(2) and not doms(3)          # gamma > 3
print("all minimum dominating sets:", doms(4))              # [(0, 1, 8, 9)] - exactly one
g = 4; cg, fg = 2, 2                                        # ceil(g/2), floor(g/2)
base = 2*g + 2*cg*fg                                        # = 16
mid  = min(n - 3*g, 2*cg - fg + 1) * (2*cg + 1)             # = min(1,3)*5 = 5
assert max(0, n - 3*g - 2*cg - fg + 1) == 0                 # Phi, literal printed reading
assert max(0, n - 3*g - (2*cg - fg + 1)) == 0               # Phi, corrected reading
print("s(G) =", len(E), "> m(13,4) =", base + mid, "(both Phi readings; tail empty)")
```

(The bundled checkers are the authoritative verification; this snippet is
orientation.)

---

## Supplementary family certificates

The systematic failure mechanism is an **unbalanced dominator split**. The
paper's construction splits the γ dominators as evenly as possible between
the two sides (⌊γ/2⌋ / ⌈γ/2⌉), which maximizes the 2pq "base" cross-edges;
but each added bulk vertex earns degree 2q+1, which is maximized by the
*most unbalanced* split p = 1, q = γ−1. Concretely (p = 1): dominator x₁
on side A with private neighbors b₁₁, b₁₂ on side B; dominators y₁,…,y_q on
side B, each with two private neighbors a_{j,1}, a_{j,2} on side A; b₁₁
joined to all 2q a-vertices; and |C| = n − 3γ extra B-side vertices, each
joined to x₁ and all 2q a-vertices (degree 2q+1 each). Then
s = 2γ + 2pq + (n−3γ)(2q+1), the unique MDS is {x₁, y₁,…,y_q}, and for
every γ ≥ 4 some unbalanced split exceeds m(n,γ) on a window of n starting
at 3γ+2 (γ even) resp. about 3γ + (γ−1)/2 (γ odd) — for γ = 3 the
unbalanced and balanced splits tie, which is why the γ = 3 strip survives.

Five supplementary certificates (all re-verified by both clean-room
checkers, fresh logs 2026-06-12; γ exhaustively certified; MDS uniqueness
exhaustively certified; **all violate both Φ readings**, which coincide at
these cells):

| certificate | n | γ | construction | s(G) | m(n,γ) literal | m(n,γ) corrected | unique MDS |
|---|---|---|---|---|---|---|---|
| `certificate_13_4.json` (primary) | 13 | 4 | sporadic (sweep-found) | **22** | 21 | 21 | {0,1,8,9} |
| `certificate_14_4.json` | 14 | 4 | unbalanced p=1, q=3, \|C\|=2 | **28** | 26 | 26 | {0,3,4,5} |
| `certificate_15_4.json` | 15 | 4 | unbalanced p=1, q=3, \|C\|=3 | **35** | 31 | 31 | {0,3,4,5} |
| `certificate_15_4_max.json` | 15 | 4 | sweep-extremal graph | **35** | 31 | 31 | {0,8,9,10} |
| `certificate_18_5.json` | 18 | 5 | unbalanced p=1, q=4, \|C\|=3 | **45** | 43 | 43 | {0,3,4,5,6} |
| `certificate_20_6.json` | 20 | 6 | unbalanced p=2, q=4, \|C\|=2 | **46** | 44 | 44 | {0,1,6,7,8,9} |

Beyond these six, the attack run verified **26 unbalanced-family
violations** (`hits_unbalanced.json`, attacker-level: `checker.py` +
independent-algorithm `verify2.py`) across 20 cells: γ = 4 at n = 14..20,
γ = 5 at n = 18..23, γ = 6 at n = 20..26 — e.g. (16,4): 42 > 37 (corrected)
> 31 (literal). For fixed γ the violations occupy a finite **window** of n
(the bound's tail term ⌈i/2⌉ eventually outgrows the family's per-vertex
gain of 2q+1): formula-level windows for p = 1 are n = 14..22 (γ = 4),
18..28 (γ = 5), 21..37 (γ = 6), 25..43 (γ = 7), 28..52 (γ = 8), with
window length and peak violation (6, 8, 20, 24, 42 edges) growing with γ;
other splits extend the windows (the (20,6) certificate uses p = 2). So
the conjecture does not fail by an isolated accident: the split analysis
predicts a non-empty violation window for **every** γ ≥ 4 (instances
certified with full hypothesis checks at γ = 4, 5, 6; γ = 7, 8 windows
recomputed at formula level this session; general γ analytic only).

---

## How to verify (under a minute; Python 3, stdlib only)

```
cd problems/p2-factory/kills/koch-narayan
python independent/cleanroom_check.py   # expect: OVERALL VERDICT: KILL CONFIRMED, exit 0
python independent/indy_check.py        # expect: OVERALL: KILL CONFIRMED, exit 0
python independent/mutation_tests.py    # expect: MUTATION TESTS: ALL KILLED, exit 0
```

All three re-run fresh in this bundle on 2026-06-12 with exactly those
results (logs `independent/cleanroom_verify.log`, `independent/verify.log`
regenerated in place). The checkers consume only the certificate JSON data
files and their own hard-coded transcription of the conjecture; the n = 13
graph is additionally rebuilt from its textual edge-list description and
cross-checked against an independent graph6 decode.

## Codex hostile audit (verbatim from the Gate-4 record)

Codex (GPT-5.5, xhigh, hostile-referee audit of the clean-room
verification, 2026-06-11, thread 019eb9be-06d6-71d3-b594-ed6b1754a071):
"transcription of Conjecture 1 is exact against PaperDraft.tex (same
hypotheses, same min, same sum i=1..Phi, same printed Phi; 'size' means
edge count, domination is standard closed-neighborhood); no missed
hypothesis excludes the n=13 graph (no connectivity /
balanced-bipartition / maximality / perfect-domination condition in
Conjecture 1). Audited indy_check.py line by line: graph6 decoder bit
order correct (cross-checked via NetworkX), domination enumeration sound
(first non-empty size is gamma; all sets at that size enumerated before
claiming uniqueness), formula matches the paper; only minor robustness
nits, none capable of a false PASS. Independently recomputed with own
scratch code (independent/codex-audit/recompute_n13.py): n=13, |E|=22,
gamma=4, all minimum dominating sets = exactly [(0,1,8,9)], literal Phi=0
and corrected Phi=0, m(13,4)=21 under both readings; supplementary
certificates also recheck. Rescue attempt failed: 'No defensible reading
gives 22 <= m(13,4)' — saving it requires changing the statement
(min->max, an unprinted i=0 summand, Fischermann's general bound, or
total/perfect domination), which are different claims. Final sentence:
'The kill is verified: your clean-room verification is airtight for the
n=13 counterexample, with no substantive caveat beyond "against the
provided PaperDraft.tex statement as written."'"

## Exhaustive sweep: truth for n ≤ 12, minimality of n = 13 (attacker-level, flagged)

The Gate-3 sweep ran nauty `geng -b -d1 -q n lo:hi` (all bipartite graphs
with minimum degree ≥ 1, i.e. exactly the no-isolated-vertices hypothesis,
up to isomorphism) through `domfilter.c` (exact γ by increasing-size
bitmask enumeration; for each graph with γ ≥ 2, n ≥ 3γ and
s > m_corrected(n,γ), count all γ-sized dominating sets and report iff
exactly one). Edge windows `lo:hi` cover every possibly-violating count:
lo = 1 + min_γ m(n,γ) over applicable cells, hi = ⌊n²/4⌋ (bipartite
maximum) — n=9: 11:20, n=10: 16:25, n=11: 21:30, n=12: 17:36, n=13: 22:42,
n=14: 27:49, n=15: 32:56 (this last window omits only edge counts 23..31
of the (15,5) cell — the paper's *proven* n = 3γ case). Within n ≤ 15 the
two Φ readings coincide at every applicable cell, so all conclusions hold
for both. Results (`sweep.log`, ~120M graphs processed):

* **n ≤ 12: zero violations** — combined with the paper's own γ = 2 proof
  (covering n = 6, 7, 8, where γ = 2 is the only cell), Conjecture 1 is
  **true for all n ≤ 12**.
* **n = 13: exactly one violating graph up to isomorphism** — the primary
  certificate above. The smallest counterexample, and it is unique.
* True extremal values vs the conjectured bound: s_max(13,4) = 22 vs 21,
  s_max(14,4) = 28 vs 26, s_max(15,4) = 35 vs 31 (72 violating graphs total
  at n ≤ 15, all with γ = 4). The unbalanced (1,3)-family is *exactly*
  extremal at n = 14, 15.
* The γ = 3 strip is clean through n = 15: consistent with the split
  analysis (unbalancing gains nothing at γ = 3); the γ = 3 case of the
  conjecture may well be true.

**Flag (claim calibration):** these sweep conclusions — truth for n ≤ 12,
minimality and uniqueness of the n = 13 counterexample, the extremal
values, and the clean γ = 3 strip — rest on a **single C implementation**
(`domfilter.c`, in this bundle) driven by `geng`, audited by Codex (flags,
thresholds, decoder, window arithmetic) but **not independently re-run or
re-implemented**. They are reported as attacker-level results. The
refutation itself (the six certificates) does **not** depend on any of
them.

## Final kill-check (Gate-5, dated 2026-06-12)

Searches run this session, after verification, looking for any prior or
concurrent resolution of Conjecture 1:

1. arXiv abs page for 2511.01719 → **still v1** (Mon, 3 Nov 2025
   16:27:46 UTC); no revision, no withdrawal, no comment field changes.
2. Semantic Scholar Graph API (paper f2a5f9c747c3…) →
   **citationCount = 0, citations = []**. Nothing cites the paper at all.
3. Web search `arXiv 2511.01719 Koch Narayan maximal bipartite unique
   minimum dominating set` → only the paper itself and unrelated
   domination literature. **Nothing.**
4. Web search `"unique minimum dominating set" bipartite conjecture
   counterexample 2026` → the paper itself; a 2007 Gibson–Mynhardt
   counterexample to an unrelated Hartnell–Rall partitionable-graphs
   conjecture. **Nothing.**
5. Web search `Koch Narayan bipartite bound refuted OR counterexample OR
   disproved domination "m(n,gamma)" OR "bipartite bound"` → no refutation
   reported anywhere. **Nothing.**
6. Web search `"uniquely-dominatable" OR "unique minimum dominating set"
   bipartite edges maximum 2026 arXiv refutation` → the paper; unrelated
   vertex-edge domination and convex-bipartite work. **Nothing.**

Also standing from Gate 0/4 (2026-06-11): only v1 existed, no citing
refutation; Codex's independent web check during the audit likewise found
nothing. **Conclusion: no prior or concurrent resolution found. The kill
stands as of 2026-06-12.**

## What this does not show

* **Nothing about γ = 3.** The first open strip of the conjecture
  (γ = 3, n ≥ 10) is *not* refuted — the sweep found it clean through
  n = 15, and the unbalanced mechanism provably gains nothing there. The
  restriction of Conjecture 1 to γ ∈ {2, 3} remains open (γ = 2 is proven
  in the paper).
* **Sweep-dependent claims are attacker-level.** Truth for n ≤ 12,
  minimality/uniqueness of the n = 13 counterexample, the extremal values
  s_max(13..15, 4), and the clean γ = 3 strip all rest on the single-
  implementation `geng`+`domfilter.c` sweep (Codex-audited, not
  independently re-run). A skeptic should treat them as well-supported but
  unreplicated; the refutation itself needs only the six certificates.
* **"Failure for every γ ≥ 4" is certified only at γ = 4, 5, 6** (26
  instances, n ≤ 26). The general-γ uniqueness argument for the unbalanced
  family is a paper-style argument, not machine-verified for all γ.
* **Both clean-room checkers are Python.** They are independent
  implementations by different agents (plus Codex's own recomputation and
  the attacker's C filter), but the FRAMEWORK's different-*language* ideal
  for the two primary checkers is met only across the wider tool set.
* **Only Conjecture 1 is refuted.** Nothing here touches the paper's
  proven results (γ = 2; n = 3γ), Fischermann's general (non-bipartite)
  bound, or the paper's perfect-domination constructions. The tightness
  construction of their Theorem 4 is contradicted only in the sense that
  it is not extremal (at (16,4) it yields 37 edges while the unbalanced
  family certifies 42); at that cell its count equals m_corrected(16,4) =
  37, exactly as the authors intended.
* **The typo finding is editorial, not mathematical:** the literal printed
  Φ makes the paper internally inconsistent at (16,4) and beyond; we
  refute both readings, so nothing rests on adjudicating the authors'
  intent.

## Publication grouping

Standalone short note ("A counterexample to a conjecture of Koch and
Narayan on maximal bipartite graphs with a unique minimum dominating
set"), natural direct response to arXiv:2511.01719: the n = 13 sporadic
graph, the unbalanced family with the γ ≥ 4 analysis, the n ≤ 12
exhaustive verification, and the Φ typo remark. Thematically nearest
sibling in this campaign is `davila-conj9` (domination-adjacent TxGraffiti
kill) but the sources are unrelated; no shared provenance machinery, so no
merged write-up is indicated.
