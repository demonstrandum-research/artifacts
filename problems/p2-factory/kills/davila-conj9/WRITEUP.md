# Refutation of Conjecture 9 of arXiv:2406.19231 (TxGraffiti): Z(G) ≤ γ(G) + 2 for Connected Cubic Diamond-Free Graphs

**Slug:** `davila-conj9` · **Status:** verified kill (Gate 4 passed 2026-06-11; Gate 5 this document, 2026-06-11)

---

## Abstract (~120 words)

We refute Conjecture 9 of R. Davila, *Another conjecture of TxGraffiti concerning
zero forcing and domination in graphs* (arXiv:2406.19231v2, Nov 2024), which asserts
that every connected, cubic, diamond-free graph satisfies Z(G) ≤ γ(G) + 2. The
14-vertex counterexample G14 is a bridge-sum of two subdivided K₃,₃'s: subdivide one
edge in each copy and join the two subdivision vertices by an edge. G14 is connected,
cubic, and triangle-free (hence diamond-free under both readings of the paper's
definitions), with γ = 4 and Z = 7 = γ + 3, both values exhaustively certified in two
independent implementations (Python, Rust) and independently recomputed by a hostile
Codex referee. A chain family extends the failure: Z − γ = 3, 3, 4, 5 at
n = 14, 22, 30, 38, all exact; data through k = 8 suggest Z − γ → ∞ on this class
(conjectured, not proven).

---

## 1. Result

> **Result.** Conjecture 9 of arXiv:2406.19231v2 is **false**. Verbatim conjecture
> (frozen 2026-06-11 from the source, Section 4 "Conclusion"):
>
> *"**Conjecture 9** (TxGraffiti – Open). If G is a connected, cubic, and diamond-free
> graph, then Z(G) ≤ γ(G) + 2, and this bound is sharp."*
>
> The graph **G14** — two disjoint copies of K₃,₃, one edge subdivided in each copy,
> the two subdivision vertices joined by a bridge (n = 14, m = 21) — is connected,
> cubic, and diamond-free, yet has γ(G14) = 4 and Z(G14) = 7 = γ(G14) + 3 > γ(G14) + 2.
> Both values are exhaustive-search exact, not heuristic. (The trailing sharpness claim
> is moot once the bound itself fails.)
>
> **Moreover the failure grows:** an explicit chain family G_k in the same class
> (connected, cubic, triangle-free — hence diamond-free) achieves Z − γ = 3, 3, 4, 5 at
> n = 14, 22, 30, 38 (k = 2, 3, 4, 5), all values certified exact. No constant additive
> correction +c with c ≤ 4 rescues the conjecture; the data are consistent with
> Z − γ → ∞ on this class (§7, conjectured only).

### Provenance (frozen statement)

- Source: R. Davila, *Another conjecture of TxGraffiti concerning zero forcing and
  domination in graphs*, arXiv:2406.19231 (v1 27 Jun 2024; v2 18 Nov 2024 — still the
  latest version as of 2026-06-11, no v3/withdrawal/comment).
- URLs (accessed 2026-06-11): https://arxiv.org/abs/2406.19231 ,
  https://arxiv.org/html/2406.19231v2 (raw HTML archived in this directory as
  `source_2406.19231v2.html`, 2.5 MB).
- The paper's main theorem **proves** the claw-free sibling (Z ≤ γ + 2 for connected
  cubic claw-free graphs); Conjecture 9 is its proposed diamond-free analogue, stated
  in the Conclusion and flagged there as "ranked as more substantial than the more
  well-known α-Z Conjecture", warranting "further investigation".
- Definitions verified verbatim from §1.1 of the paper: zero forcing ("At each
  discrete time step, if a blue-colored vertex has a unique white-colored neighbor,
  then this blue-colored vertex forces its white-colored neighbor to become colored
  blue"; Z(G) = minimum size of a set whose forcing process colors all of V);
  domination (γ(G) = minimum size of X with N[X] = V); "a *diamond* in G is a
  *subgraph* of G isomorphic to K₄ with one edge missing", while "G is F-free if G
  does not contain F as an *induced* subgraph".
- **Definitional ambiguity, resolved:** the subgraph vs induced-subgraph readings of
  "diamond-free" differ in general. Every counterexample here is **triangle-free**,
  and a diamond contains triangles, so all our graphs are diamond-free under **both**
  readings. The ambiguity is moot.
- The conjecture is also restated as a "Known Conjecture" in IRIS, Table 3
  (OpenReview `v6Ulp3U1ZT`, ICML 2025 Workshop AI4MATH, Jul 2025).

## 2. Status before this work

Open: posed June 2024 (v2 Nov 2024), explicitly labeled "TxGraffiti – Open" in the
source; restated as a known (open) conjecture in IRIS (Jul 2025); the author's own
TxGraffiti retrospectives (arXiv:2409.19379, latest version 14 Apr 2026, and
arXiv:2507.17780, "In Reverie Together", 2025) list only the *claw-free* version as
proved and report no resolution of the diamond-free version. No published or preprint
refutation found at selection time (2026-06-11) or at the Gate-5 re-check (also
2026-06-11; see §6). TxGraffiti's empirical validation corpus is a curated database of
small graphs; the conjecture survived it, and we found no record of anyone attacking
the diamond-free statement directly.

## 3. The counterexample (inline)

**G14** (canonical labeling used by the Gate-4 clean-room rebuild; this exact list is
`certificate_g14.json → edges` and `chain_indep_k2.edges`):

- Block A = K₃,₃ on parts {0,1,2} | {3,4,5} with edge (0,3) subdivided by vertex 6;
- Block B = K₃,₃ on parts {7,8,9} | {10,11,12} with edge (7,10) subdivided by vertex 13;
- Bridge (6,13).

```
edges (21): (0,4) (0,5) (1,3) (1,4) (1,5) (2,3) (2,4) (2,5) (0,6) (3,6)
            (7,11) (7,12) (8,10) (8,11) (8,12) (9,10) (9,11) (9,12) (7,13) (10,13)
            (6,13)
graph6: MBzc_????@_M?[?q?
```

Certified facts (all exhaustive, exact integer bitmask arithmetic, two languages):

| fact | certificate |
|---|---|
| connected, 3-regular | BFS + degree check |
| triangle-free ⇒ diamond-free (both readings) | every edge's endpoints share 0 common neighbors |
| γ(G14) = 4 | **no 3-set dominates** (all C(14,3) = 364 checked); witness {0, 3, 7, 10} |
| Z(G14) = 7 | **no 6-set forces** (all C(14,6) = 3003 closures computed); witness {0, 1, 3, 4, 7, 8, 11} |
| Z = γ + 3 > γ + 2 | **Conjecture 9 is false** |

The discovery record's own edge list (different labeling, graph6
`MrDkO?@?O@_@?L?p?`, witnesses {0,3,6,9} and {0,1,3,4,6,7,10}) passes the identical
exhaustive suite, and a from-scratch backtracking isomorphism search confirms it is
isomorphic to the rebuild (mapping [0,1,2,3,4,5,12,6,7,8,9,10,11,13]).

**Why it works (one line):** K₃,₃ sits at equality Z = γ + 2 (γ = 2, Z = 4); the
bridge-sum makes γ add (4 = 2 + 2) while Z loses only one unit from additivity
(7 = 4 + 4 − 1), pushing the gap to +3.

**The chain family** (full data in `certificate_chain_family.json`; edge files
`chain_indep_k*.edges`): G_k = linear chain of k K₃,₃ blocks, end blocks with one
subdivided edge, middle blocks with two (on independent edges), bridges joining
consecutive subdivision vertices; n = 8k − 2; every G_k is connected, cubic,
triangle-free (girth 4, **not** bipartite), hence diamond-free.

| k | n | γ | Z | Z − γ | status |
|---|----|----|----|---|---|
| 2 | 14 | 4 | 7 | **3** | exact (Python + Rust, exhaustive) |
| 3 | 22 | 7 | 10 | **3** | exact (Python full enumeration of C(22,6), C(22,9) + Rust) |
| 4 | 30 | 9 | 13 | **4** | exact (Rust DFS exhaustive; Codex re-proved both values independently) |
| 5 | 38 | 11 | 16 | **5** | exact (Rust DFS exhaustive; the no-15-set-forces proof took 109 s on 32 threads) |
| 6 | 46 | 14 | ≤ 19 | — | γ exact; Z is an upper bound only (witness verified) |
| 7 | 54 | 16 | ≤ 22 | — | γ exact; Z upper bound only |
| 8 | 62 | 18 | ≤ 25 | — | γ exact; Z upper bound only |

## 4. Artifact

All files in `C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\davila-conj9\`:

| File | Role |
|---|---|
| `certificate_g14.json` | Main kill certificate: provenance, construction, 21-edge list, graph6, witnesses, exhaustiveness statements |
| `certificate_chain_family.json` | Chain family k = 2..8: per-k edge files, graph6, γ/Z values, witnesses, certification status |
| `chain_indep_k2.edges` … `chain_indep_k8.edges` | Graph files (`n m` header + edge lines, 0-based) consumed by the Rust verifier; k2 = G14 |
| `checker_conj9.py` | Checker A: clean-room pure-Python exhaustive checker (stdlib only, exact bitmask arithmetic) |
| `mutation_tests.py` | Mutation suite: 8 targeted corruptions, all rejected |
| `rust_check/` | Checker B: independent Rust exhaustive verifier (DFS with sound monotone pruning, std-thread parallel, no external crates) |
| `chain_study.py`, `emit_edges.py`, `make_certificates.py` | Family constructor, edge-file emitter, certificate generator (provenance of the JSONs) |
| `source_2406.19231v2.html` | Archived authoritative source (fetched 2026-06-11) |
| `VERIFICATION_LOG.md` | Full Gate-4 clean-room verification log |

Claim record: `problems\p2-factory\refuted-claims.json`, entries
`davila-conj9-zeroforcing-diamondfree-cubic` (the kill) and
`davila-conj9-diamond-free-cubic-Z-le-gamma-plus-2` (the pre-attack target record).

## 5. Verification

**Checker A — clean-room Python (Gate-4 agent, independent of discovery).**
`checker_conj9.py` was written from scratch from the construction *description*; no
discovery code was opened. It (1) sanity-anchors itself by reproducing known values
first — K₃,₃ (γ = 2, Z = 4) and Petersen (γ = 3, Z = 5); (2) rebuilds G14 and verifies
connected/cubic/triangle-free; (3) computes γ and Z **exhaustively** (every smaller
subset shown to fail); (4) re-verifies the discovery record's own edge list and its
witnesses; (5) proves the rebuild and the record graph isomorphic by backtracking
search. Exits nonzero on any failure. Core kill verifiable in well under a minute:

    cd problems\p2-factory\kills\davila-conj9
    python checker_conj9.py        # full exhaustive verification, sanity anchors first
    python mutation_tests.py       # 8/8 corruptions rejected

**Checker B — independent language/algorithm (Rust).** `rust_check` shares no code
with Checker A and uses a different algorithm: parallel DFS over vertex subsets with a
sound monotone pruning rule (domination coverage and zero-forcing closure are both
monotone in the blue set, so a node with partial set P and remaining pool R is pruned
only when P ∪ R already fails — no valid extension can be lost). `NONE` output is an
exhaustiveness proof for that size; `WITNESS` output is checked directly.

    cd rust_check && cargo build --release && cd ..
    rust_check\target\release\rust_check.exe chain_indep_k2.edges gamma 3    # -> NONE  (no 3-set dominates)
    rust_check\target\release\rust_check.exe chain_indep_k2.edges zf 6      # -> NONE  (no 6-set forces)
    rust_check\target\release\rust_check.exe chain_indep_k2.edges zffind 7  # -> WITNESS
    # family (optional; k=5 'zf 15' is the long one, ~2 min on 32 threads):
    rust_check\target\release\rust_check.exe chain_indep_k4.edges gamma 8   # -> NONE
    rust_check\target\release\rust_check.exe chain_indep_k4.edges zf 12     # -> NONE

**Mutation testing.** Eight targeted corruptions — bridge removed, triangle-creating
edge added, false γ-witness, false Z-witness, understated γ, understated Z, Petersen
passed off as a counterexample (gap 2 must not report as a kill), and a bogus
single-vertex forcing claim on K₃,₃ — are **all rejected** (`mutation_tests.py`,
exit 0 only when 8/8 reject).

**Orchestrator smoke test.** `problems\p2-factory\verify_kills.py` (section 1,
"Davila Conjecture 9") independently rebuilds the graph from the construction
description with its own labeling and set-based (non-bitmask) code, and re-confirms
cubic/connected/diamond-free, γ = 4 (no 3-set, 4-set exists), Z = 7 (no 6-set,
witness forces) — a third in-house implementation.

**Codex cross-examination (hostile referee, GPT-5.5, full shell + network,
2026-06-11, threadId 019eb9be-1412-7372-853c-a65e73622208).** Codex rebuilt G14 from
the prose (not the edge file), recomputed γ and Z exhaustively with its own code,
audited the Rust pruning rule, independently rebuilt the chain graphs k = 2..5 and
re-ran the lower-bound checks, and re-proved the k = 4 values with its own brute force
(all C(30,8) = 5,852,925 8-sets) plus a CP-SAT chronological zero-forcing model.
Verdict verbatim (abridged): *"Verdict: ACCEPT the G14 refutation. I could not break
it. Statement fidelity: no flaw found. … 'diamond' is defined as a subgraph, while
F-free is defined induced-free, but G14 is triangle-free, so it is diamond-free under
both readings. Independent G14 recomputation: no flaw found. … So Z(G14)=7=γ(G14)+3,
which refutes the conjectured upper bound. Rust audit: no fatal flaw found. The
pruning rule is sound … Chain table: trustworthy for k=2..5 … Literature search: I did
not find a prior published refutation. Final referee verdict: ACCEPT the refutation
claim. … the broader unbounded-family extrapolation remains a conjectural upgrade
unless separately proved."*

## 6. Openness re-check (fresh kill-check, 2026-06-11)

Queries run today and their results:

1. Web search `arXiv 2406.19231 zero forcing domination diamond-free cubic conjecture
   counterexample` — only the source paper and adjacent zero-forcing literature; no
   refutation.
2. Web search `"zero forcing" "diamond-free" cubic "domination number" conjecture
   refuted OR counterexample 2025 OR 2026` — explicit result: no refutation or
   counterexample appears; results only show the (proved) claw-free sibling.
3. Web search `TxGraffiti conjecture "Z(G)" "gamma(G)+2" diamond-free counterexample
   disproof` — nothing beyond the source paper and the claw-free proof.
4. Web search `Davila TxGraffiti conjecture zero forcing domination 2025 2026 open
   conjectures survey` — the diamond-free conjecture appears only as open.
5. OpenAlex (work `W4400141925`, DOI 10.48550/arXiv.2406.19231): `cited_by_count = 3`;
   the three citing works (Brimkov–Davila–Schuerger–Young, DAM 2024, on a *different*
   TxGraffiti conjecture; Davila, "Automated conjecturing with TxGraffiti",
   arXiv:2409.19379, latest version 14 Apr 2026; its SSRN copy) — none refutes
   Conjecture 9.
6. Semantic Scholar citations of arXiv:2406.19231 — three citing papers
   (arXiv:2507.17780, arXiv:2409.19379, arXiv:2409.03233); none mentions a
   counterexample or refutation for zero forcing vs domination in diamond-free cubic
   graphs.
7. arXiv abstract page — still **v2 (18 Nov 2024)**; no v3, comment, or withdrawal.
8. Davila's own 2025/2026 retrospectives checked directly: "In Reverie Together"
   (arXiv:2507.17780) lists Z ≤ γ + 2 only for **claw-free** cubic graphs in its
   "later proven" table and never uses the word "diamond"; arXiv:2409.19379 (v. Apr
   2026) likewise contains no resolution of the diamond-free statement. The author's
   most recent public accounting does not record this conjecture as settled.
9. arXiv metadata search `"zero forcing" AND "diamond-free"` (search UI, all fields,
   newest first) — zero hits (no preprint advertises the pair in title/abstract).
10. Web searches `zero forcing domination cubic counterexample bridge K_{3,3}
    subdivision 2026`, `"gamma + 3" zero forcing domination disproved cubic`, and
    `TxGraffiti conjecture refuted counterexample 2026 zero forcing` — nothing; the
    last returns explicitly that no 2026 refutation of a TxGraffiti zero-forcing
    conjecture is in evidence.
11. Codex's independent Gate-4 literature hunt (same day, own searches): "I did not
    find a prior published refutation."

**Conclusion: no prior or concurrent refutation found as of 2026-06-11.** (Phrased per
doctrine as "none found", not "none exists".)

## 7. Extension findings

The bridge-sum template generalizes: the chain family G_k (§3) certifies that the
conjecture fails **by a growing margin**, not by a one-off accident — Z − γ reaches 4
at n = 30 and 5 at n = 38, still connected, cubic, and triangle-free. Additionally
certified: γ(G_k) exact through k = 8 (values 4, 7, 9, 11, 14, 16, 18 — fitting
γ = ⌊7k/3⌋ at every data point), and explicit forcing witnesses of size 3k + 1
verified through k = 8 (so Z(G_k) ≤ 3k + 1 for k ≤ 8).

**Conjectured (NOT proven):** γ(G_k) = ⌊7k/3⌋ and Z(G_k) = 3k + 1 for all k, which
would give Z − γ = 3k + 1 − ⌊7k/3⌋ ≈ 2k/3 → ∞, i.e. Z − γ **unbounded** on connected
cubic triangle-free (a fortiori diamond-free) graphs. The missing piece is a
general-k lower bound Z(G_k) ≥ 3k + 1: fort-counting yields only Z ≥ k (the k
disjoint K₃,₃-cores are forts); a rigorous proof would need a per-block
interface/transfer-matrix argument, out of scope here. The k = 6 lower-bound
computation (no 18-set forces, n = 46) was estimated at ~7 h of compute and not
attempted. Note the gap grows at rate ≈ 2/3 per block, not 1 per block.

## 8. What this does not show

- It does **not** prove Z − γ is unbounded on this class: the general-k lower bound
  Z(G_k) ≥ 3k + 1 is unproven (§7); for k = 6, 7, 8 only γ is exact and Z is an upper
  bound. The certified statement stops at Z = γ + 5 (n = 38).
- It does **not** touch the paper's actual theorem (Z ≤ γ + 2 for connected cubic
  **claw-free** graphs, proved there); G14 contains claws, as it must.
- It does **not** give a *bipartite* counterexample: the family is triangle-free with
  girth 4 but not bipartite (subdividing one edge of a 4-cycle in K₃,₃ creates a
  5-cycle). "Triangle-free" is the strongest class qualifier certified here.
- It does not determine the optimal constant: whether Z ≤ γ + c holds for this class
  for *some* constant c is exactly the open question our family data bear on (we
  certify c ≥ 5 is necessary), but no upper bound of that shape is claimed or refuted
  beyond the known Z ≤ 2γ for cubic graphs.
- The discovery record's auxiliary examples (Petersen#Petersen n = 22,
  Heawood#Petersen n = 26, Heawood#Heawood n = 30) were **not** re-verified at Gate 4
  and are not part of this claim. (Calibration nit, recorded: that record cites
  "C(21,8) = 203,490" for the Petersen#Petersen check where the n = 22 count should be
  C(22,8) = 319,770 — immaterial to this claim, whose certified objects are G14 and
  the chain family only.)
- The diamond-free ambiguity (subgraph vs induced) is resolved only by
  triangle-freeness of *our* graphs; nothing is asserted about the two readings in
  general.
- "No prior refutation found as of 2026-06-11" is a statement about the searches in
  §6, not a proof that none exists.

## 9. Publication grouping

**Publication grouping:** best bundled with the other TxGraffiti-family kill
(`pandey-parity`, the two of which form the **two TxGraffiti-family kills** in this
campaign's ledger) under a "small exact counterexamples to recent computer-era graph
conjectures" framing — both refute 2024–2026 graph-theory conjectures with explicit
small graphs, exhaustive exact-arithmetic certificates, and dual-language checkers. A
strong alternative is bundling with the **two Graffiti spectral kills**
(`graffiti-143`, `graffiti-154`) as "refutations of automated-conjecturing-program
conjectures" — Graffiti (Fajtlowicz) is TxGraffiti's direct ancestor, which gives that
bundle a clean narrative arc (the pandey-parity kill also fits that umbrella as a
third member). The **three solubilizer kills** (`solubilizer-a1/-a13/-a16`) are
group-theoretic refutations of LLM-generated conjectures and do not fit. This kill
also stands alone if needed: single named open conjecture, single paper, a 14-vertex
counterexample, plus a certified growing-gap family.
