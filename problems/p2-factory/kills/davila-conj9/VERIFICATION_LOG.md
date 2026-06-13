# Gate-4 clean-room verification log — slug: davila-conj9

Verifier: independent Gate-4 agent (Claude, Fable 5), 2026-06-11/12.
Doctrine: `C:\Users\jacks\source\repos\maths\FRAMEWORK.md` §1, §9.
No code was copied from `.scratch`, `verify_kills.py`, or any other prior
artifact; every checker in this directory was written from scratch for this
verification (independence requirement).

## 1. Statement provenance (verified verbatim)

Source: R. Davila, *Another conjecture of TxGraffiti concerning zero forcing
and domination in graphs*, arXiv:2406.19231 (v1 27 Jun 2024, v2 18 Nov 2024).
Fetched `https://arxiv.org/abs/2406.19231` and the full HTML
`https://arxiv.org/html/2406.19231v2` on **2026-06-11** (raw HTML archived
here as `source_2406.19231v2.html`, 2.5 MB).

Section 4 ("Conclusion") states, verbatim:

> **Conjecture 9 (TxGraffiti – Open).** *If G is a connected, cubic, and
> diamond-free graph, then Z(G) ≤ γ(G) + 2, and this bound is sharp.*

followed by: "Conjecture 9 was ranked as more substantial than the more
well-known α-Z Conjecture, so this conjecture also warrants further
investigation."

Definitions verified verbatim from §1.1 of the same paper:
- Zero forcing: "At each discrete time step, if a blue-colored vertex has a
  unique white-colored neighbor, then this blue-colored vertex forces its
  white-colored neighbor to become colored blue." Z(G) = minimum cardinality
  of a zero forcing set (a set whose process colors all of V blue).
- Domination: X ⊆ V with every vertex in X or adjacent to a vertex of X;
  γ(G) = minimum cardinality.
- "a *diamond* in G is a *subgraph* of G isomorphic to K4 with one edge
  missing", while "G is F-free if G does not contain F as an *induced*
  subgraph". **Ambiguity note:** the two readings of "diamond-free"
  (no diamond subgraph vs no induced diamond) differ in general, but our
  counterexamples are **triangle-free**, and a diamond contains triangles,
  so they are diamond-free under BOTH readings. The ambiguity is moot.

The claim record's statement field (refuted-claims.json, entry
`davila-conj9-zeroforcing-diamondfree-cubic`) matches the source verbatim.
**statementVerified: YES.**

## 2. The counterexample (clean-room rebuild)

Construction description (from the claim record, rebuilt independently):
two disjoint copies of K_{3,3}; subdivide one edge in each copy; join the two
subdivision vertices by a bridge. n = 14, m = 21.

My labeling (checker_conj9.py `build_g14`): block A parts {0,1,2}|{3,4,5},
edge (0,3) subdivided by vertex 6; block B parts {7,8,9}|{10,11,12}, edge
(7,10) subdivided by 13; bridge (6,13). graph6: `MBzc_????@_M?[?q?`.

Results of `python checker_conj9.py` (pure Python stdlib, exact integer
bitmask arithmetic; sanity-anchored by first reproducing the known values
γ=2, Z=4 for K3,3 and γ=3, Z=5 for Petersen):

| check | method | result |
|---|---|---|
| connected, 3-regular | BFS / degree count | PASS |
| triangle-free (⇒ diamond-free, both readings) | all edges, common-neighbor test | PASS |
| γ = 4 | **exhaustive**: all C(14,3)=364 3-sets fail to dominate; witness {0,3,7,10} | PASS |
| Z = 7 | **exhaustive**: all C(14,6)=3003 6-sets fail to force; witness {0,1,3,4,7,8,11} | PASS |
| Z = γ + 3 > γ + 2 | arithmetic | **Conjecture 9 REFUTED** |

Cross-checks:
- The claim record's own 21-edge list was verified independently with the
  same suite (γ=4, Z=7, record witnesses {0,3,6,9} and {0,1,3,4,6,7,10}
  both valid), and a from-scratch backtracking isomorphism search confirms
  my rebuild is isomorphic to the record's graph
  (mapping [0,1,2,3,4,5,12,6,7,8,9,10,11,13]).
- Second language: the independent Rust implementation (`rust_check/`,
  DFS over subsets with a sound monotone pruning rule) reproduces
  "no 3-set dominates", "no 6-set forces" on the same edge file.

Mutation testing (`mutation_tests.py`): 8 targeted corruptions
(bridge removed; triangle-creating edge added; false γ witness; false Z
witness; γ understated; Z understated; Petersen passed off as counterexample;
bogus forcing claim). **All 8 rejected.**

## 3. Upgrade study: chains of k K3,3-blocks

Family G_k ("indep" variant, `chain_study.py chain(k)`): linear chain of k
K3,3 blocks; end blocks have one subdivided edge, middle blocks two
(a1b1 and a2b2); bridges join consecutive subdivision vertices. n = 8k − 2.
All G_k verified connected, cubic, triangle-free (girth 4; NOT bipartite —
subdividing one edge of a 4-cycle creates a 5-cycle), hence diamond-free.

Exact values (lower bounds by exhaustive search — pure enumeration in Python
where feasible, and the Rust DFS with sound monotone pruning everywhere;
upper bounds by explicit witnesses re-verified in BOTH the Python and Rust
implementations):

| k | n | γ(G_k) | Z(G_k) | Z − γ | certification |
|---|----|----|----|---|---|
| 2 | 14 | 4  | 7  | **3** | exhaustive, Python + Rust |
| 3 | 22 | 7  | 10 | **3** | exhaustive, Python (C(22,6), C(22,9) full enumeration) + Rust |
| 4 | 30 | 9  | 13 | **4** | exhaustive, Rust DFS (no 8-set dominates; no 12-set forces); witnesses re-verified in Python |
| 5 | 38 | 11 | 16 | **5** | exhaustive, Rust DFS (no 10-set dominates; no 15-set forces, 109 s/32 threads); witnesses re-verified in Python |
| 6 | 46 | 14 | ≤ 19 | — | γ exact (Rust: no 13-set dominates; 14-witness re-verified in Python); Z lower bound NOT certified |
| 7 | 54 | 16 | ≤ 22 | — | γ exact (Rust: no 15-set dominates; 16-witness re-verified in Python); Z lower bound NOT certified |
| 8 | 62 | 18 | ≤ 25 | — | γ exact (Rust: no 17-set dominates; 18-witness re-verified in Python); Z lower bound NOT certified |

Soundness of the pruning rule (the only non-trivial ingredient of the Rust
exhaustive claims): both domination coverage and zero-forcing closure are
monotone in the chosen set, so a DFS node with partial set P and remaining
candidate pool R can be pruned when P ∪ R fails the goal; no subset of
P ∪ R extending P can then succeed. Everything else is plain enumeration.

**Certified upgrade:** Z − γ is NOT bounded by 3 either — it reaches 4 at
n = 30 and 5 at n = 38 within the same connected/cubic/diamond-free
(indeed triangle-free) class. The conjecture is false by a growing margin,
not by a one-off accident.

**Conjectured (NOT proven):** γ(G_k) = floor(7k/3) (fits all seven data
points k = 2..8≥) and Z(G_k) = 3k + 1 (exact for k ≤ 5; witness pattern
{a2,b2,b3,s}_block1 ∪ {a1,a2,b2}_blocks 2..k verified to force for k ≤ 8),
which would give Z − γ = 3k+1−floor(7k/3) ~ 2k/3 → ∞: Z − γ unbounded on
connected cubic triangle-free graphs. Status: open; a rigorous general-k
proof would need (easy) an explicit period-3 dominating pattern for the
upper bound on γ, and (hard) a per-block interface/transfer argument for
Z ≥ 3k+1. Fort-counting gives only Z ≥ k (the k disjoint 6-vertex
K3,3-cores are forts). We do NOT claim the unbounded-gap theorem.

## 4. Codex cross-examination (GPT-5.5, hostile referee, full shell +
network, 2026-06-11, threadId 019eb9be-1412-7372-853c-a65e73622208)

Verbatim verdict (abridged only by omitting file-path links):

> **Verdict: ACCEPT the G14 refutation.** I could not break it.
> Statement fidelity: no flaw found. The official arXiv v2 PDF states
> Conjecture 9 as claimed [...] It does have the diamond subtlety:
> "diamond" is defined as a subgraph, while F-free is defined induced-free,
> but G14 is triangle-free, so it is diamond-free under both readings.
> Bundled checkers: no flaw found. I reran checker_conj9.py and
> mutation_tests.py. Results matched the log [...]
> Independent G14 recomputation: no flaw found. I rebuilt the graph from
> the prose, not from the edge file. [...] gamma: no 1-,2-,3-set dominates;
> first 4-witness (0,3,7,10). Z: no 1-..6-set forces; first 7-witness
> (0,1,3,4,7,8,11). So Z(G14)=7=gamma(G14)+3.
> Rust audit: no fatal flaw found. The pruning rule is sound [...] For
> `NONE`, every start pair is exhausted. Minor non-issue: invalid mode
> strings fall through as domination mode, but all invoked modes were valid.
> Chain table: trustworthy for k=2..5. I rebuilt the chain_indep_k2..k5
> graphs independently and confirmed their edge sets exactly match the
> supplied files. Rust reruns gave NONE for the lower-bound checks through
> k=5, including the slower k=5 zf 15 check [...] I also independently
> verified k=4: full brute force over all C(30,8)=5,852,925 8-sets found no
> dominating set, a 9-witness exists, and a separate CP-SAT chronological
> zero-forcing model proved no exact 12-initial-vertex forcing process
> exists; the 13-witness forces all 30 vertices.
> Literature search: I did not find a prior published refutation [...]
> Final referee verdict: **ACCEPT the refutation claim.** The core G14
> counterexample is independently verified. The k=2..5 exact-values table
> is also credible, with especially strong independent support for k=4;
> the broader unbounded-family extrapolation remains a conjectural upgrade
> unless separately proved.

## 5. Files

- `checker_conj9.py` — main clean-room checker (pure Python, exhaustive)
- `mutation_tests.py` — 8/8 corruptions rejected
- `chain_study.py` — chain constructor + CP-SAT/fort-cover tooling (the
  CP-SAT path was abandoned for slowness; constructor + closure functions
  used throughout)
- `emit_edges.py`, `chain_indep_k*.edges`, `chain_shared_k*.edges` — graph
  files for the Rust verifier
- `rust_check/` — independent Rust exhaustive verifier (second language)
- `make_certificates.py`, `certificate_g14.json`,
  `certificate_chain_family.json` — machine-readable certificates
- `source_2406.19231v2.html` — archived authoritative source
- `VERIFICATION_LOG.md` — this file

## 6. Verdict

The claim record's refutation of Conjecture 9 is **CORRECT and VERIFIED**
under the exact statement of arXiv:2406.19231v2: G14 (n = 14) is connected,
cubic, diamond-free, with Z = γ + 3. Both my clean-room rebuild and the
record's explicit edge list pass every check, exhaustively, in two
independent implementations (Python, Rust). The bound Z ≤ γ + 2 fails;
moreover the certified family shows the excess reaches Z = γ + 5 by n = 38.
