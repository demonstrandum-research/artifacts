# VERDICT: NO-COUNTEREXAMPLE-FOUND

No admissible graph tested failed to have a strong-majority edge-coloring with five colors. The strongest exhaustive statement established here is:

> Every finite simple graph on at most 9 vertices has a 5-color strong-majority edge-coloring whenever it is admissible.

This follows from exhaustive testing of every connected unlabeled graph through order 9 and the componentwise nature of the definition. There were 273,193 connected isomorphism types, of which 268,478 were admissible. All 268,478 were 5-SAT. All were also 4-SAT.

In addition, every connected unlabeled 4-regular graph of orders 10, 12, and 14 was tested: 59 + 1,544 + 88,168 = 89,771 graphs, all 5-SAT and 4-SAT. A further 592 admissible targeted instances, ranging from 2 to 140 vertices and 1 to 1,400 edges, were all 5-SAT and 4-SAT. No 5-UNSAT instance was found, so there is no counterexample certificate to report.

## Frozen definitions and fidelity check

The authoritative source was read before the search code was written: `AristotleMaj5.lean`, lines 49–78 and 5634–5648. The definitions used by the search are the following.

- The setting is `G : SimpleGraph V` with `[Fintype V] [DecidableEq V]` and `[DecidableRel G.Adj]`: a finite undirected loopless simple graph.
- `side G u v = (G.incidenceFinset u).erase s(u,v)`.
- `row G u v = side G u v ∪ side G v u`. Thus the row of edge `uv` consists of all graph edges sharing `u` or `v`, with `uv` itself excluded. For an edge it has exactly `d(u)+d(v)-2` members.
- `nColor G c u v α = #{f ∈ row G u v | c f = α}`. It counts row edges of color `α`; it does not count `uv` itself.
- `IsStrongMajority G c` says that for every adjacent `u,v` and **every** palette color `α`, including the color of `uv`,

  `nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2`.

  All arithmetic is Lean natural-number arithmetic. Subtraction is truncated and division is floor division. On an actual edge both endpoint degrees are positive, so the sum is at least 2 and the subtraction does not underflow. If `S=d(u)+d(v)`, the cap is:

  - `S=2k`: `k-1`;
  - `S=2k+1`: `k-1=(S-3)/2`;
  - a `K2` edge has `S=2`, empty row, and cap 0;
  - `S=3` has a one-edge row but cap 0, so it cannot be colored with any nonempty palette;
  - `S=4,5,6,7,8` give caps `1,1,2,2,3`, respectively.

- `Admissible G` is exactly `∀ u v, G.Adj u v → G.degree u + G.degree v ≠ 3`. Since endpoints of an edge have positive degrees, the only forbidden adjacent degree pair is `{1,2}`. It does not forbid any other pair.
- A coloring in Lean is a **total** function on all unordered vertex pairs, `c : Sym2 V → Fin 5`, not merely on the edge subtype. Only its values on graph edges occur in rows, so a coloring of the edge set extends arbitrarily to nonedges.
- The target `maj_le_five` is exactly: for every finite simple `G` with decidable adjacency, `Admissible G → ∃ c : Sym2 V → Fin 5, IsStrongMajority G c`.

These details are implemented literally in `scout_data/search.py::edges_and_rows`, `admissible`, and `verify_coloring`.

## Exact decision method

For an edge set `E={e_0,…,e_(m-1)}` and palette size `q`, the CNF has variables `x(e,a)` meaning edge `e` has color `a`.

1. A sequential-counter exactly-one constraint is imposed on `x(e,0),…,x(e,q-1)` for each edge.
2. For every graph edge `uv` and every color `a`, a sequential-counter at-most constraint imposes

   `Σ_{f in row(uv)} x(f,a) ≤ floor((d(u)+d(v)-2)/2)`.

3. When an edge exists, its first color is fixed to 0. This removes only global color-permutation symmetry and cannot change satisfiability.

Exhaustive enumeration used a complete symmetry-aware DFS first. Every exhaustive instance was SAT, so each decision was witnessed by a complete edge-color assignment, immediately checked by a separate direct evaluation of every Lean inequality. The targeted sweep used the CNF directly with CaDiCaL 1.9.5 through python-sat; every returned model was again checked directly. The code is exact: it does not accept a timeout or `UNKNOWN`. Had DFS exhausted an instance, the CNF UNSAT result would have been checked independently with Glucose 4.2. This two-solver path was exercised by the 3-color sanity instance discussed below.

## Exhaustive census

`geng -c` from nauty 2.8.9 generated exactly one graph6 record per connected unlabeled graph. The graph6 files and SHA-256 hashes are recorded in the result JSON.

| n | connected unlabeled | admissible | admissible m range | 5 result | 4 result |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 | all SAT | all SAT |
| 2 | 1 | 1 | 1 | all SAT | all SAT |
| 3 | 2 | 1 | 3 | all SAT | all SAT |
| 4 | 6 | 5 | 3–6 | all SAT | all SAT |
| 5 | 21 | 18 | 4–10 | all SAT | all SAT |
| 6 | 112 | 101 | 5–15 | all SAT | all SAT |
| 7 | 853 | 796 | 6–21 | all SAT | all SAT |
| 8 | 11,117 | 10,717 | 7–28 | all SAT | all SAT |
| 9 | 261,080 | 256,838 | 8–36 | all SAT | all SAT |
| **total** | **273,193** | **268,478** | 0–36 | **268,478 SAT, 0 UNSAT** | **268,478 SAT, 0 UNSAT** |

Although only connected graphs were enumerated, this proves the stated result for all graphs on at most 9 vertices: admissibility and every row constraint are component-local, and component colorings can reuse the same palette. Isolated vertices impose no constraints.

The separate exhaustive 4-regular census was:

| n | connected unlabeled 4-regular graphs | 5 result | 4 result |
|---:|---:|---:|---:|
| 10 | 59 | all SAT | all SAT |
| 12 | 1,544 | all SAT | all SAT |
| 14 | 88,168 | all SAT | all SAT |
| **total** | **89,771** | **all SAT** | **all SAT** |

## Targeted families

The seeded targeted run contains 593 records, one inadmissible (`K_{1,2}`) and 592 admissible. Every admissible record is exactly 5-SAT and 4-SAT. It includes:

- three deterministic-seed random `d`-regular generations for feasible `5≤n≤30`, `2≤d≤8` (disconnected draws were rejected);
- every complete bipartite `K_{a,b}` for `1≤a≤b≤15` (with the inadmissible case filtered);
- lexicographic cycle/clique blowups `C_n[K_k]` over the ranges in `family_graphs`;
- one- and two-subdivisions of every edge of `K5`, `K6`, the Petersen graph, and the octahedral graph.

The exact generated edge lists, graph6 strings, solver statistics, colorings, and seed are in `scout_data/targeted.json`.

## Four-color calibration

**Calibration set: empty in the tested space.** No 4-failure was found among:

- all 268,478 admissible connected unlabeled graphs through 9 vertices;
- all 89,771 connected unlabeled 4-regular graphs at orders 10, 12, and 14;
- all 592 admissible targeted graphs described above.

Consequently there is no honest “smallest 4-failure” to list. In particular, the exhaustive result proves that any 4-failure, if one exists, has at least 10 vertices; the 4-regular census proves that no 4-regular witness exists through 14 vertices.

As a lower-palette calibration of the machinery, 3 colors already fail on the 4-vertex paw graph, graph6 `CV`, with edges `(0,2),(0,3),(1,3),(2,3)` and degree sequence `(3,2,2,1)`. Its 3-color CNF is independently UNSAT in CaDiCaL and Glucose; `calibration3_paw.cnf` has SHA-256 `703f376792590bc8f07509b66162cc11f54fcbfcff6d84479998b7a9121abd3b`. This is not offered as a 4-failure, only as a check that the search does detect a genuine palette boundary.

## Near-failures and structural observations

There was little evidence of proximity to 5-failure.

- In the exhaustive order-9 run, the largest constructive-DFS backtrack count was only 16. That graph has graph6 “H?`vBRc”, `n=9`, `m=14`, and degree sequence `(4,4,4,4,3,3,3,2,1)`. Even after fixing the first edge to color 0 it has exactly 49,668 four-colorings and more than 100,000 five-colorings, so the modest search difficulty is ordering-related, not scarcity of solutions.
- Another mixed-degree graph, graph6 `H?BDAo]`, degree sequence `(4,3,3,3,2,2,2,2,1)`, has exactly 492 normalized four-colorings and 35,064 normalized five-colorings. This was the sparsest solution set found among the explicitly counted near-hard cases. Its pattern is a degree-3/4 core linked through several degree-2 vertices, so multiple cap-1 rows interact.
- All 4-regular graphs through order 14 were solved constructively without backtracking in the chosen ordering. Degree-sum-8 rows (six adjacent edges, cap 3) are therefore not locally tight enough by themselves to create observed difficulty.
- On targeted CNF instances, `K_{14,14}` had the largest conflict count for both palettes: 178 conflicts for five colors and 677 for four. These dense bipartite cases also have enormous color symmetry (144,964 and 158,790 decisions respectively), so solver effort here is not evidence of few solutions.
- Subdivided cores and mixed degree-2/high-degree constructions did not approach 5-failure. Their restrictive cap-1 degree-2 rows form chain-like inequality constraints, while the high-degree endpoint rows have enough slack to absorb them.

No tested graph required more than four colors, so the experiments do not reveal a structural obstruction specific to five colors.

## Reproduction

All scripts, graph6 inputs, JSON outputs, CNF data, and the locally built nauty source/tool are under `scout_data/`.

From this directory with Python 3.11 and `scout_data/requirements.txt` installed:

```powershell
python scout_data/search.py exhaustive scout_data/connected_n1.g6 scout_data/connected_n2.g6 scout_data/connected_n3.g6 scout_data/connected_n4.g6 scout_data/connected_n5.g6 scout_data/connected_n6.g6 scout_data/connected_n7.g6 --output scout_data/exhaustive_n1_7.json
python scout_data/search.py exhaustive scout_data/connected_n8.g6 --output scout_data/exhaustive_n8.json
python scout_data/search.py exhaustive scout_data/connected_n9.g6 --output scout_data/exhaustive_n9.json
python scout_data/search.py exhaustive scout_data/regular4_n10.g6 scout_data/regular4_n12.g6 scout_data/regular4_n14.g6 --output scout_data/exhaustive_4regular_n10_14.json
python scout_data/search.py targeted --seed 20260711 --output scout_data/targeted.json
python scout_data/census.py
```

`search.py` also has a `certificate` subcommand that emits DIMACS for any claimed UNSAT graph. `verify.py` rechecks stored models/results, and `analyze_instances.py` performs distinct-coloring counts with only the first-edge color normalization. The frozen Lean source was not modified.

## Census

This is the final banked exact-Maj′ census after the supervisor wrap order. It uses the same frozen `AristotleMaj5.lean` definitions restated above. Palette sizes are positive integers. A reported value `Maj′(G)=k` means:

- CaDiCaL returned SAT at `k`, and the complete edge-color assignment was checked directly against every frozen row inequality;
- CaDiCaL returned UNSAT at `k-1`, and Glucose 4.2 independently returned UNSAT on the same CNF. (`k=1` has no positive lower palette to check.)

The exhaustive exact-value boundary is **all admissible connected unlabeled graphs through 8 vertices**, comprising 11,640 graphs. The per-graph graph6/value records are the `census_data/connected_n*_maj.jsonl` files. Counts are:

| n | Maj′=1 | Maj′=2 | Maj′=3 | Maj′=4 | Maj′=5 | Maj′=6 | total |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| 2 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| 3 | 0 | 0 | 1 | 0 | 0 | 0 | 1 |
| 4 | 0 | 2 | 2 | 1 | 0 | 0 | 5 |
| 5 | 0 | 0 | 16 | 2 | 0 | 0 | 18 |
| 6 | 0 | 3 | 84 | 14 | 0 | 0 | 101 |
| 7 | 0 | 1 | 723 | 72 | 0 | 0 | 796 |
| 8 | 0 | 26 | 10,241 | 450 | 0 | 0 | 10,717 |

**KEY ANSWER: Maj′ = 5 never occurs in the exhaustive census through n=8. The observed maximum is 4, so four colors suffice for every admissible graph in this exhaustively covered range.**

The interrupted `n=9` exact-value census is banked honestly as partial: 130,039 disjoint completed canonical residue records out of 256,838 admissible connected types. Their distribution is Maj′ 2: 2; Maj′ 3: 129,139; Maj′ 4: 898; Maj′ 1, 5, 6: 0. This partial subset also has maximum 4 and no value 5, but it is neither exhaustive nor statistically representative. The earlier counterexample search remains exhaustive through `n=9` for the weaker statement that every graph is 4-colorable; only the *minimum-palette census* stopped at the stated partial boundary.

The authoritative machine-readable files are `census.json` (complete `n≤8` table, exact verification standard, and explicitly labeled partial `n=9` bank) and `census_extremal.json` (all minimum-order witnesses for every value that occurs, with edge lists, degree sequences, colorings, and two-solver boundary metadata). Scratch directories `census_shards/`, `census_subshards/`, and `census_micro/` are non-authoritative work products; `census.json` lists exactly which disjoint completed files entered the partial bank.

- **OBSERVATION:** The observed maximum changes from 1 at orders 1–2, to 3 at order 3, to 4 at order 4, and then remains 4 through the complete order-8 census.
- **OBSERVATION:** The unique smallest Maj′=4 graph is the paw graph, graph6 `CV`, with edges `(0,2),(0,3),(1,3),(2,3)`, degree sequence `(3,2,2,1)`, one triangle, and two degree-2 vertices.
- **OBSERVATION:** Among the 14 order-6 Maj′=4 graphs, all 14 contain degree-2 vertices and 10 contain a triangle. At order 7 these figures are 64/72 and 55/72; at order 8 they are 413/450 and 379/450, respectively.
- **OBSERVATION:** At order 8, Maj′=3 is the dominant class (10,241/10,717), while Maj′=4 accounts for 450/10,717 and Maj′=2 for 26/10,717.
- **OBSERVATION:** The most frequent order-8 degree profile among Maj′=4 graphs is `(4,3,3,3,3,2,2,2)` (37 graphs), followed by `(4,4,3,3,3,2,2,1)` (36) and `(4,3,3,3,2,2,2,1)` (31).
