# Z − γ is unbounded on connected cubic triangle-free graphs

## Exact zero-forcing and domination numbers for the K₃,₃-chain family G_k, via a failed-forcing (wavefront) argument

**File:** `theorem/failed-forcing.md` · **Date:** 2026-06-12 ·
**Companion artifacts:** `theorem/validate_theorem.py` (validates every lemma computationally; ALL CHECKS PASSED),
`theorem/case_tables.md` (machine-emitted orbit/fort tables, reproduced in §4),
`theorem/z_exact_extend.py` (bonus: independent exact Z for k = 6; partial lower bound for k = 7),
parent directory `..\WRITEUP.md` (the certified refutation of Davila Conjecture 9, arXiv:2406.19231, which this document upgrades from "growing finite gap, unboundedness conjectured" to "unboundedness proven with exact rates").

---

## 0. Results

Let γ(G) denote the domination number and Z(G) the zero forcing number. Let G_k (k ≥ 2) be
the K₃,₃-chain graph defined in §1 (the family `chain_indep_k*.edges` of the parent
certificate; G_2 = G14, the 14-vertex counterexample to Davila's Conjecture 9). G_k is
connected, cubic, and triangle-free (hence diamond-free under both the subgraph and the
induced-subgraph reading), with n = 8k − 2 vertices.

> **Theorem A (exact values).** For every k ≥ 2:
>
> γ(G_k) = 2k + ⌊k/3⌋ = ⌊7k/3⌋  and  Z(G_k) = 3k + 1.
>
> **Theorem B (unbounded gap).** For every k ≥ 2:
>
> Z(G_k) − γ(G_k) = k − ⌊k/3⌋ + 1 = ⌈2k/3⌉ + 1 → ∞.
>
> In terms of the order n = 8k − 2: Z − γ = ⌈(n+2)/12⌉ + 1 on this family.
>
> **Corollary C.** The difference Z − γ is unbounded on the class of connected, cubic,
> triangle-free (a fortiori diamond-free) graphs. In particular, **no** additive
> weakening "Z(G) ≤ γ(G) + c" of Conjecture 9 of arXiv:2406.19231 holds for any
> constant c, and Z − γ ≥ (n + 14)/12 infinitely often within the class.

Consistency with the independently certified exact values (exhaustive search in Python +
Rust, hostile Codex re-computation; see `..\WRITEUP.md` §3, §5):

| k | n | γ certified | 2k + ⌊k/3⌋ | Z certified | 3k + 1 | gap | ⌈2k/3⌉ + 1 |
|---|----|----|----|----|----|---|---|
| 2 | 14 | 4  | 4  | 7  | 7  | 3 | 3 |
| 3 | 22 | 7  | 7  | 10 | 10 | 3 | 3 |
| 4 | 30 | 9  | 9  | 13 | 13 | 4 | 4 |
| 5 | 38 | 11 | 11 | 16 | 16 | 5 | 5 |
| 6 | 46 | 14 | 14 | 19* | 19 | 5 | 5 |
| 7 | 54 | 16 | 16 | ≤22* | 22 | — | 6 |
| 8 | 62 | 18 | 18 | ≤25* | 25 | — | 7 |

(*k = 6, 7, 8: γ was already certified exact; Z was previously only an upper bound
(witnesses verified). The proof below settles all of them. Additionally
`z_exact_extend.py` independently recomputed Z(G_6) = 19 exactly by a fort-cover/ILP
method, and reached the lower bound 21 for k = 7 before its compute budget ran out —
see §9.3.)

**Proof strategy (the assigned "wavefront" lens).** Any zero forcing process sweeps a
blue wavefront across the graph while maintaining a blue/white cut. In G_k the blocks
are joined by bridges, and a bridge can transmit the wavefront **at most once** (Lemma
3.3). Restricting a global forcing process to a single block — treating the external
bridge endpoints as permanently blue and granting any inbound bridge force for free —
yields a valid forcing process on a 7- or 8-vertex "block automaton" (Lemma 3.2). A
finite, exhaustively validated case analysis on the boundary states of the automaton
(§4) shows each block needs at least 4 − (number of inbound bridge forces) blue starts
of its own. Since at most k − 1 inbound forces exist in total, Z ≥ 4k − (k−1) = 3k + 1.
A matching explicit forcing set gives equality. The domination number is handled by a
separate local analysis (§7): each block core needs 2 dominators, and a 3-block window
argument forces an extra dominator per 3 blocks.

---

## 1. The family G_k

### 1.1 Construction

Fix k ≥ 2. G_k consists of k **blocks** numbered 1, …, k in a row, joined by k − 1
**bridges**.

* Every block contains a copy of K₃,₃ with parts A^i = {a₁^i, a₂^i, a₃^i} and
  B^i = {b₁^i, b₂^i, b₃^i}; these 6 vertices form the **core** C_i of block i.
* **End blocks** (i = 1 and i = k): the edge (a₁, b₁) is subdivided by a new vertex
  s^i. The block has 7 vertices: V_i = C_i ∪ {s^i}.
* **Middle blocks** (2 ≤ i ≤ k − 1): the two independent edges (a₁, b₁) and (a₂, b₂)
  are subdivided by new vertices s_in^i and s_out^i respectively. The block has 8
  vertices: V_i = C_i ∪ {s_in^i, s_out^i}.
* **Bridges:** for i = 1, …, k − 1, the edge (out_i, in_{i+1}), where out_i denotes
  s_out^i for a middle block and s^i for the end block i = 1, and in_{i+1} denotes
  s_in^{i+1} for a middle block and s^k for the end block i + 1 = k. (For end blocks the
  single vertex s^i plays whichever of the two roles is needed; we write s_out^1 := s^1
  and s_in^k := s^k.)

We call s^i, s_in^i, s_out^i the **subdivision vertices** of block i and write S_i for
the set of them (|S_1| = |S_k| = 1, |S_i| = 2 otherwise).

**Concrete labelling** (this exact labelling is cross-checked edge-for-edge against the
certified files `..\chain_indep_k{2..8}.edges` by `validate_theorem.py` §S0): block 1
occupies vertices 0–6, block i ≥ 2 occupies 7 + 8(i−2) … 6 + 8(i−1); within a block, in
order: a₁, a₂, a₃, b₁, b₂, b₃, then s (end) or s_in, s_out (middle).

**Neighbourhoods.** (All used repeatedly below; each is immediate from the construction.)

Middle block i:

| vertex | neighbours |
|---|---|
| a₁ | b₂, b₃, s_in |
| a₂ | b₁, b₃, s_out |
| a₃ | b₁, b₂, b₃ |
| b₁ | a₂, a₃, s_in |
| b₂ | a₁, a₃, s_out |
| b₃ | a₁, a₂, a₃ |
| s_in | a₁, b₁, out_{i−1} |
| s_out | a₂, b₂, in_{i+1} |

End block (i = 1 shown; i = k symmetric with its bridge to the left):

| vertex | neighbours |
|---|---|
| a₁ | b₂, b₃, s |
| a₂ | b₁, b₂, b₃ |
| a₃ | b₁, b₂, b₃ |
| b₁ | a₂, a₃, s |
| b₂ | a₁, a₂, a₃ |
| b₃ | a₁, a₂, a₃ |
| s  | a₁, b₁, in₂ (resp. out_{k−1}) |

Two facts that the whole argument leans on, both visible in the tables:

* **(F1)** Every neighbour of a core vertex lies in its own block.
* **(F2)** The only edges joining different blocks are the k − 1 bridges, and every
  bridge endpoint is a subdivision vertex.

### 1.2 Basic properties

**Lemma 1.1.** G_k is connected and cubic with n = 8k − 2 vertices and m = 3n/2 =
12k − 3 edges; it is triangle-free and **not** bipartite. Triangle-freeness implies diamond-freeness under both the "subgraph" and the
"induced subgraph" reading (a diamond contains a triangle).

*Proof.* Vertex count: 7 + 7 + 8(k−2) = 8k − 2. Degrees: each core vertex has its 3
K₃,₃-edges, with subdivided ones redirected to the subdivision vertex (tables above);
each subdivision vertex has degree 2 + 1 (its subdivided edge's two endpoints plus its
bridge) — so G_k is cubic, and m = 3n/2 = 12k − 3. Connectivity: each block is
connected (K₃,₃ minus at most two independent edges is connected, and each subdivision
vertex attaches to two core vertices), and the bridges join consecutive blocks.
Triangle-free: a triangle inside a block would yield a closed walk of length ≤ 3 in
K₃,₃ after un-subdividing, impossible (K₃,₃ is bipartite, girth 4, and subdividing
edges only lengthens cycles); no cycle crosses a bridge (bridges are cut edges). Not
bipartite: a₁–b₂–a₂–b₁–s–a₁ is a 5-cycle in an end block (check the table: a₁b₂, b₂a₂,
a₂b₁, b₁s, sa₁ are all edges). ∎

(Machine validation: `validate_theorem.py` §S1, k ≤ 30.)

---

## 2. Zero forcing preliminaries

**Definition 2.1 (zero forcing).** Let G = (V, E) and B ⊆ V ("blue"; V ∖ B "white").
The **forcing rule**: a blue vertex u with exactly one white neighbour w **forces** w
to become blue (written u → w). A **chronological forcing process** from B is a maximal
sequence B = T₀ ⊊ T₁ ⊊ … ⊊ T_m, where T_j = T_{j−1} ∪ {w_j} for some valid force
u_j → w_j with respect to the blue set T_{j−1} (one force at a time; maximal = no force
applies to T_m). B is a **zero forcing set** if some (equivalently, by Lemma 2.2, every)
chronological process from B ends with T_m = V. Z(G) = min size of a zero forcing set.

**Definition 2.2 (closure).** cl_G(B) := the terminal set of the synchronous iteration
"repeat: add all vertices forced by some blue vertex, until stable".

**Lemma 2.1 (closed supersets).** If S ⊇ B and no force applies to S ("S is closed"),
then S ⊇ cl_G(B).

*Proof.* Induction along the synchronous iteration. Suppose T ⊆ S for an intermediate
stage T, and let v be forced from T by u: u ∈ T ⊆ S, and every neighbour of u except v
is in T ⊆ S. If v ∉ S, then u (blue in S) has exactly one white neighbour v in S, so a
force applies to S — contradiction. Hence v ∈ S. ∎

**Lemma 2.2 (order-independence).** Every chronological forcing process from B
terminates at exactly cl_G(B). In particular all maximal processes from a zero forcing
set colour V, and cl is **monotone**: B ⊆ B′ ⇒ cl_G(B) ⊆ cl_G(B′).

*Proof.* Let T_m be the terminal set of a maximal chronological process. T_m is closed
and contains B, so T_m ⊇ cl_G(B) by Lemma 2.1. Conversely each step of the process is
also a step available to the closure computation: by induction T_j ⊆ cl_G(B) — for the
step, u_j ∈ T_{j−1} ⊆ cl_G(B) has all neighbours except w_j inside T_{j−1} ⊆ cl_G(B),
so if w_j ∉ cl_G(B) then cl_G(B) is not closed, contradiction. Hence T_m = cl_G(B).
Monotonicity: cl_G(B′) is a closed superset of B, apply Lemma 2.1. ∎

**Definition 2.3 (fort, Fast–Hicks).** A **fort** of G is a nonempty F ⊆ V such that
every vertex *outside* F has either 0 or ≥ 2 neighbours in F.

**Lemma 2.3 (fort avoidance).** If F is a fort and B ∩ F = ∅, then cl_G(B) ∩ F = ∅.
In particular every zero forcing set intersects every fort.

*Proof.* Suppose not; consider the first moment a vertex v ∈ F is forced in a
chronological process (Lemma 2.2 allows us to pick any), say by u. Then u is blue, so
u ∉ F (no vertex of F is blue yet), and v is u's *unique* white neighbour. But u, being
outside F and having the neighbour v ∈ F, has ≥ 2 neighbours in F, all of which are
still white — so u has ≥ 2 white neighbours. Contradiction. ∎

---

## 3. The block automaton and the Restriction Lemma

Throughout, fix k ≥ 2, a zero forcing set B of G_k, and a chronological forcing process
P: B = T₀ ⊊ … ⊊ T_m = V(G_k) (exists by Lemma 2.2).

**Definition 3.1 (block graphs / the automaton).** For block i let H_i := the subgraph
of G_k induced on V_i. Explicitly: H_end is K₃,₃ with edge (a₁,b₁) subdivided by s (7
vertices, s of degree 2), and H_mid is K₃,₃ with edges (a₁,b₁), (a₂,b₂) subdivided by
s_in, s_out (8 vertices, s_in, s_out of degree 2). All other degrees are 3, i.e. H_i is
the block with its bridge stub(s) deleted.

The interaction of block i with the rest of G_k during P is summarised by one item:

**Definition 3.2 (in-forces).** R_i := { v ∈ V_i : v is forced in P along a bridge,
i.e. by a forcer outside V_i }. By (F2), R_i ⊆ S_i (only subdivision vertices have
outside neighbours). Let r_i := |R_i|.

**Remark (why deleting the bridge stub is the right "boundary condition").** In the
real process the external bridge neighbour t of a subdivision vertex s can influence
block i in exactly two ways: (1) t forces s — recorded in R_i; (2) t being blue makes
s's white-neighbour count smaller, *helping* s force inside the block. Deleting t
(equivalently: treating t as permanently blue from time 0, but never letting it force)
grants the block the *most generous possible* version of (2) and exactly the recorded
version of (1). This is the content of:

**Lemma 3.2 (Restriction Lemma).** cl_{H_i}( (B ∩ V_i) ∪ R_i ) = V_i.

*Proof.* Let C := cl_{H_i}((B ∩ V_i) ∪ R_i). We show by induction on j that
T_j ∩ V_i ⊆ C; since T_m = V(G_k), this gives V_i ⊆ C ⊆ V_i.

Base: T₀ ∩ V_i = B ∩ V_i ⊆ C.

Step: suppose T_{j−1} ∩ V_i ⊆ C and T_j = T_{j−1} ∪ {w_j}, w_j forced by u_j. If
w_j ∉ V_i there is nothing to prove. So let w_j ∈ V_i.

*Case 1: u_j ∉ V_i.* Then u_jw_j is an edge leaving block i, i.e. a bridge (F2), so
w_j ∈ R_i ⊆ C.

*Case 2: u_j ∈ V_i.* Then u_j ∈ T_{j−1} ∩ V_i ⊆ C. Validity of the force in G_k means
every G_k-neighbour of u_j other than w_j lies in T_{j−1}; in particular every
H_i-neighbour of u_j other than w_j lies in T_{j−1} ∩ V_i ⊆ C (H_i-neighbourhoods are
G_k-neighbourhoods intersected with V_i). Now if w_j ∉ C, then in H_i the vertex
u_j ∈ C would have exactly one neighbour outside C, namely w_j, so C would not be
closed in H_i — contradicting the definition of closure. Hence w_j ∈ C. ∎

**Corollary 3.2′.** |B ∩ V_i| ≥ μ_i(R_i), where for R ⊆ S_i,
μ_i(R) := min{ |X| : X ⊆ V_i, cl_{H_i}(X ∪ R) = V_i }.

*Proof.* X = B ∩ V_i satisfies cl_{H_i}(X ∪ R_i) = V_i by Lemma 3.2. ∎

**Lemma 3.3 (bridge capacity).** In the whole process P, each bridge carries at most
one force (in one direction or the other, never both). Consequently
Σ_{i=1}^{k} r_i ≤ k − 1.

*Proof.* Blue vertices never revert to white, and a force u → w requires w white. After
a force along a bridge both endpoints are blue, so no further force can occur along it
in either direction. Each in-force counted by some r_i is a force along one of the
k − 1 bridges, and distinct in-forces use distinct bridges (a force along bridge e
colours e's white endpoint; a second in-force along e is excluded by the first
sentence). ∎

---

## 4. The per-block start requirement: case analysis on boundary states

This section proves the five finite facts that drive the lower bound. Define

m_end(r) := min over |R| = r of μ_end(R), m_mid(r) := min over |R| = r of μ_mid(R).

> **Lemma 4.1 (block automaton values).**
>
> | block type | grants r | value | needed inequality |
> |---|---|---|---|
> | end | 0 | m_end(0) = 4 | ≥ 4 |
> | end | 1 | m_end(1) = 3 | ≥ 3 |
> | middle | 0 | m_mid(0) = 4 | ≥ 4 |
> | middle | 1 | m_mid(1) = 3 (either grant) | ≥ 3 |
> | middle | 2 | m_mid(2) = 2 | ≥ 2 |
>
> In every case m(r) ≥ 4 − r.

Only the lower bounds are used for Theorem A's lower bound; the upper bounds (witnesses
below) show the case analysis is tight and explain where the matching construction in
§6 comes from.

The proof is a finite case analysis. We organise it so that every case is certified by
a **fort** (Lemma 2.3) of the block graph H ∈ {H_end, H_mid}, and we shrink the number
of cases with the automorphism groups:

* Aut(H_mid) = {id, σ, τ, στ} of order 4, where σ = (a₁b₁)(a₂b₂)(a₃b₃) (side swap) and
  τ = (a₁a₂)(b₁b₂)(s_in s_out) (index swap). [Brute-force enumeration of all 8!
  vertex permutations confirms these 4 are the *only* automorphisms; in particular
  {s_in, s_out}, the set of degree-2 vertices, is preserved by all of them.]
* Aut(H_end) = ⟨σ, (a₂a₃), (b₂b₃)⟩ of order 8 (σ as above; a₂, a₃ are twins, b₂, b₃ are
  twins; s is the unique degree-2 vertex, fixed by everything). [Same brute-force
  verification.]

Forcing failure transports along automorphisms (π(cl(X)) = cl(π(X))), and grants
transport with them; the M1 table below uses only the stabiliser {id, σ} of s_in.

**Reduction for start sets containing subdivision vertices.** The tables list only
X ⊆ core. This suffices, by iterating the following two moves until X ⊆ core: (1) if X
contains a subdivision vertex s ∉ R, rewrite X ∪ R = (X∖{s}) ∪ (R ∪ {s}) — the same
set, viewed as a strictly smaller start set with one more grant, i.e. a case of an
earlier table (the claim order M2 → M1 → M0 and E1 → E0 ensures the target table
exists; a middle block has only two subdivision vertices, so at most two iterations);
(2) if X contains s ∈ R, drop it: X ∪ R = (X∖{s}) ∪ R with a strictly smaller start
set and the same grants — then pad X∖{s} with arbitrary core vertices up to that
table's size; the padded set fails by the table, hence the smaller set fails by
monotonicity (Lemma 2.2). Each move strictly decreases |X| and never decreases |R|, so
the iteration terminates in a listed case. Independently of this
reduction, the machine check ran over **all** subsets including subdivision vertices
(`validate_theorem.py` §S3, "exhaustive over all C(n, q) subsets incl. sub-vertices"),
so nothing rests on the bookkeeping above.

**How to read the tables.** Each row exhibits a fort F of the block graph H with
F ∩ (X ∪ R) = ∅. By Lemma 2.3, cl_H(X ∪ R) misses all of F, so X ∪ R does not force
H — and by the automorphism column the same holds for every set in the orbit of X.
Checking a row by hand: (a) F is a fort — for each vertex outside F count its
neighbours in F using the §1.1 tables (0 or ≥ 2 required); (b) F avoids X ∪ R —
inspection. The "stalled closure" column (= V ∖ F here; in every row cl(X ∪ R) happens
to equal V ∖ F) is informational. Orbit sizes sum to C(6,1) = 6, C(6,2) = 15,
C(6,3) = 20 as appropriate, confirming coverage.

### Claim M2 — middle block, grants R = {s_in, s_out}: no single start forces. (m_mid(2) ≥ 2)

| representative X | orbit size | stalled closure of X ∪ R | fort F (avoids X ∪ R) |
|---|---|---|---|
| {a₁} | 4 | {a₁, b₁, s_in, s_out} | {a₂, a₃, b₂, b₃} |
| {a₃} | 2 | {a₃, s_in, s_out} | {a₁, a₂, b₁, b₂, b₃} |

Example hand-check of the first row's fort F = {a₂, a₃, b₂, b₃}: outside vertices
a₁ (nbrs b₂, b₃ ∈ F: 2), b₁ (a₂, a₃ ∈ F: 2), s_in (a₁, b₁ ∉ F: 0), s_out (a₂, b₂ ∈ F: 2). ✓

### Claim M1 — middle block, grant R = {s_in} (by τ-symmetry the grant {s_out} is identical): no 2 starts force. (m_mid(1) ≥ 3)

| representative X | orbit size | stalled closure of X ∪ R | fort F (avoids X ∪ R) |
|---|---|---|---|
| {a₁,a₂} | 2 | {a₁,a₂,a₃,b₁,s_in} | {b₂, b₃, s_out} |
| {a₁,a₃} | 2 | {a₁,a₂,a₃,b₁,s_in} | {b₂, b₃, s_out} |
| {a₁,b₁} | 1 | {a₁,b₁,s_in} | {a₂, a₃, b₂, b₃, s_out} |
| {a₁,b₂} | 2 | {a₁,b₁,b₂,b₃,s_in} | {a₂, a₃, s_out} |
| {a₁,b₃} | 2 | {a₁,b₁,b₂,b₃,s_in} | {a₂, a₃, s_out} |
| {a₂,a₃} | 2 | {a₂,a₃,s_in} | {a₁, b₁, b₂, b₃, s_out} |
| {a₂,b₂} | 1 | {a₂,b₂,s_in} | {a₁, a₃, b₁, b₃, s_out} |
| {a₂,b₃} | 2 | {a₂,b₃,s_in} | {a₁, a₃, b₁, b₂, s_out} |
| {a₃,b₃} | 1 | {a₃,b₃,s_in} | {a₁, a₂, b₁, b₂, s_out} |

(15 = sum of orbit sizes = C(6,2). Note every listed fort contains s_out — with only
s_in granted, the right half of the block can always be kept white.)

### Claim M0 — middle block, no grants: no 3 starts force. (m_mid(0) ≥ 4)

| representative X | orbit size | stalled closure of X | fort F (avoids X) |
|---|---|---|---|
| {a₁,a₂,a₃} | 2 | {a₁,a₂,a₃} | {b₁, b₂, b₃, s_in, s_out} |
| {a₁,a₂,b₁} | 4 | {a₁,a₂,b₁} | {a₃, b₂, b₃, s_in, s_out} |
| {a₁,a₂,b₃} | 2 | {a₁,a₂,a₃,b₃} | {b₁, b₂, s_in, s_out} |
| {a₁,a₃,b₁} | 4 | {a₁,a₃,b₁} | {a₂, b₂, b₃, s_in, s_out} |
| {a₁,a₃,b₂} | 4 | {a₁,a₂,a₃,b₂,s_out} | {b₁, b₃, s_in} |
| {a₁,a₃,b₃} | 4 | {a₁,a₂,a₃,b₃} | {b₁, b₂, s_in, s_out} |

(20 = C(6,3). Hand-check of the 3-element fort {b₁, b₃, s_in}: a₁ has neighbours
b₃, s_in ∈ F (2); a₂ has b₁, b₃ (2); a₃ has b₁, b₃ (2); b₂ has none — its neighbours
are a₁, a₃, s_out ∉ F (0); s_out has none (0). ✓)

### Claim E1 — end block, grant R = {s}: no 2 starts force. (m_end(1) ≥ 3)

| representative X | orbit size | stalled closure of X ∪ R | fort F (avoids X ∪ R) |
|---|---|---|---|
| {a₁,a₂} | 4 | {a₁,a₂,a₃,b₁,s} | {b₂, b₃} |
| {a₁,b₁} | 1 | {a₁,b₁,s} | {a₂, a₃, b₂, b₃} |
| {a₁,b₂} | 4 | {a₁,b₁,b₂,b₃,s} | {a₂, a₃} |
| {a₂,a₃} | 2 | {a₂,a₃,s} | {a₁, b₁, b₂, b₃} |
| {a₂,b₂} | 4 | {a₂,b₂,s} | {a₁, a₃, b₁, b₃} |

(15 = C(6,2). The recurring 2-element forts: {b₂, b₃} is a fort of H_end because each
of a₁, a₂, a₃ is adjacent to both and b₁, s to neither.)

### Claim E0 — end block, no grants: no 3 starts force. (m_end(0) ≥ 4)

| representative X | orbit size | stalled closure of X | fort F (avoids X) |
|---|---|---|---|
| {a₁,a₂,a₃} | 2 | {a₁,a₂,a₃} | {b₁, b₂, b₃, s} |
| {a₁,a₂,b₁} | 4 | {a₁,a₂,b₁} | {a₃, b₂, b₃, s} |
| {a₁,a₂,b₂} | 8 | {a₁,a₂,a₃,b₂} | {b₁, b₃, s} |
| {a₁,b₂,b₃} | 2 | {a₁,b₁,b₂,b₃,s} | {a₂, a₃} |
| {a₂,a₃,b₂} | 4 | {a₁,a₂,a₃,b₂} | {b₁, b₃, s} |

(20 = C(6,3).)

### Upper bounds (tightness)

cl_{H_end}({a₁,a₂,b₁,b₂}) = V_end: a₂ → b₃ (nbrs b₁,b₂ blue), b₃ → a₃ (nbrs a₁,a₂
blue), a₁ → s (nbrs b₂,b₃ blue). So m_end(0) ≤ 4.
cl_{H_end}({a₁,a₂,b₂} ∪ {s}) = V_end: a₁ → b₃ (b₂, s blue), b₃ → a₃, a₃ → b₁. So
m_end(1) ≤ 3. cl_{H_mid}({a₁,a₂,b₂} ∪ {s_in}) = V_mid: a₁ → b₃, b₃ → a₃, a₃ → b₁,
a₂ → s_out. So m_mid(1) ≤ 3; adding s_in as a start instead of a grant gives
m_mid(0) ≤ 4. cl_{H_mid}({a₁,a₂} ∪ {s_in,s_out}) = V_mid: s_in → b₁ (a₁ blue), s_out →
b₂ (a₂ blue), a₁ → b₃ (b₂ now blue... nbrs b₂,b₃,s_in: b₂ blue, s_in blue ⇒ force b₃),
b₃ → a₃. So m_mid(2) ≤ 2. ∎ (Lemma 4.1)

**Machine validation** (`validate_theorem.py` §S2–S3): μ was computed by brute force
over *all* start subsets for *every* grant set R (both choices for r = 1 agree, as τ
predicts); every deficient set was confirmed non-forcing exhaustively without symmetry
reduction; every fort above was verified to be a fort; every claimed witness verified.

---

## 5. Lower bound: Z(G_k) ≥ 3k + 1

**Theorem 5.1.** For every k ≥ 2, Z(G_k) ≥ 3k + 1.

*Proof.* Let B be a minimum zero forcing set of G_k and fix any chronological forcing
process P (Lemma 2.2). For each block i let R_i, r_i be as in Definition 3.2. The
blocks partition V(G_k), so, using Corollary 3.2′ and then Lemma 4.1,

Z(G_k) = |B| = Σ_{i=1}^{k} |B ∩ V_i| ≥ Σ_{i=1}^{k} μ_i(R_i) ≥ Σ_{i=1}^{k} m_{type(i)}(r_i) ≥ Σ_{i=1}^{k} (4 − r_i) = 4k − Σ_{i=1}^{k} r_i.

(End blocks can only have r_i ≤ 1 and middle blocks r_i ≤ 2, so all cases are covered
by Lemma 4.1's table.) By Lemma 3.3, Σ r_i ≤ k − 1. Hence Z(G_k) ≥ 4k − (k−1) = 3k+1. ∎

**Interpretation (wavefront accounting).** Each bridge can hand the wavefront across
the cut at most once, and each handover discounts the receiving block's price by
exactly one start, from 4 down to no lower than 2. With k blocks and k − 1 possible
handovers the bill is at least 4k − (k − 1).

**In-situ validation of the entire §3–§5 pipeline** (`validate_theorem.py` §S4): for
k = 2, *all* 504 forcing 7-sets and *all* 1065 forcing 8-sets; for k = 3, *all* 20 268
forcing 10-sets (exhaustive over C(22,10) = 646 646 subsets); for k = 4, 5, 400 random
forcing sets each of sizes Z … Z+6 — in every case, under several independently
randomised chronological orders, the recorded in-forces satisfied Σ r_i ≤ k − 1 and
every block satisfied |B ∩ V_i| ≥ m(r_i). No violation found anywhere.

---

## 6. Upper bound: Z(G_k) ≤ 3k + 1

**Theorem 6.1.** The set
W_k := {a₁¹, a₂¹, b₁¹, b₂¹} ∪ ⋃_{i=2}^{k} {a₁^i, a₂^i, b₂^i}
(4 starts in block 1, 3 in every later block; |W_k| = 3k + 1) is a zero forcing set of
G_k. Hence Z(G_k) ≤ 3k + 1 and, with Theorem 5.1, **Z(G_k) = 3k + 1**.

*Proof.* We exhibit a chronological process and verify each force against the §1.1
neighbourhood tables; blocks are processed left to right, so when block i + 1's turn
comes, its in-vertex has just been forced across the bridge and nothing else in blocks
i+1, …, k is blue except its three W_k-starts.

*Block 1* (blue: a₁, a₂, b₁, b₂):
1. a₂ → b₃  (N(a₂) = {b₁, b₂, b₃}; b₁, b₂ blue)
2. b₃ → a₃  (N(b₃) = {a₁, a₂, a₃}; a₁, a₂ blue)
3. a₁ → s¹  (N(a₁) = {b₂, b₃, s}; b₂ blue, b₃ blue by step 1)
4. s¹ → in₂  (N(s¹) = {a₁, b₁, in₂}; a₁, b₁ blue) — the bridge force into block 2.

*Block i, 2 ≤ i ≤ k − 1* (blue: a₁^i, a₂^i, b₂^i, and s_in^i just forced from the left):
5. a₁ → b₃  (N(a₁) = {b₂, b₃, s_in}; b₂ blue, s_in blue)
6. b₃ → a₃  (N(b₃) = {a₁, a₂, a₃})
7. a₃ → b₁  (N(a₃) = {b₁, b₂, b₃})
8. a₂ → s_out  (N(a₂) = {b₁, b₃, s_out}; b₁ blue by step 7, b₃ by step 5)
9. s_out → in_{i+1}  (N(s_out) = {a₂, b₂, in_{i+1}}) — the bridge force into block i+1.
Block i is now entirely blue (a₁, a₂, b₂ started; s_in, b₃, a₃, b₁, s_out forced).

*Block k* (blue: a₁^k, a₂^k, b₂^k, and s^k just forced from the left; N(s^k) = {a₁, b₁, out_{k−1}}):
5′. a₁ → b₃  (N(a₁) = {b₂, b₃, s}; b₂, s blue)
6′. b₃ → a₃  (N(b₃) = {a₁, a₂, a₃})
7′. a₃ → b₁  (N(a₃) = {b₁, b₂, b₃})
All of block k is blue. Every vertex of G_k is coloured, so W_k forces. ∎

(For k = 2 the schedule degenerates to blocks 1 and k only; W_2 = {0,1,3,4,7,8,11} is
*exactly* the certified Z-witness of G14 in `..\certificate_g14.json`. Machine
validation §S5: W_k forces and |W_k| = 3k + 1 for all k ≤ 20 and k = 40, 60.)

---

## 7. The domination number: γ(G_k) = 2k + ⌊k/3⌋

Let D be a dominating set of G_k; write d_i := |D ∩ V_i|. Recall N[v] denotes the
closed neighbourhood, and "x dominates v" means v ∈ N[x].

### 7.1 Lower bound

**Lemma 7.1 (core isolation).** Every vertex that dominates a core vertex of block i
lies in V_i.

*Proof.* Fact (F1): all neighbours of core vertices are inside their block. ∎

**Lemma 7.2 (per-block demand).** d_i ≥ 2 for every i.

*Proof.* By Lemma 7.1, D ∩ V_i must dominate all 6 core vertices. A single vertex of
V_i dominates at most 4 core vertices (a core vertex: itself + its ≤ 3 core
neighbours; a subdivision vertex: its 2 core neighbours). 6 > 4. ∎

**Lemma 7.3 (classification of tight blocks).** If d_i = 2 then D ∩ V_i ⊆ C_i, and
D ∩ V_i is one of:

* middle block: {a₁,b₁}, {a₂,b₂}, {a₃,b₃} ("diagonal pairs");
* end block: {a₁,b₁}, or {a_x, b_y} with x, y ∈ {2,3}.

Moreover the subdivision vertices these pairs dominate are exactly:

* middle: {a₁,b₁} dominates s_in only; {a₂,b₂} dominates s_out only; {a₃,b₃} dominates
  neither.
* end: {a₁,b₁} dominates s; the other four pairs dominate no subdivision vertex.

*Proof.* The pair must dominate the 6-vertex core (Lemma 7.1 + Lemma 7.2's count).

(i) *No subdivision vertex can participate.* A subdivision vertex dominates exactly 2
core vertices (its two core neighbours, one "a" and one "b"), leaving 4 core vertices
— two a's and two b's — for the partner alone. But every vertex of V_i dominates at
most one a-vertex *or* at most one b-vertex of its own side: A is independent, so an
a-vertex dominates only itself among A (at most one of the two remaining a's — fails);
a b-vertex dominates only itself among B (fails on the two remaining b's); a second
subdivision vertex dominates exactly one a and one b (fails). So both members of the
pair are core vertices.

(ii) *Same-side pairs fail*: two a's dominate only 2 of the 3 a's (A independent);
symmetrically for b's.

(iii) *Cross pairs {a_x, b_y}*: the pair dominates all of A iff A∖{a_x} ⊆ N(b_y), and
all of B iff B∖{b_y} ⊆ N(a_x). Reading the §1.1 tables: in a middle block,
N_core(a₁) = {b₂,b₃}, N_core(a₂) = {b₁,b₃}, N_core(a₃) = {b₁,b₂,b₃} and symmetrically
for b's. For x = 1: B∖{b_y} ⊆ {b₂,b₃} forces y = 1, and N_core(b₁) = {a₂,a₃} ⊇ A∖{a₁} ✓
— so {a₁,b₁} works; for x = 2: y = 2 ✓ similarly; for x = 3: any y passes the first
test, but A∖{a₃} = {a₁,a₂} ⊆ N_core(b_y) only for y = 3 ✓. In an end block,
N_core(a₁) = {b₂,b₃} forces y = 1 as before, and N_core(b₁) = {a₂,a₃} ⊇ A∖{a₁} ✓; for
x ∈ {2,3}: N_core(a_x) = B, so the first test passes for every y, and the second test
A∖{a_x} ⊆ N_core(b_y) needs a₁ ∈ N_core(b_y), which holds iff y ∈ {2,3}
(N_core(b₂) = N_core(b₃) = A, while N_core(b₁) = {a₂,a₃} ∌ a₁ ✗).

The subdivision-domination statement follows by reading N(s_in) = {a₁, b₁, ·},
N(s_out) = {a₂, b₂, ·}, N(s) = {a₁, b₁, ·} off the tables. ∎

(Machine validation §S7(a): exhaustive enumeration of all ≤ 2-subsets of each block
type reproduces exactly these lists, including the subdivision-domination columns.)

**Lemma 7.4 (who can dominate a subdivision vertex).** N[s_in^i] = {s_in^i, a₁^i,
b₁^i, out_{i−1}}, N[s_out^i] = {s_out^i, a₂^i, b₂^i, in_{i+1}} (and for end blocks
N[s^1] = {s¹, a₁¹, b₁¹, in₂}, N[s^k] = {s^k, a₁^k, b₁^k, out_{k−1}}). In particular the
only vertex *outside* block i that dominates a subdivision vertex of block i is its
bridge partner, which is a subdivision vertex of the adjacent block. ∎ (Read off §1.1.)

**Lemma 7.5 (window lemma).** For every middle index 2 ≤ w ≤ k − 1:
d_{w−1} + d_w + d_{w+1} ≥ 7.

*Proof.* Suppose not. By Lemma 7.2 each of the three terms is ≥ 2, so all three equal
2. By Lemma 7.3, each of D ∩ V_{w−1}, D ∩ V_w, D ∩ V_{w+1} is a core pair — in
particular **no subdivision vertex of blocks w−1, w, w+1 is in D**. Block w is a middle
block; by Lemma 7.3 its pair dominates at most one of s_in^w, s_out^w, so at least one
of them — call it s — is not dominated from within block w (its in-block dominators are
its two core neighbours and itself, per Lemma 7.4). By Lemma 7.4 the only remaining
candidate dominator of s is its bridge partner, a subdivision vertex of block w−1 or
w+1 — none of which is in D. So s is undominated, contradiction. ∎

**Theorem 7.6.** γ(G_k) ≥ 2k + ⌊k/3⌋.

*Proof.* Write k = 3q + r with r ∈ {0, 1, 2} (so q = ⌊k/3⌋). Partition the first 3q
blocks into the q disjoint windows {3j−2, 3j−1, 3j}, j = 1, …, q. Each window's middle
index 3j−1 satisfies 2 ≤ 3j−1 ≤ 3q−1 ≤ k−1, so Lemma 7.5 applies:
Σ_{i ∈ window_j} d_i ≥ 7. The remaining r blocks each contribute d_i ≥ 2 (Lemma 7.2).
Summing over the partition of blocks: γ(G_k) = |D| = Σ d_i ≥ 7q + 2r = 2(3q + r) + q =
2k + ⌊k/3⌋. ∎

(Machine validation §S7(c): for k = 2 and k = 3, all minimum dominating sets were
enumerated exhaustively — 1 and 110 of them — and every one satisfies d_i ≥ 2, the
diagonal-pair classification at every tight block, and every window sum ≥ 7.)

### 7.2 Upper bound

**Theorem 7.7.** γ(G_k) ≤ 2k + ⌊k/3⌋.

*Proof.* We exhibit a dominating set D_k with |D_k| = 2k + ⌊k/3⌋, using the **donor**
block pattern {a₃, s_in, s_out} (3 vertices) and the diagonal pairs of Lemma 7.3. With
blocks 1-indexed and q = ⌊k/3⌋:

*Case r = k mod 3 ∈ {0, 1}:* donors at i ≡ 2 (mod 3); blocks i ≡ 1 (mod 3) get
{a₁, b₁}; blocks i ≡ 0 (mod 3) get {a₂, b₂}.

*Case r = 2:* donors at i ≡ 0 (mod 3); block 1 and blocks i ≡ 2 (mod 3) get {a₁, b₁};
blocks i ≡ 1 (mod 3), i ≥ 4, get {a₂, b₂}.

Count: in both cases there are exactly q donor blocks (r ∈ {0,1}: i = 2, 5, …; the
largest is ≤ k−1 since k ≢ 2 (mod 3); r = 2: i = 3, 6, …, 3q = k−2), so
|D_k| = 3q + 2(k − q) = 2k + q. When any donors exist (q ≥ 1; for k = 2 there are
none and D_2 is just two pairs), they are always middle blocks (2 ≤ i ≤ k − 1 in both
cases — for r ∈ {0,1} because k ≢ 2, for r = 2 because the largest donor index is
3q = k − 2), so {a₃, s_in, s_out} makes sense.

Domination check, vertex by vertex (using §1.1 and Lemma 7.3/7.4):

* *Core of a pair-block:* every diagonal/end pair listed dominates its block's core
  (Lemma 7.3). [{a₁,b₁} is in the end-block list and the middle-block list; {a₂,b₂}
  likewise; blocks 1 and k always receive a pair from their respective valid lists —
  block 1 gets {a₁,b₁}; block k gets: r = 0 ⇒ k ≡ 0 ⇒ {a₂,b₂} ✓ end-valid; r = 1 ⇒
  {a₁,b₁} ✓; r = 2 ⇒ k ≡ 2 ⇒ {a₁,b₁} ✓.]
* *Core of a donor block:* s_in dominates a₁, b₁; s_out dominates a₂, b₂; a₃ dominates
  itself and b₃ (a₃b₃ is an edge of every middle block). ✓
* *Subdivision vertices of a donor block:* s_in, s_out ∈ D. ✓
* *Subdivision vertices of pair-blocks:* check each position against the nearest donor.
  r ∈ {0,1}: block i ≡ 1 (mod 3): {a₁,b₁} dominates s_in^i (and for i = 1 or i = k the
  single s) ✓; if such a block is middle (then 4 ≤ i ≤ k−1), its s_out^i is dominated
  by donor i+1's s_in ∈ D via the bridge (Lemma 7.4; i+1 ≡ 2 (mod 3) and i+1 ≤ k, and
  i+1 ≠ k since k ≢ 2 (mod 3), so block i+1 is a donor). Block i ≡ 0 (mod 3):
  {a₂,b₂} dominates s_out^i; s_in^i is
  dominated by donor i−1's s_out ∈ D via the bridge ✓ (i−1 ≡ 2 is a donor, i−1 ≥ 2);
  if i = k (r = 0), the single s^k = s_in^k is dominated by donor k−1's s_out ✓.
  r = 2: block 1: {a₁,b₁} dominates s¹ ✓ (block 2 needs nothing from block 1). Block
  i ≡ 2 (mod 3): {a₁,b₁} dominates s_in^i (for i = k: the single s^k ✓, done); for
  middle such i, s_out^i is dominated by donor i+1 ≡ 0 ✓ (i+1 ≤ k−2 ✓ donor). Block
  i ≡ 1 (mod 3), i ≥ 4: {a₂,b₂} dominates s_out^i; s_in^i ← donor i−1 ≡ 0 ✓ (3 ≤ i−1 ≤
  3q ✓).

Every vertex of G_k is dominated, so D_k is a dominating set of the claimed size. ∎

(For k = 2 (r = 2, q = 0): D_2 = {a₁¹, b₁¹, a₁², b₁²} = {0, 3, 7, 10} — *exactly* the
certified γ-witness of G14. Machine validation §S6: D_k dominates with
|D_k| = 2k + ⌊k/3⌋ for all k ≤ 20 and k = 40, 60.)

**Corollary 7.8.** γ(G_k) = 2k + ⌊k/3⌋ = ⌊7k/3⌋ for all k ≥ 2. ∎

---

## 8. Main theorems

**Theorem A.** For every k ≥ 2: γ(G_k) = 2k + ⌊k/3⌋ and Z(G_k) = 3k + 1.
*Proof.* Theorems 5.1 + 6.1 and Corollary 7.8. ∎

**Theorem B.** Z(G_k) − γ(G_k) = 3k + 1 − 2k − ⌊k/3⌋ = k − ⌊k/3⌋ + 1 = ⌈2k/3⌉ + 1,
which is unbounded; with n = n(G_k) = 8k − 2 this equals ⌈(n+2)/12⌉ + 1. ∎

**Corollary C.** On the class of connected, cubic, triangle-free graphs — a subclass of
connected cubic diamond-free graphs under both readings of "diamond-free" (Lemma 1.1) —
the difference Z − γ is unbounded: for every constant c there is a member G with
Z(G) > γ(G) + c (any integer k ≥ 3(⌈c⌉ + 1) works, since then Z − γ ≥ 2(⌈c⌉+1) + 1 >
c). Hence no statement of the form
"Z(G) ≤ γ(G) + c for all connected cubic diamond-free G" is true for any constant c:
Conjecture 9 of arXiv:2406.19231 fails not by an accident of small constants but
catastrophically, at linear rate ≈ n/12 in the order of the graph. ∎

**Remarks.**
1. The certified finite data (table in §0) match the formulas at every point where
   exact values exist, including the previously-only-bounded Z value at k = 6, made
   exact by an independent computation (§9.3).
2. The family G_k is *not* bipartite (Lemma 1.1), so this theorem says nothing about
   the bipartite cubic subclass; see §10.
3. Within the proof, both inequalities are *locally tight*: m(r) = 4 − r is achieved
   in every automaton case (§4 upper bounds), the forcing witness W_k uses exactly one
   bridge crossing per bridge and exactly 4−r starts per block, and every minimum
   dominating set of G_2, G_3 realises the window bound with equality.
4. Davila's Conjecture 9 asked about Z ≤ γ + 2 ("and this bound is sharp"). The proven
   growth rate (Z − γ)/n → 1/12 on this family raises the natural follow-up of the
   optimal constant in sup (Z − γ)/n over connected cubic triangle-free graphs; we make
   no claim about it beyond ≥ 1/12.

---

## 9. Computational validation (what was machine-checked, and how to re-run)

All validation code is stdlib Python (exact bitmask arithmetic, no external
dependencies except `ortools` for the *optional* §9.3) and lives next to this file.

```
cd problems\p2-factory\kills\davila-conj9\theorem
python validate_theorem.py       # ~2-3 minutes; must print ALL CHECKS PASSED
python z_exact_extend.py         # optional, ortools; exact Z for k=6,7,8
```

### 9.1 Per-lemma map

| Lemma / claim | Validation (all in `validate_theorem.py`) |
|---|---|
| Construction §1.1 = certified artifacts | S0: rebuilt edge lists equal `chain_indep_k{2..8}.edges` verbatim |
| Lemma 1.1 (cubic, connected, triangle-free, n = 8k−2) | S1: k ≤ 30 |
| Lemma 4.1 values m_end = (4,3), m_mid = (4,3,2) | S2: brute force over all start sets × all grant sets; both r = 1 grants agree |
| §4 case tables, fort certificates, orbit coverage | S3: exhaustive no-symmetry re-check of every deficient set (including sets containing subdivision vertices); every fort verified as a fort; tables in `case_tables.md` machine-emitted; automorphism groups by brute force over all vertex permutations |
| §4 upper bounds (tightness) | S3: the four explicit witnesses force |
| Restriction Lemma 3.2 + Lemma 3.3 + Theorem 5.1 accounting | S4 (in situ): k = 2 all 504 forcing 7-sets (×8 random chronological orders) and all 1065 forcing 8-sets; k = 3 all 20 268 forcing 10-sets out of the full C(22,10) = 646 646 enumeration (×5 orders); k = 4, 5: 400 random forcing sets each of sizes Z…Z+6 (×4 orders). Checked each time: Σ r_i ≤ k−1 and |B ∩ V_i| ≥ m(r_i) for every block |
| Theorem 6.1 (W_k forces, size 3k+1) | S5: k ≤ 20 and k = 40, 60; W_2 = certified G14 witness |
| Theorem 7.7 (D_k dominates, size 2k+⌊k/3⌋) | S6: k ≤ 20 and k = 40, 60; D_2 = certified G14 witness |
| Lemma 7.3 classification (incl. sub-vertex domination columns) | S7(a): exhaustive over all ≤2-subsets of both block types |
| Lemma 7.1/(F1) core isolation | S7(b): k ≤ 8 directly on G_k |
| Lemmas 7.2, 7.3, 7.5 in situ | S7(c): k = 2, 3 — every minimum dominating set (1 resp. 110, exhaustively enumerated, γ re-confirmed) satisfies per-block ≥ 2, the pair classification, and all window sums ≥ 7 |
| Formulas vs certified table | S8: γ at k = 2…8, Z at k = 2…5, gap formula |

Result: **ALL CHECKS PASSED** (run of 2026-06-12).

### 9.2 Independent prior certification (inherited)

γ(G_k) exact for k ≤ 8 and Z(G_k) exact for k ≤ 5 were certified before this work by
exhaustive enumeration / pruned DFS in two languages plus a hostile Codex referee
(`..\WRITEUP.md` §3, §5, `..\VERIFICATION_LOG.md`). The present theorem reproduces
every one of those numbers.

### 9.3 New exact value at k = 6 (bonus, not part of the proof)

`z_exact_extend.py` computes Z exactly by the fort-cover loop: iteratively solve a
minimum hitting set ILP over discovered forts (CP-SAT; a valid lower bound on Z since
every forcing set hits every fort — Lemma 2.3) and, when the optimal hitting set
forces, its size *equals* Z. Each cut added is a minimum-size fort avoiding the current
candidate (found by a second CP-SAT model; every fort is re-verified by direct
definition before use). Output (run of 2026-06-12):

* **Z(G_6) = 19 = 3·6 + 1** — converged after 948 fort cuts (witness re-verified by
  closure). This turns the previously "upper bound only" k = 6 row exact by a method
  independent of this theorem, and it matches the theorem's prediction.
* k = 7: the loop reached the certified lower bound **Z(G_7) ≥ 21** (1 750+ fort cuts)
  but had not closed the final unit to 22 when the 10-minute compute budget expired;
  k = 8 was not attempted. For k = 7, 8 the exact values Z = 22, 25 therefore rest on
  the *theorem* (and the verified witnesses for ≤), not on an independent computation.

(Caveat: the k = 6 value and the k = 7 partial bound trust CP-SAT's optimality/
infeasibility claims for the two ILP models; the *theorem* does not depend on them.
The k ≤ 5 anchors have no such caveat — they were verified by exhaustive enumeration.)

---

## 10. Honest gap list

1. **Machine-assisted finite case analysis.** Lemma 4.1 (the heart of the lower bound)
   is a finite case analysis over ≤ C(8,3) = 56 start sets per claim. The tables in §4
   are complete and every row is hand-checkable in under a minute (a fort check is a
   ≤ 7-vertex, ≤ 3-neighbour count), and orbit sizes sum to the full binomial counts;
   but a referee who distrusts the symmetry bookkeeping must either check 15–20 sets
   per claim by hand or run `validate_theorem.py` (which checks all of them with no
   symmetry reduction). The same applies to the automorphism group orders (asserted by
   brute force over all permutations, not proven in prose beyond the generators
   exhibited).
2. **Not bipartite.** G_k contains 5-cycles, so Corollary C is for the triangle-free
   cubic class, not the bipartite cubic class. Whether Z − γ is unbounded on connected
   *bipartite* cubic graphs is open here. (A natural candidate — subdividing twice to
   preserve bipartiteness — changes the block automaton and was not analysed.)
3. **Rate optimality.** We prove Z − γ ≈ n/12 on this family but make no claim that
   1/12 is the extremal density for the class, nor any claim about how Z − γ behaves
   on other families; upper bounds on how fast the gap *can* grow on the class are
   not addressed here.
4. **The k = 6 exact Z value and k = 7 partial lower bound** (§9.3) rely on CP-SAT
   optimality (two ILP models), and the fort-cover run for k = 7 did **not** converge
   within budget (stopped at Z ≥ 21 of the predicted 22), so k = 7, 8 have no
   independent exact recomputation. This is decoration either way: the theorem covers
   all k ≥ 2 independently. The k ≤ 5 anchors are enumeration-exact.
5. **Scope of the Restriction Lemma.** Lemma 3.2 as stated uses two specific features
   of G_k: blocks partition V and all inter-block edges are bridges with subdivision
   endpoints (F2). It is *not* a general-purpose decomposition theorem; any reuse on
   another family must re-verify (F2)-style structure.
6. **Chronology subtleties.** The in-force sets R_i (and hence the per-block discount)
   depend on the chosen chronological order; the proof only needs *some* fixed complete
   order, and Lemma 2.2 guarantees one exists for any forcing set. The validation in
   §S4 deliberately randomises orders to probe exactly this point; no order-dependent
   violation was observed. The bound Σ r_i ≤ k − 1 is order-independent (Lemma 3.3).
7. **Definitional fidelity.** "Zero forcing" here is the standard (simple) zero
   forcing of the source conjecture (arXiv:2406.19231 §1.1, quoted verbatim in
   `..\WRITEUP.md`); no positive-semidefinite or fractional variants are addressed.
   Domination is standard. The diamond-free subgraph-vs-induced ambiguity is moot by
   triangle-freeness (Lemma 1.1).
