# Z − γ is unbounded on connected cubic triangle-free graphs: exact values γ(G_k) = ⌊7k/3⌋ and Z(G_k) = 3k + 1 for the chain family

**Slug:** `davila-conj9/theorem` · **Status:** complete proof draft (2026-06-12), every finite
ingredient machine-validated (`theorem/validate_gamma_exact.py`, 29/29 checks pass) ·
**Upgrades:** the conjectural §7 of `../WRITEUP.md` ("γ(G_k) = ⌊7k/3⌋ and Z(G_k) = 3k+1,
NOT proven") to a theorem.

---

## 0. Results

Let G_k (k ≥ 2) be the certified chain family of `../WRITEUP.md` (formal definition in §3
below; identical, edge-for-edge, to the files `chain_indep_k*.edges` — check **V1**): a
linear chain of k copies of K₃,₃, the two end copies with one subdivided edge, every
middle copy with two subdivided edges on independent (non-adjacent) edges, consecutive
subdivision vertices joined by bridges. G_k is connected, cubic, and triangle-free, with
n = 8k − 2 vertices.

> **Theorem A (domination, exact).** For every k ≥ 2, γ(G_k) = ⌊7k/3⌋.
>
> **Theorem B (zero forcing, exact).** For every k ≥ 2, Z(G_k) = 3k + 1.
>
> **Corollary C (unboundedness).** For every k ≥ 2,
> Z(G_k) − γ(G_k) = 3k + 1 − ⌊7k/3⌋ = ⌈(2k+3)/3⌉ → ∞.
> Writing n = 8k − 2, the gap equals ⌈(n+14)/12⌉ > n/12. Consequently **Z − γ is
> unbounded on connected cubic triangle-free graphs** — a fortiori on connected cubic
> diamond-free graphs under both readings of "diamond-free" — so no additive constant
> repairs Conjecture 9 of arXiv:2406.19231: for every c there is a connected cubic
> diamond-free graph with Z(G) > γ(G) + c.

The first exact values:

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|----|
| n | 14 | 22 | 30 | 38 | 46 | 54 | 62 | 70 | 78 |
| γ | 4 | 7 | 9 | 11 | 14 | 16 | 18 | 21 | 23 |
| Z | 7 | 10 | 13 | 16 | 19 | 22 | 25 | 28 | 31 |
| Z − γ | 3 | 3 | 4 | 5 | 5 | 6 | 7 | 7 | 8 |

Rows k = 2..5 reproduce the previously certified exact values (γ and Z both exhaustively
verified there in two independent implementations); rows k = 6, 7, 8 had γ certified
exact and only Z ≤ 19, 22, 25 certified — Theorem B now pins those Z values exactly
(the certified witnesses of sizes 19, 22, 25 are optimal). Per residue class:

- k ≡ 0 (mod 3): γ = 7k/3, Z − γ = (2k+3)/3;
- k ≡ 1 (mod 3): γ = (7k−1)/3, Z − γ = (2k+4)/3;
- k ≡ 2 (mod 3): γ = (7k−2)/3, Z − γ = (2k+5)/3.

**Proof architecture.**

- γ ≤ ⌊7k/3⌋: an explicit periodic dominating set D_k (§4).
- γ ≥ ⌊7k/3⌋: an interface dynamic program across the bridges — three boundary states
  per bridge, transfer matrix in the (min, +) semiring, all table entries proved by
  short case analyses and re-proved by exhaustive enumeration of all 2⁷/2⁸ subsets per
  block — plus a finitely verified min-plus periodicity v_{i+3} = v_i + 7 (§5).
- Z ≥ 3k + 1: a cut superadditivity lemma — Z(G) ≥ Σ_components Z(H_j) − |E′| for any
  deleted edge set E′ — applied to the k − 1 bridges, together with Z(S1) = Z(S2) = 4
  for the two block graphs (7 and 8 vertices; fort case analyses + exhaustive checks)
  (§6).
- Z ≤ 3k + 1: an explicit forcing set F_k whose forcing cascade is written out and
  proved block-by-block by induction (§7). F_2 is literally the certified witness for
  G14.

Every lemma with finite content is validated by `validate_gamma_exact.py` (check IDs
**V1**–**V12** cited inline; §9).

---

## 1. Frozen definitions

All definitions as in §1.1 of R. Davila, arXiv:2406.19231v2 (frozen in `../WRITEUP.md`).
G = (V, E) is a finite simple graph, N(v) the open and N[v] = N(v) ∪ {v} the closed
neighborhood.

- **Domination.** D ⊆ V is *dominating* if ∪_{v∈D} N[v] = V; γ(G) is the minimum size.
- **Zero forcing.** Given B ⊆ V ("blue"), the *color change rule* lets a blue vertex u
  with exactly one white neighbor v force v blue. B is a *zero forcing set* if iterating
  the rule colors all of V; Z(G) is the minimum size of a zero forcing set.

We use the standard closure formalism: B₀ = B, B_{t+1} = B_t ∪ {v : ∃u ∈ B_t with
N(u) \ B_t = {v}}, and cl(B) := ∪_t B_t (a fixpoint, reached in ≤ |V| steps). B is a
zero forcing set iff cl(B) = V.

---

## 2. Two standard lemmas (with proofs)

**Lemma 2.1 (monotonicity and serialization).**
(i) If B ⊆ B′ then cl(B) ⊆ cl(B′).
(ii) Call a sequence of single forces u₁→v₁, …, u_m→v_m *valid from B* if, setting
X₀ = B and X_ℓ = X_{ℓ−1} ∪ {v_ℓ}, we have u_ℓ ∈ X_{ℓ−1}, v_ℓ ∉ X_{ℓ−1} and
N(u_ℓ) \ X_{ℓ−1} = {v_ℓ} for every ℓ. Then X_m ⊆ cl(B) for every valid sequence, and
every valid sequence that cannot be extended ends at exactly cl(B). In particular:
cl(B) = V iff some valid sequence of single forces ends at V, and any such sequence
can be produced by performing the simultaneous process one force at a time.

*Proof.* (i) Induction on t shows B_t ⊆ cl(B′): if u ∈ B_t ⊆ cl(B′) forces v
(N(u) \ B_t = {v}), then N(u) \ cl(B′) ⊆ N(u) \ B_t = {v}; if v ∉ cl(B′) this says u
has v as its unique non-blue neighbor in the fixpoint cl(B′), so cl(B′) would not be a
fixpoint — contradiction; hence v ∈ cl(B′).

(ii) First, X_m ⊆ cl(B) by induction on ℓ with the identical fixpoint argument: if
X_{ℓ−1} ⊆ cl(B) then N(u_ℓ) \ cl(B) ⊆ N(u_ℓ) \ X_{ℓ−1} = {v_ℓ}, and u_ℓ ∈ cl(B), so
v_ℓ ∈ cl(B) (else cl(B) is not a fixpoint). Second, if the sequence cannot be extended,
X_m is a fixpoint of the simultaneous rule containing B; induction on t shows
B_t ⊆ X_m: if u ∈ B_t ⊆ X_m forces v ∉ X_m, then N(u) \ X_m ⊆ N(u) \ B_t = {v}, i.e.
N(u) \ X_m = {v}, so the single force u→v extends the sequence — contradiction. Hence
cl(B) ⊆ X_m ⊆ cl(B). ∎

**Lemma 2.2 (forts obstruct forcing).** Call ∅ ≠ F ⊆ V a *fort* if no vertex outside F
has exactly one neighbor in F. Then every zero forcing set intersects every fort.

*Proof.* Suppose B ∩ F = ∅. Induction on t: assume B_t ∩ F = ∅ and some u forces
v ∈ F at step t+1. Then u ∉ F, and v ∈ N(u) ∩ F, so |N(u) ∩ F| ≥ 2 (fort property);
pick w ∈ N(u) ∩ F, w ≠ v. Since F ∩ B_t = ∅, w ∉ B_t, so {v, w} ⊆ N(u) \ B_t,
contradicting |N(u) \ B_t| = 1. Hence cl(B) ∩ F = ∅ ≠ F and cl(B) ≠ V. ∎

(Forts in this sense are standard in the zero-forcing literature; both lemmas are
folklore, proved here to keep the document self-contained.)

---

## 3. The family G_k

**Construction (identical to `chain_study.chain(k, "indep")`; check V1).** For k ≥ 2,
G_k consists of blocks 1, …, k. Block i has vertex classes
A_i = {a₁, a₂, a₃} and B_i = {b₁, b₂, b₃} (superscripts i suppressed) and:

- **End blocks (i = 1 and i = k), 7 vertices:** all nine edges a_x b_y *except* a₁b₁,
  which is subdivided by a new vertex s (edges a₁s, b₁s). Block 1's s is its
  *out-port* q₁; block k's s is its *in-port* p_k.
- **Middle blocks (2 ≤ i ≤ k−1), 8 vertices:** all nine edges a_x b_y *except* a₁b₁
  and a₂b₂; a₁b₁ is subdivided by the *in-port* p_i (edges a₁p_i, b₁p_i) and a₂b₂ by
  the *out-port* q_i (edges a₂q_i, b₂q_i).
- **Bridges:** q_i p_{i+1} for i = 1, …, k−1.

In the 0-based labels of the `.edges` files, block i sits at offset o (o = 0 for i = 1,
o = 7 + 8(i−2) for i ≥ 2) with a₁a₂a₃ = o, o+1, o+2; b₁b₂b₃ = o+3, o+4, o+5;
s/p = o+6; q = o+7 (middle blocks).

Intra-block adjacency used throughout (read off the construction):

| block type | adjacency |
|---|---|
| end | a₁: b₂,b₃,s · a₂: b₁,b₂,b₃ · a₃: b₁,b₂,b₃ · b₁: a₂,a₃,s · b₂: a₁,a₂,a₃ · b₃: a₁,a₂,a₃ · s: a₁,b₁ (+ bridge) |
| middle | a₁: b₂,b₃,p · a₂: b₁,b₃,q · a₃: b₁,b₂,b₃ · b₁: a₂,a₃,p · b₂: a₁,a₃,q · b₃: a₁,a₂,a₃ · p: a₁,b₁ (+ bridge) · q: a₂,b₂ (+ bridge) |

**Lemma 3.1 (structure).** G_k is connected, 3-regular, triangle-free (hence
diamond-free under both the subgraph and the induced-subgraph reading), with
n = 8k − 2 vertices and 3n/2 edges. *(Machine check V2 for k ≤ 12.)*

*Proof.* Counting: 2·7 + (k−2)·8 = 8k − 2 vertices. Degrees: core vertices keep degree
3 (each loses at most subdivided incidences but gains the corresponding subdivision
vertex); each port has two core neighbors plus one bridge — degree 3. Connectivity:
each block is connected (K₃,₃ stays connected under edge subdivision) and the bridges
chain the blocks. Triangle-freeness: the only inter-block edges are bridges, and the
endpoints q_i, p_{i+1} of a bridge have no common neighbor (their other neighbors lie
in different blocks), so a triangle would lie inside one block; a block's core is
bipartite (classes A_i, B_i), so a triangle would use a port s/p/q, whose two in-block
neighbors (a_j and b_j for the subdivided edge a_j b_j) are non-adjacent — exactly the
edge that was deleted when subdividing. ∎

---

## 4. Theorem A, upper bound: an explicit dominating set of size ⌊7k/3⌋

**Definition (the set D_k).** Take, in block i:

- i = 1: {a₁, b₁};
- 2 ≤ i ≤ k−1 (middle blocks): {a₁, b₁} if i ≡ 2 (mod 3); {p_i, b₃, q_i} if i ≡ 0;
  {a₂, b₂} if i ≡ 1;
- i = k: {a₁, b₁} if k ≡ 2 (mod 3); {s, a₃, b₃} if k ≡ 0; {a₂, b₂} if k ≡ 1.

**Proposition 4.1.** D_k is a dominating set of G_k of size 2k + ⌊k/3⌋ = ⌊7k/3⌋.
Hence γ(G_k) ≤ ⌊7k/3⌋. *(Machine check V8 for k ≤ 60; D_2 = {0,3,7,10} is literally
the certified γ-witness of G14.)*

*Proof.* Size: every block contributes 2 except blocks i ≡ 0 (mod 3), which contribute
3; there are ⌊k/3⌋ such blocks in 1..k, and 2k + ⌊k/3⌋ = ⌊7k/3⌋ since 7k/3 = 2k + k/3.

Domination, by block type (using the §3 adjacency table):

- *Block 1, {a₁, b₁}:* N[a₁] ⊇ {a₁, b₂, b₃, s}, N[b₁] ⊇ {b₁, a₂, a₃, s} — all 7
  vertices, including the out-port s = q₁.
- *Middle i ≡ 2, {a₁, b₁}:* N[a₁] ⊇ {a₁, b₂, b₃, p_i}, N[b₁] ⊇ {b₁, a₂, a₃, p_i} —
  everything except q_i. The next block (i+1 ≡ 0) contains p_{i+1} ∈ D_k (as p or as
  s when i+1 = k, k ≡ 0), and p_{i+1} is the bridge neighbor of q_i. ✓
- *Middle i ≡ 0, {p_i, b₃, q_i}:* N[p_i] ⊇ {p_i, a₁, b₁}, N[b₃] = {b₃, a₁, a₂, a₃},
  N[q_i] ⊇ {q_i, a₂, b₂} — all 8 vertices. (Moreover p_i dominates q_{i−1} across the
  left bridge and q_i dominates p_{i+1} across the right bridge — used by the
  neighbors.)
- *Middle i ≡ 1, {a₂, b₂}:* N[a₂] = {a₂, b₁, b₃, q_i}, N[b₂] = {b₂, a₁, a₃, q_i} —
  everything except p_i; the previous block (i−1 ≡ 0) contains q_{i−1} ∈ D_k, the
  bridge neighbor of p_i. (Middle blocks with i ≡ 1 have i ≥ 4, so block i−1 ≥ 3 is a
  middle block ≡ 0.) ✓
- *Block k ≡ 2, {a₁, b₁}:* as for block 1 — all 7 vertices, including s = p_k.
- *Block k ≡ 0, {s, a₃, b₃}:* N[s] ⊇ {s, a₁, b₁}, N[a₃] = {a₃, b₁, b₂, b₃},
  N[b₃] = {b₃, a₁, a₂, a₃} — all 7; moreover s = p_k ∈ D_k dominates q_{k−1}, needed
  by block k−1 ≡ 2.
- *Block k ≡ 1, {a₂, b₂}:* N[a₂] = {a₂, b₁, b₂, b₃}, N[b₂] = {b₂, a₁, a₂, a₃} (end
  block adjacency) — everything except s; block k−1 ≡ 0 supplies q_{k−1} ∈ D_k, the
  bridge neighbor of s = p_k. ✓

Every vertex of every block is dominated, and every cross-block requirement is met by
the stated neighbor; the boundary cases (k = 2: blocks 1 and 2 both self-sufficient
type {a₁,b₁}; k = 3, 4 similarly traced above) introduce no exceptions. ∎

---

## 5. Theorem A, lower bound: interface dynamic program and min-plus periodicity

The blocks V₁, …, V_k partition V(G_k), and the only inter-block edges are the bridges
q_i p_{i+1}. Call a vertex of a block *interior* if it is not a port; interior closed
neighborhoods lie entirely inside their block (asserted programmatically for every
block — part of V4). Port neighborhoods: N[q_i] = {q_i} ∪ (N(q_i) ∩ V_i) ∪ {p_{i+1}},
N[p_i] = {p_i} ∪ (N(p_i) ∩ V_i) ∪ {q_{i−1}}.

**States.** For a set D ⊆ V and 1 ≤ i ≤ k−1, define the *interface state* σ_i(D) of
the bridge q_i p_{i+1}:

- **A** if q_i ∈ D;
- **B** if q_i ∉ D but some in-block neighbor of q_i is in D (q_i is dominated by its
  own block);
- **C** otherwise (q_i is dominated, if at all, only by p_{i+1}).

**Feasible local data.** For S₁ ⊆ V₁ and σ ∈ {A,B,C}, say (S₁, σ) is *feasible* if
every interior vertex of V₁ is dominated by S₁ within V₁ and σ is the state determined
by S₁ at q₁. For middle blocks and σ, σ′ ∈ {A,B,C}, say (σ, S_i, σ′) is *feasible* if

1. every interior vertex of V_i is dominated by S_i within V_i;
2. p_i is dominated: p_i ∈ S_i, or an in-block neighbor of p_i is in S_i, or σ = A;
3. if σ = C then p_i ∈ S_i (this is what dominates q_{i−1});
4. σ′ is the state determined by S_i at q_i.

For the last block, (σ, S_k) is *feasible* if 1–3 hold with p_k = s. Define

- v₁(σ) = min{|S₁| : (S₁, σ) feasible},
- M[σ→σ′] = min{|S| : (σ, S, σ′) feasible} (any middle block — they are pairwise
  isomorphic by translation of labels; the machine check V4 computes the table from
  the actual adjacency of *every* middle block of G₈ and verifies they coincide),
- c(σ) = min{|S_k| : (σ, S_k) feasible}.

**Lemma 5.1 (decomposition).** For every k ≥ 2,
γ(G_k) = min over σ₁, …, σ_{k−1} ∈ {A,B,C} of
v₁(σ₁) + Σ_{i=2}^{k−1} M[σ_{i−1}→σ_i] + c(σ_{k−1}).

*Proof.* (≥) Let D be a minimum dominating set, S_i = D ∩ V_i, σ_i = σ_i(D). Condition
1 holds in every block because interior closed neighborhoods stay inside the block.
Condition 2 holds because N[p_i] = {p_i} ∪ (N(p_i) ∩ V_i) ∪ {q_{i−1}} must meet D, and
q_{i−1} ∈ D is precisely σ_{i−1} = A. Condition 3: if σ_{i−1} = C, then by definition
q_{i−1} ∉ D and no in-block neighbor of q_{i−1} is in D, yet
N[q_{i−1}] = {q_{i−1}} ∪ (N(q_{i−1}) ∩ V_{i−1}) ∪ {p_i} meets D — forcing p_i ∈ D.
Condition 4 holds by definition of σ_i. So the state sequence is feasible with costs
Σ|S_i| = |D| = γ(G_k), and the right-hand side is ≤ γ(G_k).

(≤) Conversely, fix a feasible state sequence and minimizers S₁, …, S_k of the local
problems; let D = ∪S_i (a disjoint union, so |D| is the sum of the local costs). Every
interior vertex is dominated (condition 1). Every in-port p_i is dominated (condition
2: in-block, or σ_{i−1} = A means q_{i−1} ∈ S_{i−1} ⊆ D and q_{i−1} ∈ N(p_i)). Every
out-port q_i is dominated: if σ_i ∈ {A, B} by its own block (condition 4); if σ_i = C
then condition 3 applied at block i+1 gives p_{i+1} ∈ D ∩ N(q_i). So D dominates and
γ(G_k) ≤ the right-hand side. ∎

**Lemma 5.2 (the tables).** With state order (A, B, C):

v₁ = (3, 2, 2), c = (2, 2, 3), M = [σ→σ′] =

| M | →A | →B | →C |
|---|---|---|---|
| **A→** | 3 | 2 | 2 |
| **B→** | 3 | 3 | 2 |
| **C→** | 3 | 3 | 3 |

*(Machine check V4: exhaustive enumeration of all 2⁷ resp. 2⁸ subsets of every block of
G₈ reproduces exactly these tables.)*

*Proof (human-readable; every claim also covered by V4/V11).* Write "core" for the six
vertices A_i ∪ B_i of a block; cores are interior, so condition 1 forces S to dominate
the core within the block.

*Step 1: every entry is ≥ 2.* A single closed neighborhood covers at most 4 core
vertices (§3 table: a₃, b₃ cover 4; a₁, a₂, b₁, b₂ cover 3; ports cover 2), and the
core has 6 vertices.

*Step 2: which 2-sets dominate a core?* (Check V11.) In a middle block the closed core
neighborhoods are N[a₁]∩core = {a₁,b₂,b₃}, N[a₂]∩core = {a₂,b₁,b₃},
N[a₃]∩core = {a₃,b₁,b₂,b₃}, and symmetrically for b's; ports add {a₁,b₁} (p) and
{a₂,b₂} (q). A covering pair must consist of two sets of sizes 4+4, 4+3 or 3+3 whose
union is all 6. Sizes 4+4: {a₃, b₃} — works ({a₃,b₁,b₂,b₃} ∪ {b₃,a₁,a₂,a₃}). Size 4+3
with a₃: the partner must cover {a₁, a₂}, and the only vertex whose closed core
neighborhood contains both is b₃ — already counted; symmetrically for b₃. Sizes 3+3
must partition the core: the complement of N[a₁]∩core = {a₁,b₂,b₃} is {a₂,a₃,b₁} =
N[b₁]∩core ✓; the complement of N[a₂]∩core is {a₁,a₃,b₂} = N[b₂]∩core ✓; no other
3-set N[x]∩core has its complement of that form (the remaining candidates pair a with
a or b with b and miss a vertex), and ports (2 core vertices) cannot participate.
**Middle core pairs: exactly {a₁,b₁}, {a₂,b₂}, {a₃,b₃}.** The same analysis in an end
block (core = K₃,₃ − a₁b₁) gives exactly {a₁,b₁}, {a₂,b₂}, {a₂,b₃}, {a₃,b₂}, {a₃,b₃},
and **no pair {s, x} dominates an end core** (s covers only a₁, b₁ of the core, and no
single x covers {a₂, a₃, b₂, b₃}).

*Step 3: cost-2 cells of M.* A feasible cost-2 S must be one of the three middle core
pairs. Their profiles:

- {a₁, b₁}: p_i is dominated (a₁ ∈ N(p_i)); condition 3 fails for σ = C (p_i ∉ S);
  q_i undominated in-block → σ′ = C. Realizes (A→C) and (B→C) at cost 2.
- {a₂, b₂}: p_i not dominated in-block → needs σ = A; q_i dominated by a₂ → σ′ = B.
  Realizes (A→B) at cost 2.
- {a₃, b₃}: needs σ = A; σ′ = C. Realizes (A→C) again.

So the cost-2 cells are exactly (A→B), (A→C), (B→C); all other cells are ≥ 3.

*Step 4: cost-3 witnesses for the remaining cells.* (A→A): {a₃, b₃, q}. (B→A):
{a₁, b₁, q}. (B→B): {a₁, b₁, a₂}. (C→A): {p, b₃, q} (p covers a₁, b₁; b₃ covers
a₁, a₂, a₃; q covers a₂, b₂). (C→B): {p, a₂, b₂}. (C→C): {p, a₃, b₃}. Each is checked
against conditions 1–4 directly with the §3 table. This proves the matrix M.

*Step 5: v₁ and c.* v₁(A): s ∈ S is required, and by Step 2 no {s, x} dominates the
end core, so v₁(A) ≥ 3; witness {s, a₃, b₃}. v₁(B): need s ∉ S, N(s) ∩ S ∋ a₁ or b₁:
the end-core pair {a₁, b₁} qualifies, so v₁(B) = 2. v₁(C) = 2 via {a₂, b₂}. c(A): with
σ = A, q_{k−1} ∈ D dominates s, so {a₂, b₂} (an end-core pair) suffices: c(A) = 2.
c(B): s must be dominated in-block; {a₁, b₁} does it: c(B) = 2. c(C): condition 3
forces s ∈ S, and no {s, x} dominates the core, so c(C) = 3; witness {s, a₃, b₃}. ∎

**Lemma 5.3 (min-plus shift invariance).** Define v_i ∈ ℤ³ by v₁ as above and
v_i(σ′) = min_σ [v_{i−1}(σ) + M[σ→σ′]] for 2 ≤ i ≤ k−1, and
γ_DP(k) = min_σ [v_{k−1}(σ) + c(σ)]. Then for any vector w and constant t,
min_σ[(w+t)(σ) + M[σ→σ′]] = min_σ[w(σ) + M[σ→σ′]] + t and likewise for the closing
functional. (Immediate: constants pull out of minima.) Consequently, if v_{i₀+3} =
v_{i₀} + 7 for some i₀, then v_{i+3} = v_i + 7 for **all** i ≥ i₀, and
γ_DP(k+3) = γ_DP(k) + 7 for all k ≥ i₀ + 1.

**Proposition 5.4 (period certificate).** v₁ = (3,2,2), v₂ = (5,5,4), v₃ = (7,7,7),
v₄ = (10,9,9) = v₁ + 7. *(Machine check V6 verifies v_{i+3} = v_i + 7 for all i along
a chain of length 40.)*

*Proof.* Direct evaluation with Lemma 5.2 (order A,B,C):
v₂(A) = min(3+3, 2+3, 2+3) = 5; v₂(B) = min(3+2, 2+3, 2+3) = 5;
v₂(C) = min(3+2, 2+2, 2+3) = 4.
v₃(A) = min(5+3, 5+3, 4+3) = 7; v₃(B) = min(5+2, 5+3, 4+3) = 7;
v₃(C) = min(5+2, 5+2, 4+3) = 7.
v₄(A) = min(7+3, 7+3, 7+3) = 10; v₄(B) = min(7+2, 7+3, 7+3) = 9;
v₄(C) = min(7+2, 7+2, 7+3) = 9. ∎

**Theorem A.** γ(G_k) = ⌊7k/3⌋ for all k ≥ 2.

*Proof.* Lower bound: by Lemma 5.1, γ(G_k) = γ_DP(k). Closing values:
γ_DP(2) = min(3+2, 2+2, 2+3) = 4; γ_DP(3) = min(5+2, 5+2, 4+3) = 7;
γ_DP(4) = min(7+2, 7+2, 7+3) = 9. By Proposition 5.4 and Lemma 5.3,
γ_DP(k+3) = γ_DP(k) + 7 for all k ≥ 2. Since ⌊7(k+3)/3⌋ = ⌊7k/3⌋ + 7 and the base
values 4, 7, 9 equal ⌊7k/3⌋ at k = 2, 3, 4, induction gives γ_DP(k) = ⌊7k/3⌋ for all
k ≥ 2. The matching upper bound is Proposition 4.1. ∎

*(Machine checks V5, V7, V12: the DP reproduces the seven independently certified
values γ = 4, 7, 9, 11, 14, 16, 18 at k = 2..8, equals ⌊7k/3⌋ for k ≤ 60, agrees with
a from-scratch exhaustive enumeration at k = 2, 3 — no 3-set of C(14,3), no 6-set of
C(22,6) dominates — and with CP-SAT ILP optima for k ≤ 12.)*

---

## 6. Theorem B, lower bound: cut superadditivity and the block forcing numbers

**Lemma 6.1 (superadditivity under edge deletion).** Let G be a graph, E′ ⊆ E(G), and
let H₁, …, H_t be the connected components of G − E′. Then
Z(G) ≥ Σ_j Z(H_j) − |E′|.

*Proof.* Let B be a minimum zero forcing set of G and fix a valid serialized run
u₁→v₁, …, u_m→v_m from B ending at V (Lemma 2.1(ii)). Call step ℓ *crossing* if
u_ℓ v_ℓ ∈ E′. Distinct crossing steps use distinct edges of E′: after a crossing force
along e both endpoints of e are blue, and any force's target must be white at its
time, so no later force can target an endpoint of e along e. Hence there are at most
|E′| crossing steps. For each j let I_j = {v_ℓ : step ℓ crossing, v_ℓ ∈ V(H_j)};
since each crossing step has its (unique, never re-forced) target in exactly one
component, Σ_j |I_j| ≤ |E′|.

*Claim:* (B ∩ V(H_j)) ∪ I_j is a zero forcing set of H_j. Let K =
cl_{H_j}((B ∩ V(H_j)) ∪ I_j); we show by induction on ℓ that X_ℓ ∩ V(H_j) ⊆ K, where
X_ℓ is the blue set after step ℓ in G. Base: X₀ ∩ V(H_j) = B ∩ V(H_j) ⊆ K. Step ℓ with
v_ℓ ∈ V(H_j): if ℓ is crossing, v_ℓ ∈ I_j ⊆ K. Otherwise u_ℓ v_ℓ ∈ E(G) \ E′ is an
edge of G − E′, so u_ℓ lies in the same component H_j, and u_ℓ ∈ X_{ℓ−1} ∩ V(H_j) ⊆ K.
Validity in G gives N_G(u_ℓ) \ X_{ℓ−1} = {v_ℓ}; since N_{H_j}(u_ℓ) ⊆ N_G(u_ℓ) and, by
induction, N_{H_j}(u_ℓ) ∩ X_{ℓ−1} ⊆ K, we get N_{H_j}(u_ℓ) \ K ⊆ {v_ℓ}. If v_ℓ ∉ K,
then u_ℓ ∈ K has exactly one neighbor of H_j outside K, namely v_ℓ, contradicting that
K is a closure fixpoint. So v_ℓ ∈ K. Since the run ends with all of V blue,
V(H_j) ⊆ K, proving the claim.

Therefore |B ∩ V(H_j)| ≥ Z(H_j) − |I_j| for every j, and summing over j (the blocks
partition V):  Z(G) = |B| ≥ Σ_j Z(H_j) − Σ_j |I_j| ≥ Σ_j Z(H_j) − |E′|. ∎

*(Remark: Lemma 6.1 also follows by iterating the known edge-spread inequality
Z(G − e) ≤ Z(G) + 1 — C.J. Edholm, L. Hogben, M. Huynh, J. LaGrange, D.D. Row,
"Vertex and edge spread of zero forcing number, maximum nullity, and minimum rank of a
graph", Linear Algebra Appl. 436 (2012) 4352–4372 — together with additivity of Z over
disjoint unions. The self-contained proof above keeps the document independent of the
citation.)*

Deleting the k−1 bridges of G_k leaves exactly the k blocks as components: two copies
of **S1** (K₃,₃ with one edge subdivided, 7 vertices) and k−2 copies of **S2** (K₃,₃
with two independent edges subdivided, 8 vertices), all middle blocks being isomorphic
by translation.

**Lemma 6.2.** Z(S1) = 4 and Z(S2) = 4.

*Proof.* Upper bounds: in S1, {a₁, a₂, b₁, b₂} forces (a₂→b₃, b₂→a₃, a₁→s; all seven
vertices are then blue); in S2, {p, a₁, a₂, b₂} forces (p→b₁, a₁→b₃, a₂→q, b₂→a₃;
all eight vertices are then blue). Lower bounds
(≥ 4 ⟺ no 3-set forces) — *machine check V3 settles both exhaustively (all C(7,3)=35
resp. C(8,3)=56 closures computed; none is V). Human-readable proofs via Lemma 2.2:*

*S1.* The following are forts of S1 (each verified against the §3 end-block adjacency
in one line: every outside vertex has 0 or ≥ 2 neighbors inside):
F₁ = {a₂,a₃}, F₂ = {b₂,b₃}, F₃ = {a₁,a₃,s}, F₄ = {b₁,b₃,s}, F₅ = {a₁,a₃,b₁,b₃}.
Let |B| = 3 force S1. B meets F₁ and F₂ (Lemma 2.2); since a₂↔a₃ and b₂↔b₃ are
automorphisms of S1, assume WLOG a₂, b₂ ∈ B; let z be the third vertex. If z = s,
B misses F₅. If z ∈ {a₁, a₃}, B misses F₄. If z ∈ {b₁, b₃}, B misses F₃. Contradiction
in all cases, so Z(S1) ≥ 4.

*S2.* S2 has automorphisms α: a_i↔b_i (fixing p, q) and β: a₁↔a₂, b₁↔b₂, p↔q (fixing
a₃, b₃); automorphic images of forts are forts. The following eleven sets are forts of
S2 (same one-line verification with the §3 middle-block adjacency; each is
machine-verified to be a fort, check V13 — this is *not* claimed to be a complete list
of S2's forts, only the ones the case analysis uses; S2 has 14 inclusion-minimal
forts in total): G₁ = {a₁,a₃,p}, G₂ = {a₂,a₃,q}, G₃ = {b₁,b₃,p}, G₄ = {b₂,b₃,q},
G₅ = {a₁,a₂,b₁,b₂}, G₆ = {a₁,a₃,b₁,b₃}, G₆′ = β(G₆) = {a₂,a₃,b₂,b₃},
G₇ = {a₁,a₂,p,q}, G₈ = {b₁,b₂,p,q}, G₉ = {a₁,a₃,b₁,q}, G₁₀ = α(G₉) = {a₁,b₁,b₃,q}.
Let |B| = 3 force S2; by Lemma 2.2, B meets every fort above.

Case (a): p, q ∈ B, third vertex z. Then z ∈ G₅ ∩ G₆ ∩ G₆′; but G₅ ∩ G₆ = {a₁, b₁}
and {a₁, b₁} ∩ G₆′ = ∅. Impossible.

Case (b): exactly one of p, q ∈ B; by β assume p ∈ B. Meeting G₂ and G₄ (which avoid
p) forces B = {p, x, y} with x ∈ {a₂, a₃} and y ∈ {b₂, b₃}. All four combinations miss
a fort: {p,a₂,b₂} misses G₆; {p,a₂,b₃} misses G₉; {p,a₃,b₂} misses G₁₀;
{p,a₃,b₃} misses G₅.

Case (c): p, q ∉ B. Meeting G₁, G₂, G₃, G₄ means B meets each of {a₁,a₃}, {a₂,a₃},
{b₁,b₃}, {b₂,b₃}. If a₃ ∉ B then a₁, a₂ ∈ B and the single remaining vertex must meet
both {b₁,b₃} and {b₂,b₃}, so B = {a₁,a₂,b₃} — which misses G₈. Symmetrically (α) if
b₃ ∉ B then B = {a₃,b₁,b₂} — which misses G₇. If a₃, b₃ ∈ B with third vertex z
(z ∈ {a₁,a₂,b₁,b₂} since p, q ∉ B): if z ∈ {a₁,a₂} then B misses G₈; if z ∈ {b₁,b₂}
then B misses G₇.

Contradiction in all cases, so Z(S2) ≥ 4. ∎

**Theorem 6.3 (zero forcing lower bound).** Z(G_k) ≥ 3k + 1 for all k ≥ 2.

*Proof.* Apply Lemma 6.1 with E′ = the k−1 bridges:
Z(G_k) ≥ 2·Z(S1) + (k−2)·Z(S2) − (k−1) = 8 + 4(k−2) − (k−1) = 3k + 1. ∎

*(Machine check V10: the previously certified exact values Z = 7, 10, 13, 16 at
k = 2..5 — each proved there by exhaustive search over all smaller sets in two
independent implementations — equal 3k+1 exactly, confirming the bound is tight where
exact data exists.)*

---

## 7. Theorem B, upper bound: an explicit forcing set of size 3k + 1

**Definition (the set F_k).** F_k = {a₁, a₂, b₁, b₂ of block 1} ∪ {a₁, a₂, b₂ of
block i : 2 ≤ i ≤ k}. |F_k| = 4 + 3(k−1) = 3k + 1.

**Proposition 7.1.** cl(F_k) = V(G_k); hence Z(G_k) ≤ 3k + 1. *(Machine check V9 for
k ≤ 60; F_2 = {0,1,3,4,7,8,11} is literally the certified Z-witness of G14.)*

*Proof.* We exhibit a valid serialized run (Lemma 2.1(ii)) and prove by induction on i
the invariant: *immediately after the out-port q_i performs its crossing force
q_i → p_{i+1}, all of blocks 1..i and the vertex p_{i+1} are blue, and no vertex of
blocks i+1..k other than p_{i+1} and the initial set is blue.*

*Block 1* (initially blue: a₁, a₂, b₁, b₂; adjacency from §3, end block):
a₂ (neighbors b₁✓, b₂✓, b₃) forces b₃; b₂ (a₁✓, a₂✓, a₃) forces a₃; a₁ (b₂✓, b₃✓, s)
forces s; now block 1 is entirely blue and s = q₁ (a₁✓, b₁✓, p₂) forces p₂. Every
listed force is valid: each forcer's full G_k-neighborhood except the target is blue
at its turn (no vertex of block 1 has a neighbor outside block 1 except s, whose
outside neighbor is exactly the target p₂).

*Middle block i, 2 ≤ i ≤ k−1* (initially blue: a₁, a₂, b₂; p_i just forced; by the
invariant q_{i−1} is blue): p_i (a₁✓, b₁, q_{i−1}✓) forces b₁; a₁ (b₂✓, b₃, p_i✓)
forces b₃; a₂ (b₁✓, b₃✓, q_i) forces q_i; b₂ (a₁✓, a₃, q_i✓) forces a₃; now block i is
entirely blue and q_i (a₂✓, b₂✓, p_{i+1}) forces p_{i+1}. Again every forcer's full
neighborhood except its target is blue, including the bridge neighbors (q_{i−1} for
p_i; p_{i+1} is the target for q_i).

*Block k* (initially blue: a₁, a₂, b₂; s = p_k just forced; q_{k−1} blue):
s (a₁✓, b₁, q_{k−1}✓) forces b₁; a₂ (b₁✓, b₂✓, b₃) forces b₃; b₂ (a₁✓, a₂✓, a₃)
forces a₃. Block k — and with it all of V(G_k) — is blue. (For k = 2, block 2 is
handled by this case directly after block 1.) ∎

**Theorem B.** Z(G_k) = 3k + 1 for all k ≥ 2. *(Theorem 6.3 + Proposition 7.1.)* ∎

---

## 8. Main theorem

**Theorem (main).** For every k ≥ 2, the graph G_k is connected, cubic, and
triangle-free (hence diamond-free whether "diamond-free" is read as forbidding a
diamond subgraph or an induced diamond), with n = 8k − 2 vertices,

γ(G_k) = ⌊7k/3⌋,  Z(G_k) = 3k + 1,  Z(G_k) − γ(G_k) = ⌈(2k+3)/3⌉ = ⌈(n+14)/12⌉.

*Proof.* Lemma 3.1, Theorem A, Theorem B; the gap identity:
3k + 1 − ⌊7k/3⌋ = 3k + 1 + ⌈−7k/3⌉ = ⌈(9k + 3 − 7k)/3⌉ = ⌈(2k+3)/3⌉, and substituting
k = (n+2)/8 gives (2k+3)/3 = (n+14)/12 (both numerators are divisible by 3
simultaneously, so the ceilings agree). ∎

**Corollary C.** sup {Z(G) − γ(G)} = ∞ over connected cubic triangle-free graphs G,
the gap exceeding n/12 along the family G_k. In particular, for every constant c ≥ 0
there is a connected, cubic, diamond-free graph (under both readings) with
Z(G) > γ(G) + c — e.g. G_k for any k > (3c − 3)/2 — so Conjecture 9 of
arXiv:2406.19231 ("Z(G) ≤ γ(G) + 2 for connected cubic diamond-free G") fails by an
unbounded margin, and no weakened form Z ≤ γ + c with constant c holds on this class. ∎

(For calibration: the known general bound for cubic graphs is Z ≤ 2γ-type linear-in-γ
behavior; our family has Z/γ → 9/7, so the *additive* gap is unbounded while the
*ratio* stays bounded — consistent with Z ≤ 2γ.)

---

## 9. Computational validation

Everything with finite content was validated by
`theorem/validate_gamma_exact.py` (pure stdlib Python except the optional V12;
runtime ≈ 1–2 minutes):

```
cd problems\p2-factory\kills\davila-conj9\theorem
python validate_gamma_exact.py     # prints PASS per check; exit 0 iff all pass
```

| check | content | status |
|---|---|---|
| V1 | construction = certified edge files `chain_indep_k{2..8}.edges`, edge-for-edge | PASS |
| V2 | G_k connected, cubic, triangle-free, n = 8k−2 (k ≤ 12) | PASS |
| V3 | Z(S1) = 4 and Z(S2) = 4, exhaustive over all 3-subsets (35; 56) + 4-witnesses | PASS |
| V4 | DP tables v₁ = (3,2,2), M = [[3,2,2],[3,3,2],[3,3,3]], c = (2,2,3) by exhaustive enumeration of all subsets of every block; all middle blocks give identical tables | PASS |
| V5 | DP = certified γ at k = 2..8 (4,7,9,11,14,16,18); DP = ⌊7k/3⌋ for k ≤ 60 | PASS |
| V6 | min-plus periodicity v_{i+3} = v_i + 7, all i, chain of length 40 | PASS |
| V7 | independent brute force: no 3-set dominates G₂ (C(14,3)); no 6-set dominates G₃ (C(22,6)); no 6-set forces G₂ (C(14,6)) | PASS |
| V8 | explicit D_k dominates, |D_k| = ⌊7k/3⌋, k ≤ 60; D₂ = certified γ-witness of G14 | PASS |
| V9 | explicit F_k forces, |F_k| = 3k+1, k ≤ 60; F₂ = certified Z-witness of G14 | PASS |
| V10 | certified exact Z at k = 2..5 equals 3k+1 (7,10,13,16) | PASS |
| V11 | core-pair classifications used in Lemma 5.2 (middle: exactly 3 pairs; end: exactly 5 pairs; no {s,x}) | PASS |
| V13 | every named object in Lemma 6.2: the 5 S1 forts, the 11 S2 forts, the four automorphisms used in WLOG steps, and both 4-element forcing witnesses | PASS |
| V12 | (optional) CP-SAT ILP γ optimum = ⌊7k/3⌋ for k ≤ 12 | PASS |

Cross-validation against pre-existing, independently produced certificates: the γ
values at k = 2..8 and Z values at k = 2..5 used in V5/V10 were certified before this
document existed, by exhaustive search in two languages (Python + Rust) and re-proved
by a hostile Codex referee (see `../WRITEUP.md` §5, `../certificate_chain_family.json`,
and `../rust_check/`); none of that machinery is reused by the validation script.

---

## 10. Honest gap list and remarks

1. **Finite computer checks are load-bearing but redundant.** Lemma 5.2 (nine matrix
   entries + six boundary entries) and Lemma 6.2 (Z(S1), Z(S2) ≥ 4) are each proved
   twice: by hand (case analyses above, which a referee can verify with pencil and the
   §3 adjacency table) and by exhaustive machine enumeration (V3, V4, V11; search
   spaces ≤ 2⁸ per block). Neither proof path depends on the other. The hand proofs of
   Lemma 6.2 additionally rely on sixteen claimed forts (five for S1, eleven for S2);
   each fort claim is a one-line verification, and every named fort, automorphism, and
   forcing witness is individually machine-verified (V13). The displayed fort lists
   are the ones the case analyses use, not complete enumerations (S2 has 14
   inclusion-minimal forts).
2. **What "exhaustive" means here.** The base data the theorems are checked against
   (γ at k ≤ 8, Z at k ≤ 5) are prior exhaustive-search certificates from
   `../WRITEUP.md`; this document's proofs do not *depend* on them — they are used
   only as cross-validation (V5, V10). The theorems themselves rest on Lemmas 3.1,
   5.1–5.3, 6.1–6.2, Propositions 4.1, 5.4, 7.1, all proved here.
3. **Bipartite case remains open.** G_k is triangle-free but *not* bipartite
   (subdividing one edge of K₃,₃ creates 5-cycles). Whether Z − γ is unbounded on
   connected cubic triangle-free *bipartite* graphs is not addressed by this document.
   So the theorem statement "unbounded on connected cubic triangle-free graphs" is
   final here; "(bipartite, if true)" from the task brief is **not** established.
4. **Class fidelity to Davila's Conjecture 9.** The conjecture's class is connected
   cubic diamond-free; triangle-free implies diamond-free under both the subgraph and
   the induced readings (a diamond contains triangles), so Corollary C legitimately
   speaks to the conjecture's class. We do not claim anything about graphs that are
   diamond-free but contain triangles.
5. **Citation hedging.** The remark after Lemma 6.1 attributes the edge-spread
   inequality |Z(G) − Z(G−e)| ≤ 1 to Edholm–Hogben–Huynh–LaGrange–Row (LAA 436, 2012).
   The proof given here is self-contained, so nothing depends on that attribution.
   Likewise "fort" terminology follows the zero-forcing literature (Fast–Hicks);
   Lemma 2.2 is proved from scratch.
6. **Rate optimality not claimed.** The family gives gap ≈ n/12. We make no claim that
   n/12 is the extremal growth rate of Z − γ on connected cubic triangle-free graphs
   (denser block gadgets might do better); only unboundedness plus this explicit rate.
7. **k = 1 excluded.** G_1 is not defined by the construction (a single block with one
   subdivided edge has a degree-2 vertex and is not cubic); all statements are for
   k ≥ 2.
8. **DP-state economy.** The 3-state interface DP is exact for this family because the
   bridge is the unique inter-block edge and domination "sees" only distance 1 across
   it. Nothing in §5 is heuristic: Lemma 5.1 is an unconditional equality.

---

## 11. Provenance

- Construction and certified base data: `../WRITEUP.md`, `../certificate_g14.json`,
  `../certificate_chain_family.json`, `../chain_indep_k*.edges`, `../rust_check/`
  (all 2026-06-11).
- This document and `validate_gamma_exact.py`: 2026-06-12.
- Validation suite: 29/29 checks PASS (2026-06-12, Python 3.11, Windows; V12 via
  OR-Tools CP-SAT).
- **Hostile referee review (Codex GPT-5.5, full shell + network, 2026-06-12, threadId
  `019eba75-cd26-7b91-8ce5-475b7f25c74f`): VERDICT "ACCEPT WITH MINOR FIXES" — "No
  fatal or major flaw found. The theorem survives the attack."** Codex independently
  rebuilt S1/S2 from the definitions (not the validator) and re-derived Z(S1) = Z(S2)
  = 4; recomputed the DP tables v₁, M, c and γ_DP(k) = 4,7,9,11,14,16,18,21,23 for
  k = 2..10; checked D_k and F_k for k ∈ {2,3,4,5,6,9,10} including legality of every
  cascade force with bridge neighbors; brute-forced γ and Z at k = 2,3; stress-tested
  Lemma 6.1 on all graphs up to n = 5 against all deleted-edge sets (including
  non-cut edges); verified the arithmetic identities; confirmed the
  Edholm–Hogben–Huynh–LaGrange–Row citation (LAA 436(12), 2012, pp. 4352–4372, DOI
  10.1016/j.laa.2010.10.015) and the edge-spread inequality −1 ≤ Z(G) − Z(G−e) ≤ 1;
  and re-ran this validation suite (29/29 PASS). The three minor wording fixes it
  requested (fort-list completeness wording, "s exhausts the graph", fort count) are
  applied in this version.
