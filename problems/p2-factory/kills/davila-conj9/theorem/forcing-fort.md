# Z − γ is unbounded on connected cubic triangle-free graphs: a fort-based proof of Z(G_k) = 3k + 1 and γ(G_k) = ⌊7k/3⌋

**File:** `theorem/forcing-fort.md` · **Date:** 2026-06-12 · **Lens:** zero forcing via **forts**
(fort obstruction, fort-transversal characterization, per-block fort certificates).
**Companion artifacts:** `theorem/validate_forts.py` (validates every finite claim of this
document; run of 2026-06-12: **ALL CHECKS PASSED**), `theorem/fort_tables.md` (machine-emitted
orbit/fort certificate tables, reproduced verbatim in §4), parent `..\WRITEUP.md` (the certified
refutation of Conjecture 9 of arXiv:2406.19231, whose conjectural §7 this document upgrades to a
theorem). Sibling proofs of the same theorem through different lenses:
`theorem/failed-forcing.md` (wavefront/restriction argument), `theorem/gamma-exact.md`
(interface dynamic program); the three documents share the graphs and the certified anchors but
were written and validated independently.

---

## 0. Results

For a finite simple graph G, γ(G) is the domination number and Z(G) the zero forcing number
(standard color-change rule; definitions in §2). Let G_k (k ≥ 2) be the chain family of
`..\WRITEUP.md` — edge-for-edge identical to the certified artifact files `chain_indep_k*.edges`
(machine check **F1**): k blocks, each a copy of K₃,₃; the two end blocks have one subdivided
edge, every middle block has two subdivided edges (on independent edges); consecutive
subdivision vertices are joined by bridges. G₂ = G14 is the 14-vertex counterexample that
refuted Conjecture 9. G_k is connected, cubic, and triangle-free, with n = 8k − 2 vertices.

> **Theorem A.** For every k ≥ 2:  γ(G_k) = ⌊7k/3⌋  and  Z(G_k) = 3k + 1.
>
> **Theorem B.** For every k ≥ 2:
> Z(G_k) − γ(G_k) = 3k + 1 − ⌊7k/3⌋ = ⌈2k/3⌉ + 1 → ∞.
> In terms of n = 8k − 2 the gap is ⌈(n + 14)/12⌉ > n/12.
>
> **Corollary C.** Z − γ is **unbounded** on the class of connected, cubic, triangle-free
> graphs — a fortiori on connected cubic diamond-free graphs under both readings of
> "diamond-free" (a diamond contains a triangle). Hence no additive weakening
> "Z(G) ≤ γ(G) + c" of Conjecture 9 of arXiv:2406.19231 holds for any constant c.

Consistency with the independently certified exact values (exhaustive Python + Rust, hostile
Codex referee; `..\WRITEUP.md` §3, §5):

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| n | 14 | 22 | 30 | 38 | 46 | 54 | 62 |
| γ certified | 4 | 7 | 9 | 11 | 14 | 16 | 18 |
| ⌊7k/3⌋ | 4 | 7 | 9 | 11 | 14 | 16 | 18 |
| Z certified | 7 | 10 | 13 | 16 | ≤19 | ≤22 | ≤25 |
| 3k + 1 | 7 | 10 | 13 | 16 | 19 | 22 | 25 |
| gap | 3 | 3 | 4 | 5 | 5 | 6 | 7 |

(k = 6, 7, 8: γ was certified exact, Z only as an upper bound; Theorem A settles
Z(G₆) = 19, Z(G₇) = 22, Z(G₈) = 25 — the certified witnesses were optimal.)

**Proof architecture (the fort lens).**

1. Every zero forcing set meets every fort; in fact the zero forcing sets are *exactly* the
   transversals of the fort hypergraph (§2). So Z is governed by forts.
2. The forts of G_k that fit inside a single block are classified (§3): they yield
   Z(G_k) ≥ 2k + 2 with pairwise disjoint *supports* — the honest ceiling of purely
   block-local fort counting, strictly below γ ≈ 7k/3. Something must carry the bridges.
3. The repair (§4–§5): delete the k − 1 bridges; the components R₁, …, R_k are subdivided
   K₃,₃'s in which the fort population is much richer (the bridge endpoints stop being
   poisoned). Fort certificate tables show **every 3-subset of a component misses an explicit
   fort**, so Z(R_i) = 4 for every i. A cut superadditivity lemma — each deleted edge can
   transmit at most one force — converts the per-block fort certificates into
   Z(G_k) ≥ 4k − (k − 1) = 3k + 1.
4. An explicit pattern W_k of size 3k + 1 forces (§6): Z(G_k) = 3k + 1 exactly.
5. Domination is settled by hand (§7): a two-lemma local analysis (each block holds ≥ 2
   dominators; three consecutive blocks hold ≥ 7) gives γ ≥ ⌊7k/3⌋, and an explicit periodic
   pattern D_k of size ⌊7k/3⌋ dominates.

Every finite claim below carries a machine check labelled **F1**–**F10**
(`validate_forts.py`); §9 summarizes what was machine-verified and §10 lists the honest gaps.

---

## 1. The family G_k

**Definition 1.1 (blocks).** For i = 1, …, k, block i consists of six *core* vertices
a₁ⁱ, a₂ⁱ, a₃ⁱ, b₁ⁱ, b₂ⁱ, b₃ⁱ and one or two *subdivision* vertices:

- **End blocks** (i = 1 and i = k): start from K₃,₃ with parts {a₁,a₂,a₃} | {b₁,b₂,b₃} and
  subdivide the edge a₁b₁ by a new vertex s. For block 1 we call its subdivision vertex
  s_out¹; for block k we call it s_in^k.
- **Middle blocks** (2 ≤ i ≤ k − 1): subdivide the two independent edges a₁b₁ and a₂b₂ by new
  vertices s_inⁱ (on a₁b₁) and s_outⁱ (on a₂b₂).

**Definition 1.2 (G_k).** G_k is the disjoint union of the k blocks plus the k − 1 **bridges**
s_outⁱ s_inⁱ⁺¹ (i = 1, …, k − 1). The *region* V_i of block i is its core plus its subdivision
vertices; |V_i| = 7 for end blocks, 8 for middle blocks, and n = 2·7 + (k−2)·8 = 8k − 2.

Explicitly, the adjacencies inside a middle block are

```
a1: b2, b3, s_in     a2: b1, b3, s_out     a3: b1, b2, b3
b1: a2, a3, s_in     b2: a1, a3, s_out     b3: a1, a2, a3
s_in: a1, b1 (+ bridge to s_out of block i−1)
s_out: a2, b2 (+ bridge to s_in of block i+1)
```

and inside an end block the same with the s_out (resp. s_in) column deleted and s = the single
subdivision vertex, adjacent to a1, b1 and its bridge partner. This generator is
**edge-for-edge identical** to the certified artifact files `chain_indep_k2.edges` …
`chain_indep_k8.edges` (**F1**), and G₂ is exactly G14 of `..\WRITEUP.md` §3.

**Lemma 1.3 (hypotheses).** For every k ≥ 2, G_k is connected, 3-regular, and triangle-free
(hence diamond-free both as "no diamond subgraph" and "no induced diamond"). It is not
bipartite.

*Proof.* Degrees: a core vertex keeps its three K₃,₃-neighbours, with each subdivided edge
replaced by the corresponding subdivision vertex; each subdivision vertex has degree 2 inside
its block plus exactly one bridge (block 1's s_out¹ bridges right, block k's s_in^k bridges
left, middle subdivision vertices bridge once each by Definition 1.2). Connectivity: each block
is connected, and the bridges link blocks 1, 2, …, k in a path. Triangle-freeness: each block
alone is a subdivision of the bipartite K₃,₃, hence bipartite, hence triangle-free; a triangle
through a bridge s_outⁱ s_inⁱ⁺¹ would require a common neighbour of the two endpoints, but
their remaining neighbourhoods lie in different blocks. Non-bipartiteness: a₁¹ s_out¹ b₁¹ a₃¹
b₂¹ a₁¹ is a 5-cycle (edges a₁s, s b₁, b₁a₃, a₃b₂, b₂a₁). ∎
(Machine check **F1**: k ≤ 20.)

---

## 2. Fort machinery

**Zero forcing.** Given B ⊆ V(G) ("blue"), the *colour change rule* lets a blue vertex u with
exactly one white neighbour v force v blue. The *closure* cl(B) is the result of applying the
rule until no force is possible. It is well defined (order-independent): if u can force v and
some other force is applied first, then u is still blue and its number of white neighbours can
only have decreased — either it is still exactly one (namely v) and the force remains
available, or v itself was just coloured, which is the same outcome; hence all maximal
application sequences reach the same fixed point. B is a *zero forcing set* (ZFS) if
cl(B) = V(G); Z(G) is the minimum size of a ZFS.
If cl(B) = V(G), there is a *chronological list of forces* u₁→v₁, …, u_m→v_m (m = |V| − |B|):
order the forced vertices by the closure rounds, breaking ties arbitrarily; at the time of the
force uₜ→vₜ, every neighbour of uₜ other than vₜ is already blue.

**Domination.** D ⊆ V dominates if N[D] = V; γ(G) = min |D|.

**Definition 2.1 (fort — Fast 2017 / Brimkov–Fast–Hicks 2019).** A *fort* of G is a nonempty F ⊆ V(G) such that
no vertex outside F has **exactly one** neighbour in F (every v ∉ F has 0 or ≥ 2 neighbours
in F).

**Lemma 2.2 (fort obstruction).** If B is a ZFS and F is a fort, then B ∩ F ≠ ∅.

*Proof.* Suppose B ∩ F = ∅. In a chronological list of forces, consider the first force u→v
with v ∈ F (it exists: F ≠ ∅ and F starts all white). The forcer u is not in F (no vertex of F
is blue yet). Since u is adjacent to v ∈ F and u ∉ F, the fort property gives u a second
neighbour w ∈ F, w ≠ v; w is still white, so u has two white neighbours and cannot force. ∎

**Lemma 2.3 (stalled complements are forts).** If cl(B) ≠ V then V ∖ cl(B) is a fort disjoint
from B.

*Proof.* Let F = V ∖ cl(B) ≠ ∅ and consider any vertex v **outside** F — that is,
v ∈ cl(B), blue at the fixed point. If v had exactly one neighbour in F, that neighbour would
be v's unique white neighbour, and v would force it — contradicting that cl(B) is stalled.
Hence every vertex outside F has 0 or ≥ 2 neighbours in F: F is a fort. B ⊆ cl(B), so
B ∩ F = ∅. ∎

**Theorem 2.4 (transversal characterization; Brimkov–Fast–Hicks).** B ⊆ V(G) is a zero forcing
set **iff** B intersects every fort of G. Consequently Z(G) equals the minimum size of a
transversal of the fort hypergraph, and for **any** family 𝓕 of forts,
Z(G) ≥ τ(𝓕) := min{|X| : X ∩ F ≠ ∅ for all F ∈ 𝓕}.

*Proof.* (⇒) Lemma 2.2. (⇐) If cl(B) ≠ V, Lemma 2.3 produces a fort disjoint from B. ∎

**Corollary 2.5 (disjoint forts).** If F₁, …, F_m are pairwise disjoint forts, Z(G) ≥ m. More
generally, if 𝓕 = 𝓕₁ ∪ … ∪ 𝓕_m where the *supports* ⋃𝓕_j are pairwise disjoint, then
τ(𝓕) = Σ_j τ(𝓕_j).

Machine check **F2** (in situ on G₂, n = 14): all C(14,6) = 3003 6-subsets stall and each
complement-of-closure is a fort disjoint from the start set (Lemma 2.3); all 504 forcing
7-subsets meet every one of the 2592 forts of G₂ (Lemma 2.2).

---

## 3. The fort landscape of G_k: what block-local forts can and cannot do

Throughout, "block-local fort" means a fort of G_k contained in a single region V_i.

**Lemma 3.1 (bridges poison subdivision vertices).** No fort of G_k contained in one region V_i
contains a subdivision vertex.

*Proof.* Every subdivision vertex s ∈ V_i is the endpoint of a bridge st with t ∉ V_i
(Definition 1.2 and Lemma 1.3's degree count). If s ∈ F ⊆ V_i, then t ∉ F, and t's other two
neighbours lie in t's own region ≠ V_i, so N(t) ∩ F = {s} — exactly one. Not a fort. ∎

**Lemma 3.2 (classification of block-local forts).** The inclusion-minimal block-local forts
of G_k are:

- in a **middle** block: exactly the three "index-pair" forts
  F₁₂ = {a₁,a₂,b₁,b₂}, F₁₃ = {a₁,a₃,b₁,b₃}, F₂₃ = {a₂,a₃,b₂,b₃};
- in an **end** block: exactly {a₂,a₃}, {b₂,b₃}, and the four forts
  {a₁,a_x,b₁,b_y} (x, y ∈ {2,3}).

*Proof.* By Lemma 3.1 a block-local fort lies in the 6-vertex core, so this is a finite check
over the 63 nonempty core subsets per block type, with the outside-vertices condition taken in
G_k (the subdivision vertices and, for the core, nothing else sees the core). Verification of
the listed sets is immediate; e.g. for F₂₃ in a middle block: a₁ has neighbours b₂,b₃ ∈ F₂₃
(two); b₁ has a₂,a₃ (two); s_in has none; s_out has a₂,b₂ (two). For minimality and
completeness see machine check **F4** (all 2^|V_i| subsets of each region of G₄ enumerated; the
local fort lists are exactly as stated, and none contains a subdivision vertex). ∎

The asymmetry has one cause: in an end block, s exists only on a₁b₁, so {a₂,a₃} survives (the
b's see two of it, a₁ sees none, s sees none); in a middle block, s_out sits on a₂b₂ and kills
{a₂,a₃}'s candidate analogues — every minimal local fort must shield both s_in and s_out.

**Proposition 3.3 (the per-block disjoint-fort bound, and its honest ceiling).**
The block-local forts of G_k give Z(G_k) ≥ 2k + 2, and **no better**: the family of all
block-local forts has transversal number exactly 2k + 2.

*Proof.* The local fort families of distinct blocks have disjoint supports (the regions), so by
Corollary 2.5, τ(all local forts) = Σᵢ τᵢ. **Middle block:** the three minimal forts pairwise
intersect but no vertex lies in all three (a₁ misses F₂₃, etc.), so τᵢ = 2; {a₁, a₂} works
(a₁ ∈ F₁₂ ∩ F₁₃, a₂ ∈ F₂₃). **End block:** {a₂,a₃} and {b₂,b₃} are disjoint, so τᵢ ≥ 2; a
2-transversal must take exactly one of a₂/a₃ and one of b₂/b₃ — say a_x', b_y' — and then the
fort {a₁, a_x, b₁, b_y} with x ≠ x', y ≠ y' is missed; so τᵢ ≥ 3, and {a₁, a₂, b₂} works
(it meets {a₂,a₃}, {b₂,b₃}, and every {a₁,·,b₁,·} through a₁). Total
τ = 2(k − 2) + 3 + 3 = 2k + 2. ∎
(Machine check **F4**: per-region transversal numbers 2 (mid) and 3 (end), with witnesses.)

So purely block-local fort counting is structurally capped at 2k + 2, which grows at rate
2 < 7/3 per block: it falls strictly below the domination number ⌊7k/3⌋ for every k ≥ 9 and
can therefore never prove unboundedness of Z − γ (it is also far below the true Z = 3k + 1). The deficit is the bridges': in
G_k itself every fort that touches a subdivision vertex is forced by Lemma 3.1's mechanism to
snake across bridges into neighbouring blocks, and a hand-checkable transversal bound for such
snaking families is unwieldy. The right move is to make the bridges *disappear*.

---

## 4. Per-block fort certificates: Z(R_end) = Z(R_mid) = 4

**Definition 4.1.** Let R_end and R_mid denote the two standalone block graphs — the
isomorphism types of the connected components of G_k minus its bridges:

- **R_end** (7 vertices, 10 edges): K₃,₃ with the edge a₁b₁ subdivided by s. Degrees: core 3,
  s has degree 2 (neighbours a₁, b₁).
- **R_mid** (8 vertices, 11 edges): K₃,₃ with a₁b₁ subdivided by s₁ and a₂b₂ subdivided by s₂.
  Degrees: core 3, s₁ (neighbours a₁, b₁) and s₂ (neighbours a₂, b₂) have degree 2.

For every k ≥ 2, deleting the k − 1 bridges of G_k leaves exactly the components
R₁ ≅ R_end, R₂ ≅ … ≅ R_{k−1} ≅ R_mid, R_k ≅ R_end (for k = 2: two copies of R_end).

With the bridges gone, Lemma 3.1's poisoning disappears and the fort population explodes:
R_end has 46 forts (10 minimal), R_mid has 73 forts (14 minimal) — machine census **F3**.
The inclusion-minimal forts (each is hand-checkable in seconds from Definition 2.1):

- **R_end (10):** {a₂,a₃}, {b₂,b₃}; {a₁,a₂,s}, {a₁,a₃,s}, {b₁,b₂,s}, {b₁,b₃,s};
  {a₁,a₂,b₁,b₂}, {a₁,a₂,b₁,b₃}, {a₁,a₃,b₁,b₂}, {a₁,a₃,b₁,b₃}.
- **R_mid (14):** {a₁,a₃,s₁}, {b₁,b₃,s₁}, {a₂,a₃,s₂}, {b₂,b₃,s₂};
  F₁₂ = {a₁,a₂,b₁,b₂}, F₁₃ = {a₁,a₃,b₁,b₃}, F₂₃ = {a₂,a₃,b₂,b₃};
  {a₂,a₃,b₂,s₁}, {a₂,b₂,b₃,s₁}, {a₁,a₃,b₁,s₂}, {a₁,b₁,b₃,s₂};
  {a₁,a₂,s₁,s₂}, {b₁,b₂,s₁,s₂}, {a₃,b₃,s₁,s₂}.

(Example verifications. {a₁,a₃,s₁} in R_mid: b₁ ∉ F sees a₃, s₁ — two; b₂ sees a₁, a₃ — two;
b₃ sees a₁, a₃ — two; a₂, s₂ see none. {a₃,b₃,s₁,s₂} in R_mid: a₁ sees b₃, s₁ — two; a₂ sees
b₃, s₂ — two; b₁ sees a₃, s₁ — two; b₂ sees a₃, s₂ — two.)

**Theorem 4.2 (per-block values).** Z(R_end) = Z(R_mid) = 4.

*Proof.* **Upper bounds.** cl({a₁,a₂,b₁,b₂}) = V(R_end): a₂ (neighbours b₁, b₂ blue, b₃ white)
forces b₃; b₂ (neighbours a₁, a₂ blue, a₃ white) forces a₃; a₁ (neighbours b₂, b₃ blue, s
white) forces s. cl({a₁,a₂,b₁,b₃}) = V(R_mid): b₃ (neighbours a₁, a₂ blue, a₃ white) forces
a₃; b₁ (neighbours a₂, a₃ blue, s₁ white) forces s₁; a₃ (neighbours b₁, b₃ blue, b₂ white)
forces b₂; a₂ (neighbours b₁, b₃ blue, s₂ white) forces s₂. All blue.
(Machine check **F3** verifies both closures.)

**Lower bounds (fort certificates).** By Theorem 2.4 it suffices to show every 3-subset misses
some fort. The tables below list, for each orbit of 3-subsets under Aut, an explicit
inclusion-minimal fort disjoint from the representative. This suffices: automorphisms map
forts to forts and preserve disjointness, so if the representative B misses fort F, the orbit
member π(B) misses the fort π(F). The automorphism groups are

- Aut(R_end) = ⟨ρ, σ, τ⟩ of order 8, with ρ = (a₁b₁)(a₂b₂)(a₃b₃) (swap the two sides, fix s),
  σ = (a₂a₃), τ = (b₂b₃);
- Aut(R_mid) = ⟨ρ, π⟩ of order 4, with ρ = (a₁b₁)(a₂b₂)(a₃b₃) (fixing s₁, s₂) and
  π = (a₁a₂)(b₁b₂)(s₁s₂) (swap the two subdivided pairs).

(Each generator is checked to preserve the edge lists in one line; the group **orders** and the
completeness of the orbit tables are machine facts, **F3** — and `validate_forts.py` also
checks all C(7,3) = 35 and C(8,3) = 56 3-subsets directly, with no symmetry reduction, so the
tables' bookkeeping is not load-bearing.)

**R_end — every 3-subset misses a fort** (35 = 2+4+2+8+4+4+2+1+4+4 sets in 10 orbits):

| orbit representative B | orbit size | disjoint minimal fort |
|---|---|---|
| {a₁,a₂,a₃} | 2 | {b₂,b₃} |
| {a₁,a₂,b₁} | 4 | {b₂,b₃} |
| {a₂,a₃,b₁} | 2 | {b₂,b₃} |
| {a₁,a₂,b₂} | 8 | {b₁,b₃,s} |
| {a₂,a₃,b₂} | 4 | {b₁,b₃,s} |
| {a₁,a₂,s} | 4 | {b₂,b₃} |
| {a₂,a₃,s} | 2 | {b₂,b₃} |
| {a₁,b₁,s} | 1 | {a₂,a₃} |
| {a₂,b₁,s} | 4 | {b₂,b₃} |
| {a₂,b₂,s} | 4 | {a₁,a₃,b₁,b₃} |

**R_mid — every 3-subset misses a fort** (56 sets in 17 orbits):

| orbit representative B | orbit size | disjoint minimal fort |
|---|---|---|
| {a₁,a₂,a₃} | 2 | {b₁,b₃,s₁} |
| {a₁,a₂,b₁} | 4 | {b₂,b₃,s₂} |
| {a₁,a₃,b₁} | 4 | {b₂,b₃,s₂} |
| {a₂,a₃,b₁} | 4 | {b₂,b₃,s₂} |
| {a₃,b₁,b₂} | 2 | {a₁,a₂,s₁,s₂} |
| {a₁,a₃,b₃} | 4 | {b₁,b₂,s₁,s₂} |
| {a₁,a₂,s₁} | 4 | {b₂,b₃,s₂} |
| {a₁,a₃,s₁} | 4 | {b₂,b₃,s₂} |
| {a₂,a₃,s₁} | 4 | {b₂,b₃,s₂} |
| {a₁,b₁,s₁} | 2 | {a₂,a₃,s₂} |
| {a₂,b₁,s₁} | 4 | {b₂,b₃,s₂} |
| {a₃,b₁,s₁} | 4 | {b₂,b₃,s₂} |
| {a₂,b₂,s₁} | 2 | {a₁,a₃,b₁,b₃} |
| {a₃,b₂,s₁} | 4 | {a₁,b₁,b₃,s₂} |
| {a₃,b₃,s₁} | 2 | {a₁,a₂,b₁,b₂} |
| {a₁,s₁,s₂} | 4 | {a₂,a₃,b₂,b₃} |
| {a₃,s₁,s₂} | 2 | {a₁,a₂,b₁,b₂} |

Every 3-subset of either graph therefore misses a fort, so no 3-subset forces (Theorem 2.4)
and Z ≥ 4 in both. ∎

Remark (sharpness of the certificate). The minimal-fort hypergraph is *exactly* what is
needed: in R_end no proper subfamily of the 10 minimal forts covers all 35 3-subsets, and in
R_mid 13 of the 14 minimal forts are needed (**F3**). The per-block bound Z(R) ≥ 4 is thus a
genuinely global fort phenomenon of the block, not the consequence of a couple of lucky forts.

---

## 5. The bridge-cut superadditivity lemma

**Lemma 5.1 (one force per cut edge).** Fix a graph G, a set B with cl(B) = V(G), and a
chronological list of forces. For every edge e = uv of G, at most one force is performed along
e (in either direction combined).

*Proof.* A force along e colours one endpoint and requires both that the forcer be blue and
the target be white. After the first force along e both endpoints are blue and remain blue; a
second force along e would need a white target. ∎

**Theorem 5.2 (cut superadditivity).** Let G be a graph, E′ ⊆ E(G), and let H₁, …, H_m be the
connected components of G − E′ (the graph (V, E ∖ E′)), with vertex sets V₁, …, V_m. Then

Z(G) ≥ Σ_{j=1}^m Z(H_j) − |E′|.

*Proof.* Let B be a minimum ZFS of G and fix a chronological list u₁→v₁, …, u_r→v_r. Call a
force *crossing* if its edge uₜvₜ lies in E′, and let X = {vₜ : uₜ→vₜ crossing} be the set of
crossing-forced vertices; |X| ≤ |E′| by Lemma 5.1.

*Claim:* for each component j, the set B_j := (B ∪ X) ∩ V_j satisfies cl_{H_j}(B_j) = V_j.

By strong induction on t we show every vₜ ∈ V_j lies in cl_{H_j}(B_j). If uₜ→vₜ is crossing,
vₜ ∈ X ∩ V_j ⊆ B_j. Otherwise uₜvₜ ∈ E ∖ E′, so uₜ ∈ V_j (components of G − E′). At the time
of the force, every G-neighbour of uₜ other than vₜ is blue, i.e. lies in B ∪ {v₁, …, vₜ₋₁};
hence every H_j-neighbour of uₜ other than vₜ lies in (B ∩ V_j) ∪ {v_s ∈ V_j : s < t}, which
is contained in cl_{H_j}(B_j) by the induction hypothesis (and B ∩ V_j ⊆ B_j directly).
Likewise uₜ itself is in B ∩ V_j or equals some v_s (s < t), so uₜ ∈ cl_{H_j}(B_j). Inside the
closure cl_{H_j}(B_j), the vertex uₜ is blue and all its H_j-neighbours except possibly vₜ are
blue; if vₜ were white it would be forced. Either way vₜ ∈ cl_{H_j}(B_j), proving the claim
(every vertex of V_j is in B or forced at some time t).

Therefore Z(H_j) ≤ |B_j| ≤ |B ∩ V_j| + |X ∩ V_j|, and summing over j (the V_j partition V):

Σ_j Z(H_j) ≤ |B| + |X| ≤ Z(G) + |E′|. ∎

**Corollary 5.3 (the per-block fort bound, bridged).** For every k ≥ 2,
Z(G_k) ≥ 4k − (k − 1) = **3k + 1**.

*Proof.* Apply Theorem 5.2 with E′ = the k − 1 bridges. The components are two copies of R_end
and k − 2 copies of R_mid (Definition 4.1), each with Z = 4 by the fort certificates of
Theorem 4.2: Z(G_k) ≥ 4k − (k − 1). ∎

Machine check **F5** validates the proof mechanics in situ: for **all** 504 forcing 7-sets and
all 1065 forcing 8-sets of G₂ (and 300 random forcing sets each for k = 3, 4), random
chronological orders were generated; in every run every bridge transmitted at most one force,
the replayed sets (B ∪ X) ∩ V_j forced their components, and the per-block accounting
|B ∩ V_j| ≥ 4 − |X ∩ V_j| held, summing to ≥ 3k + 1.

The division of labour in Corollary 5.3 is exactly the one promised in §0: **forts deliver the
per-block constant 4** (Theorem 4.2 — per-block fort certificates with pairwise disjoint
supports across blocks), and **the cut lemma pays one unit per bridge** to glue the blocks
back together: (4)·k − 1·(k − 1). Note the contrast with Proposition 3.3: staying inside G_k,
block-local forts can only certify 2k + 2; converting each block into its bridge-free
standalone graph raises the per-block fort yield from 2 to 4 at a price of k − 1 total.

---

## 6. The matching upper bound: Z(G_k) = 3k + 1

**Theorem 6.1.** For every k ≥ 2, the set

W_k = {a₁¹, a₂¹, b₁¹, b₂¹} ∪ ⋃_{i=2}^{k} {a₁ⁱ, a₂ⁱ, b₂ⁱ}   (|W_k| = 4 + 3(k−1) = 3k + 1)

is a zero forcing set of G_k. Hence, with Corollary 5.3, **Z(G_k) = 3k + 1**.

*Proof.* We force the blocks left to right. Invariant I(i): before stage i begins, every
vertex of regions V₁, …, V_{i−1} is blue, and s_inⁱ is blue (for i ≥ 2).

*Stage 1.* Blue: a₁¹, a₂¹, b₁¹, b₂¹. Then a₂¹ (neighbours b₁¹, b₂¹, b₃¹; the first two blue)
forces b₃¹; b₂¹ (neighbours a₁¹, a₂¹, a₃¹) forces a₃¹; a₁¹ (neighbours b₂¹, b₃¹, s_out¹)
forces s_out¹; s_out¹ (neighbours a₁¹, b₁¹, s_in²) forces s_in². This colours all of V₁ and
establishes I(2).

*Stage i, 2 ≤ i ≤ k − 1 (middle block).* Blue so far in V_i: a₁ⁱ, a₂ⁱ, b₂ⁱ (from W_k) and
s_inⁱ (invariant). Then a₁ⁱ (neighbours b₂ⁱ, b₃ⁱ, s_inⁱ; b₂ⁱ and s_inⁱ blue) forces b₃ⁱ;
s_inⁱ (neighbours a₁ⁱ, b₁ⁱ, s_outⁱ⁻¹; a₁ⁱ blue and s_outⁱ⁻¹ blue by I(i)) forces b₁ⁱ; b₁ⁱ
(neighbours a₂ⁱ, a₃ⁱ, s_inⁱ) forces a₃ⁱ; a₂ⁱ (neighbours b₁ⁱ, b₃ⁱ, s_outⁱ) forces s_outⁱ;
s_outⁱ (neighbours a₂ⁱ, b₂ⁱ, s_inⁱ⁺¹) forces s_inⁱ⁺¹. All of V_i is blue and I(i+1) holds.

*Stage k (end block).* Blue: a₁ᵏ, a₂ᵏ, b₂ᵏ and s_inᵏ. Then a₁ᵏ (neighbours b₂ᵏ, b₃ᵏ, s_inᵏ)
forces b₃ᵏ; s_inᵏ (neighbours a₁ᵏ, b₁ᵏ, s_outᵏ⁻¹; s_outᵏ⁻¹ blue by I(k)) forces b₁ᵏ; b₂ᵏ
(neighbours a₁ᵏ, a₂ᵏ, a₃ᵏ) forces a₃ᵏ. All of V_k is blue, completing cl(W_k) = V(G_k). ∎

Machine check **F6**: cl(W_k) = V(G_k) and |W_k| = 3k + 1 for every k ≤ 20 and k = 30, 40;
moreover W₂ = {0,1,3,4,7,8,11} is **identical** to the certified Z-witness of G14
(`..\certificate_g14.json`), and the values 3k + 1 reproduce the certified Z = 7, 10, 13, 16
at k = 2, 3, 4, 5 (**F10**), the latter re-anchored this run by the independent Rust verifier
(`rust_check … zf 9` → NONE on k = 3, `zf 12` → NONE on k = 4).

---

## 7. Domination: γ(G_k) = ⌊7k/3⌋

Write C_i = {a₁ⁱ, a₂ⁱ, a₃ⁱ, b₁ⁱ, b₂ⁱ, b₃ⁱ} for the core of block i, and for a dominating set
D let c_i = |D ∩ V_i|.

### 7.1 Lower bound

**Lemma 7.1 (core isolation).** For every core vertex v ∈ C_i, N[v] ⊆ V_i. Hence C_i can only
be dominated from inside V_i. (Immediate from Definition 1.2: only subdivision vertices have
neighbours outside their region. Machine check **F8**, k ≤ 8.)

**Lemma 7.2 (c_i ≥ 2).** Every closed neighbourhood meets C_i in at most 4 vertices, so
c_i ≥ ⌈6/4⌉ = 2 for every block of every dominating set.

*Proof.* G_k is cubic, so |N[v]| = 4 for every v, whence |N[v] ∩ C_i| ≤ 4 < 6 = |C_i|; and
vertices outside V_i contribute 0 (Lemma 7.1). So one vertex cannot dominate C_i. ∎ (**F8**:
the maximum of |N[v] ∩ C_i| is indeed 4.)

**Lemma 7.3 (pair classification).** Suppose c_i = 2, say D ∩ V_i = {x, y}. Then {x, y}
dominates C_i (Lemma 7.1), and:

- **middle block:** {x,y} ∈ { {a₁,b₁}, {a₂,b₂}, {a₃,b₃} } (the three "diagonal" pairs);
- **end block:** {x,y} ∈ { {a₁,b₁}, {a₂,b₂}, {a₂,b₃}, {a₃,b₂}, {a₃,b₃} }.

In particular **no subdivision vertex belongs to a 2-vertex block of a dominating set**, and
in a middle block with D ∩ V_i = {a₃,b₃} neither subdivision vertex of block i is dominated
from inside block i's pair.

*Proof (middle block; coverage numbers |N[v] ∩ C| from the table in Definition 1.2).*
Coverage 4: a₃ ({a₃,b₁,b₂,b₃}), b₃ ({b₃,a₁,a₂,a₃}); coverage 3: a₁ ({a₁,b₂,b₃}),
a₂ ({a₂,b₁,b₃}), b₁ ({b₁,a₂,a₃}), b₂ ({b₂,a₁,a₃}); coverage 2: s₁ ({a₁,b₁}), s₂ ({a₂,b₂}).
Two closed neighbourhoods cover the 6 core vertices only if their coverages sum to ≥ 6 with
union all of C. 4+4: {a₃,b₃} ✓ (union is C). 4+2: a₃ misses {a₁,a₂}; no s covers both a₁ and
a₂; b₃ misses {b₁,b₂}; same. 4+3: a₃ misses {a₁,a₂} and the only vertex whose closed
neighbourhood contains both a₁ and a₂ is b₃ (a₁ ∈ N[x] ⇔ x ∈ {a₁,b₂,b₃,s₁};
a₂ ∈ N[x] ⇔ x ∈ {a₂,b₁,b₃,s₂}; intersection {b₃}) — giving {a₃,b₃} again; symmetrically for
b₃. 3+3: the union must be a disjoint cover; checking the four coverage-3 sets pairwise,
{a₁,b₂,b₃} ⊔ {b₁,a₂,a₃} (pair {a₁,b₁}) and {a₂,b₁,b₃} ⊔ {b₂,a₁,a₃} (pair {a₂,b₂}) are the
only disjoint complementary pairs (directly: a₁&a₂ share b₃; a₁&b₂ share a₁ and b₂; a₂&b₁
share a₂ and b₁; b₁&b₂ share a₃). Lower sums (3+2, 2+2 < 6) cannot cover.
*(End block: same style; coverages a₁:{a₁,b₂,b₃}, a₂:{a₂,b₁,b₂,b₃}, a₃:{a₃,b₁,b₂,b₃},
b₁:{b₁,a₂,a₃}, b₂:{b₂,a₁,a₂,a₃}, b₃:{b₃,a₁,a₂,a₃}, s:{a₁,b₁}. The 4+4 pairs {a₂,b₂},
{a₂,b₃}, {a₃,b₂}, {a₃,b₃} work; {a₂,a₃} misses a₁, {b₂,b₃} misses b₁; 3+3 gives {a₁,b₁};
4+3 and pairs with s all leave a hole — e.g. s covers only {a₁,b₁} and no vertex covers
{a₂,a₃,b₂,b₃}.)* Machine check **F8** confirms both lists exactly. The last sentence: by the
classification no pair contains s₁/s₂/s; and N[{a₃,b₃}] ∩ {s₁,s₂} = ∅ since s₁ ~ a₁,b₁ and
s₂ ~ a₂,b₂ only. ∎

**Lemma 7.4 (window lemma).** For every dominating set D of G_k (k ≥ 3) and every
1 ≤ i ≤ k − 2: c_i + c_{i+1} + c_{i+2} ≥ 7.

*Proof.* Suppose c_i = c_{i+1} = c_{i+2} = 2. By Lemma 7.3, each of D ∩ V_i, D ∩ V_{i+1},
D ∩ V_{i+2} is one of the listed core pairs; in particular none contains a subdivision vertex.
Block i+1 is a middle block (2 ≤ i+1 ≤ k−1). Consider s_inⁱ⁺¹: its closed neighbourhood is
{s_inⁱ⁺¹, a₁ⁱ⁺¹, b₁ⁱ⁺¹, s_outⁱ}. D must meet it; s_inⁱ⁺¹ ∉ D and s_outⁱ ∉ D (pairs are
s-free), so a₁ⁱ⁺¹ ∈ D or b₁ⁱ⁺¹ ∈ D, forcing D ∩ V_{i+1} = {a₁,b₁} (the only listed middle
pair meeting {a₁,b₁}). Symmetrically, s_outⁱ⁺¹ has closed neighbourhood
{s_outⁱ⁺¹, a₂ⁱ⁺¹, b₂ⁱ⁺¹, s_inⁱ⁺²}, and s_outⁱ⁺¹ ∉ D, s_inⁱ⁺² ∉ D force
D ∩ V_{i+1} = {a₂,b₂}. Contradiction. ∎

**Theorem 7.5 (lower bound).** γ(G_k) ≥ 7⌊k/3⌋ + 2(k mod 3) = ⌊7k/3⌋ for every k ≥ 2.

*Proof.* Let D dominate G_k and write k = 3q + r, r ∈ {0,1,2}. Partition blocks 1, …, 3q into
q disjoint consecutive triples; each triple contributes ≥ 7 (Lemma 7.4) and each of the r
leftover blocks contributes ≥ 2 (Lemma 7.2):
|D| ≥ 7q + 2r = (7k − 7r + 6r)/3 = (7k − r)/3 = ⌊7k/3⌋ (since 7k ≡ r mod 3). For k = 2 only
Lemma 7.2 is needed: γ ≥ 4 = ⌊14/3⌋. ∎

### 7.2 Upper bound: an explicit periodic dominating pattern

**Definition 7.6 (motifs).** Per block, take D ∩ V_i as follows (names match the machine
checker):

| motif | block type | D ∩ V_i | dominates inside V_i | needs | provides |
|---|---|---|---|---|---|
| **E** | end | {a₁, b₁} | all of V_i (N[a₁] ∪ N[b₁] ⊇ C_i ∪ {s}) | — | — |
| **A** = P_A | middle | {a₁, b₁} | all but s_out | s_inⁱ⁺¹ ∈ D | — |
| **B** = P_B | middle | {a₂, b₂} | all but s_in | s_outⁱ⁻¹ ∈ D | — |
| **T** | middle | {s_in, s_out, a₃} | all of V_i | — | both sides |
| **W** | middle | {s_in, a₂, b₂} | all of V_i | — | left side |
| **P** = E′ | end (block k) | {s_in, a₂, b₂} | all of V_i | — | left side |

("Provides left" means s_in ∈ D dominates the previous block's s_out across the bridge;
"provides right" means s_out ∈ D dominates the next block's s_in. The "dominates inside"
claims are one-line closed-neighbourhood computations from Definition 1.2; e.g. **T**:
N[a₃] ⊇ {a₃,b₁,b₂,b₃}, N[s_in] ⊇ {a₁,b₁}, N[s_out] ⊇ {a₂,b₂} — union V_i.)

**Theorem 7.7 (upper bound).** For every k ≥ 2, γ(G_k) ≤ ⌊7k/3⌋, achieved by the patterns
(k = 3q + r):

- r = 2: **E** [**A T B**]^q **E**  (size 2 + 7q + 2 = ⌊7k/3⌋);
- r = 0: **E** [**A T B**]^{q−1} **A P**  (size 2 + 7(q−1) + 2 + 3 = 7q);
- r = 1, k ≥ 4: **E** [**A T B**]^{q−1} **A W E**  (size 2 + 7(q−1) + 2 + 3 + 2 = 7q + 2).

*Proof.* Each motif dominates its own region except as listed in "needs", and the junctions
discharge every need: every **A** is immediately followed by **T**, **W**, or **P** — all of
which have s_in ∈ D, dominating A's s_out across the bridge; every **B** is immediately
preceded by **T**, whose s_out ∈ D dominates B's s_in; **E**, **T**, **W**, **P** are
self-sufficient. (Spot-check the boundary cases: in pattern r = 2 with q = 0 the chain is
**E E** — both end blocks self-sufficient, k = 2, size 4; in r = 0 with q = 1 the chain is
**E A P**, k = 3, size 7.) Sizes as displayed; ⌊7k/3⌋ = 7q + ⌊7r/3⌋ = 7q, 7q+2, 7q+4 for
r = 0, 1, 2. ∎

Machine check **F7**: D_k dominates with |D_k| = ⌊7k/3⌋ for all k ≤ 20 and k = 30, 40; and
D₂ = {0, 3, 7, 10} is identical to the certified γ-witness of G14. The values reproduce the
certified γ = 4, 7, 9, 11, 14, 16, 18 (k = 2…8, **F10**), re-anchored this run by
`rust_check … gamma 6` → NONE (k = 3) and `gamma 8` → NONE (k = 4). An independent
three-state interface dynamic program (different code path, **F9**) confirms
γ(G_k) = ⌊7k/3⌋ for **all 2 ≤ k ≤ 60**.

**Theorem 7.8.** γ(G_k) = ⌊7k/3⌋ for every k ≥ 2. ∎ (Theorems 7.5 + 7.7.)

---

## 8. Assembly: the main theorem and its consequences

**Theorem A.** For every k ≥ 2, γ(G_k) = ⌊7k/3⌋ (Theorem 7.8) and Z(G_k) = 3k + 1
(Corollary 5.3 + Theorem 6.1). ∎

**Theorem B.** Z(G_k) − γ(G_k) = 3k + 1 − ⌊7k/3⌋. Writing k = 3q + r:
the gap equals 2q + 1 + r, i.e. ⌈2k/3⌉ + 1 = ⌈(2k+3)/3⌉, which is **unbounded**. With
n = 8k − 2 (so k = (n+2)/8): gap = ⌈(n+14)/12⌉ > n/12. ∎

**Corollary C.** On the class of connected cubic triangle-free graphs — all of which are
diamond-free under both the "no diamond subgraph" and the "no induced diamond" reading, since
every diamond contains a triangle — the difference Z − γ is unbounded. In particular, for
every constant c there is a connected cubic diamond-free graph with Z > γ + c: **no additive
correction rescues Conjecture 9** of arXiv:2406.19231 (which proposed c = 2 and which G₂ = G14
already refuted). ∎

**Remarks.**

1. **New exact values.** Theorem A settles Z(G₆) = 19, Z(G₇) = 22, Z(G₈) = 25 (previously
   only certified as upper bounds; the lower-bound search at k = 6 was estimated at ~7 h of
   compute and never run — the theorem replaces it).
2. **Not bipartite.** G_k contains 5-cycles (Lemma 1.3), so Corollary C does *not* cover the
   bipartite cubic class; whether Z − γ is unbounded on connected bipartite cubic graphs
   remains open here. (The natural fix — double subdivision to preserve bipartiteness —
   changes both block constants and was not analysed.)
3. **Growth-rate context.** Z/γ → 9/7 on this family, consistent with the known regime
   Z ≤ 2γ for cubic graphs mentioned in `..\WRITEUP.md` §8; the family pushes the *additive*
   gap, not the ratio. We make no claim that n/12 is extremal for the class.
4. **The fort ledger.** Within G_k, block-local forts certify Z ≥ 2k + 2 and no more
   (Proposition 3.3); the full fort hypergraph of G_k certifies Z exactly (Theorem 2.4), but
   the forts that do the extra work snake across bridges. The bridge-cut lemma (§5) is the
   bookkeeping device that lets the per-block fort certificates (Theorem 4.2) act at full
   strength 4 per block, at a cost of exactly one unit per bridge. For k ≤ 5 the resulting
   3k + 1 matches the exhaustively certified Z at every point.

---

## 9. Computational validation (all finite claims machine-checked)

`theorem/validate_forts.py` (pure stdlib Python, exact bitmask arithmetic, fresh code —
independent of the discovery scripts, of `..\checker_conj9.py`, of `..\rust_check`, and of the
sibling validators) checks, with **ALL CHECKS PASSED** on 2026-06-12:

| check | claim validated | section |
|---|---|---|
| F1 | generator == certified `chain_indep_k2..8.edges`, edge-for-edge; cubic/connected/triangle-free, n = 8k−2, k ≤ 20 | §1 |
| F2 | Lemmas 2.2/2.3 in situ on G₂: 3003 6-sets all stall with fort complements; 504 forcing 7-sets hit all 2592 forts | §2 |
| F3 | Z(R_end) = Z(R_mid) = 4 (exhaustive over all 3- and 4-sets); full fort census (46/73), minimal forts (10/14); every 3-subset misses a minimal fort; orbit tables (|Aut| = 8/4) emitted to `fort_tables.md` and re-checked without symmetry; certificate minimality | §4 |
| F4 | block cores and F₁₂/F₁₃/F₂₃ are forts of G_k (k ≤ 6); region-contained forts of G₄ avoid subdivision vertices; minimal local fort lists; local transversal numbers 2 (mid) / 3 (end) | §3 |
| F5 | cut lemma mechanics in situ: ALL forcing 7-/8-sets of G₂ (504/1065) × random chronological orders, plus 300 random forcing sets each at k = 3, 4: ≤ 1 force per bridge, replay forces each component, per-block accounting ≥ 3k+1 | §5 |
| F6 | W_k forces with |W_k| = 3k+1, k ≤ 20 and 30, 40; W₂ == certified G14 Z-witness | §6 |
| F7 | D_k dominates with |D_k| = ⌊7k/3⌋, k ≤ 20 and 30, 40; D₂ == certified G14 γ-witness | §7.2 |
| F8 | γ-lower-bound block lemmas: max core coverage 4; pair classifications exact (mid: 3 diagonal pairs; end: 5 pairs; none with subdivision vertices); core isolation k ≤ 8 | §7.1 |
| F9 | independent 3-state interface DP: γ(G_k) = ⌊7k/3⌋ for all k ≤ 60; reproduces certified γ at k = 2…8 | §7 |
| F10 | formulas vs the certified table (γ at k ≤ 8, Z at k ≤ 5, gap values) | §0 |

External re-anchors run this session: `..\rust_check\target\release\rust_check.exe` on
`chain_indep_k3.edges` (`gamma 6` → NONE, `zf 9` → NONE) and `chain_indep_k4.edges`
(`gamma 8` → NONE, `zf 12` → NONE) — the certified exhaustive lower bounds γ(G₃) ≥ 7,
Z(G₃) ≥ 10, γ(G₄) ≥ 9, Z(G₄) ≥ 13 reproduce. Prior certification stack inherited from
`..\WRITEUP.md`: exhaustive Python + Rust + hostile Codex recomputation for k ≤ 5.
Independent same-theorem validations: `theorem/validate_theorem.py` (wavefront lens, ALL
CHECKS PASSED) and `theorem/validate_gamma_exact.py` (DP lens, 29/29) — different code paths,
same formulas, same graphs.

**Hostile Codex foil (GPT-5.5, full shell access, 2026-06-12, threadId
019eba8a-623a-77e1-8d7c-231373f4442a).** A hostile referee pass over this finished document,
with instructions to break it. Codex wrote its own independent checker
(`theorem/hostile_referee_fresh_check.py`, fresh graph/forcing/fort/domination code, reading
only the `.edges` anchors) and reported: Z(R_end) = Z(R_mid) = 4 reconfirmed with fort counts
46/73 and minimal counts 10/14; **every** fort-table row re-verified (fort property,
disjointness, minimality, orbit sums 35/56); attempted refutation of Theorem 5.2 by exhaustive
search over **all** labelled graphs and all edge-deletion sets through n ≤ 6 (14,408,717
ternary edge states) plus 4000 random n = 7, 8 trials — no counterexample; Lemmas 2.2/2.3 and
Theorem 2.4 checked on all graphs through n ≤ 5 including degenerate cases; the exact stated
force order of Theorem 6.1 simulated legally for k = 2…6; Lemma 7.3 classifications exact; no
dominating set with three consecutive 2-blocks exists for k = 3…6 "even giving all outside
blocks for free"; Theorem 7.7 patterns verified k = 2…12; all arithmetic identities and the
§0 table verified against `..\WRITEUP.md`. Verdict verbatim: *"ACCEPT WITH MINOR FIXES. I
tried to kill it and failed."* The single required fix (a wording ambiguity in the proof of
Lemma 2.3) is applied in this version.

Reproduce:

```
cd problems\p2-factory\kills\davila-conj9\theorem
python validate_forts.py     # ~2 minutes; must end with ALL CHECKS PASSED
```

---

## 10. Honest gap list

1. **Finite machine-checked case analyses.** Three ingredients are finite computations rather
   than prose: (a) the fort census / minimality / completeness of the orbit tables in §4
   (every individual table row *is* hand-checkable in under a minute, and the no-symmetry
   exhaustive re-check removes the orbit bookkeeping from the trusted base, but a referee who
   wants zero computer trust must verify 35 + 56 closures by hand); (b) the automorphism group
   orders 8 and 4 (generators are exhibited and easily verified; that there are no *further*
   automorphisms is machine-checked — though it is also not load-bearing, by the same
   no-symmetry re-check); (c) the classification of block-local forts in Lemma 3.2 (used only
   for the non-load-bearing Proposition 3.3). Everything else — the cut lemma, the forcing
   schedule, the domination lemmas — is hand-proved in full, with the machine checks serving
   as validation rather than evidence.
2. **The cut lemma is a process argument, not a fort argument.** Theorem 2.4 guarantees that a
   pure fort certificate for Z(G_k) ≥ 3k + 1 exists (the fort-cover ILP found one for each
   k ≤ 5), but we did not extract a hand-checkable *global* fort family with transversal
   number 3k + 1; the bridge-cut replay (Theorem 5.2) stands in for it. A purely fort-static
   proof would need to organise the bridge-snaking forts of §3 into a transfer structure —
   doable in principle, not done here.
3. **Pattern-validation range.** W_k and D_k are *proved* to force/dominate for all k (§6, §7.7
   — finite local computations plus induction along the chain), and additionally
   machine-verified for k ≤ 20 ∪ {30, 40}; the proofs do not depend on the verification range.
   The independent DP cross-check of γ runs to k = 60. No claim in the paper has an
   unverified finite component beyond those listed in item 1.
4. **Bipartite case open.** See Remark 2 of §8 — the family is triangle-free but not
   bipartite; "triangle-free" is the strongest class qualifier proved.
5. **Rate optimality not claimed.** Z − γ = ⌈(n+14)/12⌉ on this family; whether other cubic
   triangle-free families grow faster, or what the extremal density is, is untouched.
6. **Definitional fidelity.** "Zero forcing" is the standard colour-change rule of the source
   conjecture (quoted verbatim in `..\WRITEUP.md` §1); domination is standard; nothing here
   addresses PSD/fractional/probabilistic forcing variants. The diamond-free ambiguity
   (subgraph vs induced) is moot for our graphs by triangle-freeness.
7. **Novelty of the general lemmas.** Lemma 2.2/2.3/Theorem 2.4 are known (Fast 2017;
   Brimkov–Fast–Hicks, *Computational approaches for zero forcing and related problems*,
   EJOR 2019); Theorem 5.2 is folklore-adjacent (edge-deletion superadditivity appears in
   various forms in the minimum-rank/zero-forcing literature, e.g. edge spread results
   Z(G) − 1 ≤ Z(G − e) ≤ Z(G) + 1, of which it is an easy consequence by induction on |E′|,
   but we prove it from scratch); no novelty is claimed for them, only for the application.

---

## References

- R. Davila, *Another conjecture of TxGraffiti concerning zero forcing and domination in
  graphs*, arXiv:2406.19231 (v2, Nov 2024). Conjecture 9 is the refuted target;
  `..\source_2406.19231v2.html` is the archived source.
- C. Fast, *Novel techniques for the zero forcing and k-forcing numbers of a graph*,
  PhD thesis, Rice University, 2017 — origin of forts.
- B. Brimkov, C. Fast, I. V. Hicks, *Computational approaches for zero forcing and related
  problems*, European J. Oper. Res. 273 (2019) — fort covers / transversal IP formulation.
- AIM Special Work Group, *Zero forcing sets and the minimum rank of graphs*, Linear Algebra
  Appl. 428 (2008) — zero forcing number; edge spread literature for context to Theorem 5.2.
- `..\WRITEUP.md`, `..\VERIFICATION_LOG.md`, `..\certificate_chain_family.json` — the
  certified exact anchors k ≤ 5 (Z) and k ≤ 8 (γ).
