# Z − γ is unbounded on connected cubic triangle-free graphs

## A bridge-transfer proof for the Davila Conjecture 9 chain family

**Path:** `problems/p2-factory/kills/davila-conj9/theorem/induction-transfer.md`
**Date:** 2026-06-12 · **Companion artifacts:** `validate_induction.py` (all finite
facts and all constructions machine-validated; exit 0), `ilp_crosscheck.py` and
`z_chrono_check.py` (optional CP-SAT consistency checks), `b1.edges`, `b2.edges`
(piece graphs for the Rust dual check), and the parent directory's `WRITEUP.md`,
`chain_indep_k*.edges`, `rust_check/` (the verified refutation this theorem
upgrades).

---

## 0. Main results

Throughout, Z(G) is the zero forcing number and γ(G) the domination number,
with the definitions of arXiv:2406.19231v2 §1.1 (restated in §2 below).
G_k (k ≥ 2) is the chain graph of Definition 1.1: k blocks, each a copy of
K₃,₃ with one (end blocks) or two (middle blocks) subdivided edges, consecutive
subdivision vertices joined by bridges; G_2 is the 14-vertex counterexample G14
of the parent WRITEUP.

> **Theorem A.** For every integer k ≥ 2, G_k is a connected, cubic,
> triangle-free graph on n = 8k − 2 vertices (hence diamond-free under both the
> subgraph and the induced-subgraph readings), and
>
> γ(G_k) = ⌊7k/3⌋  and  Z(G_k) = 3k + 1.
>
> Consequently
>
> Z(G_k) − γ(G_k) = 3k + 1 − ⌊7k/3⌋ = ⌈(2k + 3)/3⌉ ≥ (2k + 3)/3 → ∞.

> **Corollary B.** Z − γ is unbounded on the class of connected cubic
> triangle-free (a fortiori diamond-free) graphs. In particular, for every
> constant c there is a graph in this class with Z(G) > γ(G) + c (take
> k ≥ 3c/2, i.e. n = O(c) vertices suffice), so **no additive correction
> rescues Conjecture 9 of arXiv:2406.19231** ("Z(G) ≤ γ(G) + 2 for connected
> cubic diamond-free G"). Moreover Z(G_k)/γ(G_k) → 9/7, so no inequality of the
> form Z(G) ≤ c·γ(G) with constant c < 9/7 holds on this class either.

This turns the verified refutation in `../WRITEUP.md` (certified values
Z − γ = 3, 3, 4, 5 at k = 2, 3, 4, 5) into a theorem with exact rates, and
resolves both quantities that WRITEUP §7 listed as conjectural
(γ(G_k) = ⌊7k/3⌋ and Z(G_k) = 3k + 1 for all k).

**Proof architecture** (the "direct induction / transfer" lens):

| ingredient | statement | type |
|---|---|---|
| Lemma 3.1 (cut transfer) | Z(G) ≥ Σᵢ Z(G[Vᵢ]) − #(crossing edges) | proved (general) |
| Lemma 4.2 (pieces) | Z(B¹) = Z(B²) = 4 | finite fact, machine-certified twice |
| Theorem 5.1 | Z(G_k) ≥ 4k − (k−1) = 3k+1 | proved |
| Theorem 6.1 | Z(G_k) ≤ 3k+1, explicit set + schedule | proved |
| Theorem 7.1 | γ(G_k) ≤ ⌊7k/3⌋, explicit pattern | proved |
| Lemma 8.2 (window) | any dominating set has ≥ 7 vertices in any 3 consecutive blocks | finite fact, machine-certified twice |
| Theorem 8.4 | γ(G_k) ≥ ⌊7k/3⌋ | proved |

Every lemma was validated by exact computation **before** being proved (see §10);
the transfer lemma is tight at every certified data point (k = 2..5), and the two
formulas agree with every certified or solver-exact value (γ through k = 14, Z
through k = 12 after the new chronological-model computations of §10.4).

---

## 1. The family G_k

**Definition 1.1 (blocks and bridges).** Fix k ≥ 2. For each i ∈ {1, …, k},
block i has vertex set

- Vᵢ = {a⁰ᵢ, a¹ᵢ, a²ᵢ, b⁰ᵢ, b¹ᵢ, b²ᵢ, sᵢ} if i ∈ {1, k} (an **end block**, 7 vertices),
- Vᵢ = {a⁰ᵢ, a¹ᵢ, a²ᵢ, b⁰ᵢ, b¹ᵢ, b²ᵢ, sᵢ, tᵢ} if 1 < i < k (a **middle block**, 8 vertices).

Edges inside block i: all aˣᵢ bʸᵢ (x, y ∈ {0,1,2}) **except** the subdivided ones,
namely except a⁰ᵢ b⁰ᵢ always, and except a¹ᵢ b¹ᵢ when i is a middle block; plus the
subdivision paths a⁰ᵢ–sᵢ–b⁰ᵢ, and a¹ᵢ–tᵢ–b¹ᵢ for middle blocks. (So block i is K₃,₃
with one or two independent edges subdivided.) For end blocks put tᵢ := sᵢ
(block 1's unique subdivision vertex serves as its "out" port, block k's as its
"in" port).

Bridges: for i = 1, …, k−1 add the edge tᵢ s_{i+1}. G_k is the union of the k
blocks and the k−1 bridges; n = 7·2 + 8(k−2) = 8k − 2.

This is exactly `chain(k, 'indep')` of `../chain_study.py`; the reconstruction in
`validate_induction.py` reproduces the shipped files `../chain_indep_k{2..8}.edges`
edge-set-for-edge-set (§10, check A), and G_2 is the certified counterexample G14
(`../certificate_g14.json`).

**Lemma 1.2 (hygiene).** G_k is connected, 3-regular, and triangle-free. Hence it
is diamond-free both as "no diamond subgraph" and as "no induced diamond" (a
diamond contains a triangle either way).

*Proof.* **Degrees.** Subdividing an edge of K₃,₃ leaves its endpoints' degrees at
3 (one neighbor is replaced by the subdivision vertex). Subdivision vertices have
degree 2 inside their block and gain exactly one bridge each: s₁ (= t₁) gains the
bridge to s₂; sₖ gains the bridge from t_{k−1}; for a middle block, sᵢ gains the
bridge from t_{i−1} and tᵢ the bridge to s_{i+1}. So every vertex has degree 3.
**Connectivity.** Each block is connected (K₃,₃ is, and subdividing preserves
connectivity), and the bridges link blocks 1, …, k in a path. **Triangle-freeness.**
A triangle inside a block: subdivided K₃,₃ is triangle-free, since K₃,₃ is
bipartite (triangle-free) and subdividing only lengthens cycles; concretely the
neighborhoods sᵢ → {a⁰ᵢ, b⁰ᵢ} and tᵢ → {a¹ᵢ, b¹ᵢ} are independent pairs (those
edges were removed by the subdivision). A triangle using a bridge tᵢ s_{i+1} would
need a common neighbor of tᵢ and s_{i+1}; but N(tᵢ) ∖ {s_{i+1}} ⊆ Vᵢ and
N(s_{i+1}) ∖ {tᵢ} ⊆ V_{i+1}, disjoint sets. ∎

(Machine validation: cubic/connected/triangle-free asserted for all k ≤ 40,
§10 check A.)

**Remark 1.3 (not bipartite).** G_k contains the 5-cycle
a⁰₁–b¹₁–a¹₁–b⁰₁–s₁–a⁰₁ (all five edges present in block 1: a⁰₁b¹₁, b¹₁a¹₁,
a¹₁b⁰₁, b⁰₁s₁, s₁a⁰₁; machine-checked, §10 A), so G_k is not bipartite. The
theorem is therefore about the triangle-free class; the bipartite analogue is
untouched (§11).

---

## 2. Zero forcing: definitions and order-independence

**Definition 2.1** (verbatim semantics of arXiv:2406.19231v2 §1.1). Given
B ⊆ V(G) ("blue", the rest "white"): *at each discrete time step, if a blue
vertex has a unique white neighbor, then it forces that neighbor to become blue*
(all applicable forces are applied in rounds; see Lemma 2.3 for why round-based
vs. one-at-a-time semantics agree). The **closure** cl(B) is the blue set when no
force is applicable anymore (the process is monotone on a finite set, so it
stabilizes). B is a **zero forcing set** if cl(B) = V(G), and
Z(G) = min{|B| : cl(B) = V(G)}. γ(G) = min{|X| : N[X] = V(G)}.

Call C ⊆ V(G) **stalled** if no force applies from C, i.e. every u ∈ C has
either 0 or ≥ 2 neighbors outside C. cl(B) is by construction the unique stalled
set reached from B by exhaustively applying simultaneous rounds.

**Claim 2.2 (absorption).** Let T be stalled, S ⊆ T, and let S → S ∪ {w} be a
valid single force (u ∈ S, N(u) ∖ S = {w}). Then w ∈ T.

*Proof.* u ∈ T and N(u) ∖ T ⊆ N(u) ∖ S = {w}. If w ∉ T then u has exactly one
neighbor outside T, contradicting stalledness. ∎

**Lemma 2.3 (order-independence and serialization).**
(i) If B ⊆ B′ then cl(B) ⊆ cl(B′) (monotonicity).
(ii) Any maximal sequence of valid **single** forces starting from B terminates
with blue set exactly cl(B). In particular, if cl(B) = V there is a finite
sequence of single forces F₁, …, F_m, F_j = (u_j → w_j), starting from B and
ending with all of V blue, such that at the time of F_j the vertex u_j is blue
and w_j is its unique white neighbor; and every force is applied along an edge
of G.

*Proof.* (i) Induct on rounds of the closure of B: B₀ = B ⊆ cl(B′). If
B_r ⊆ cl(B′) and round r+1 forces w via u ∈ B_r (N(u) ∖ B_r = {w}), apply
Claim 2.2 with T = cl(B′) (stalled), S = B_r: w ∈ cl(B′). So cl(B) ⊆ cl(B′).
(ii) Let C be the final set of a maximal single-force sequence from B; C is
stalled (maximality). *C ⊆ cl(B):* induct along the sequence using Claim 2.2 with
T = cl(B) (stalled), S = the current blue set (⊆ cl(B) by induction; valid force
S → S ∪ {w_j}). *cl(B) ⊆ C:* induct on rounds of cl(B) using Claim 2.2 with
T = C, S = B_r. Hence C = cl(B), and when cl(B) = V the sequence ends all-blue. ∎

---

## 3. The transfer lemma

**Lemma 3.1 (edge-cut superadditivity of Z).** Let G be a graph, let
{V₁, …, V_r} be a partition of V(G), and let B be the set of edges of G whose
endpoints lie in different parts. Then

Z(G) ≥ Σᵢ Z(G[Vᵢ]) − |B|.

*Proof.* Let S be a minimum zero forcing set of G and, by Lemma 2.3(ii), fix a
serialized force sequence F₁, …, F_m from S ending all-blue.

**Claim (one force per edge).** Each edge xy of G is the edge of at most one
force F_j. Indeed, when a force is applied along xy (say x → y), y is white
immediately before and both x, y are blue immediately after — and blue vertices
stay blue. A second force along xy would have to target x or y, but targets are
white at the moment they are forced. ∎

For each part i, let Iᵢ := {w ∈ Vᵢ : some F_j = (u → w) has u ∉ Vᵢ} (the
vertices of Vᵢ forced from outside). Each w ∈ Iᵢ is the target of a force whose
edge uw lies in B; a vertex is forced at most once (it is white before, blue
after), and by the claim each edge of B carries at most one force, so

Σᵢ |Iᵢ| ≤ |B|.

**Claim (projection).** For each i, the set (S ∩ Vᵢ) ∪ Iᵢ is a zero forcing set
of Hᵢ := G[Vᵢ].

Let X := cl_{Hᵢ}((S ∩ Vᵢ) ∪ Iᵢ), a stalled set in Hᵢ. Let C_j ⊆ V(G) denote the
blue set after F₁, …, F_j in G (C₀ = S). We show by induction on j that
C_j ∩ Vᵢ ⊆ X. Base: C₀ ∩ Vᵢ = S ∩ Vᵢ ⊆ X. Step: let F_{j+1} = (u → w); only w
is added. If w ∉ Vᵢ there is nothing to show. If w ∈ Vᵢ and u ∉ Vᵢ, then w ∈ Iᵢ ⊆ X.
If w ∈ Vᵢ and u ∈ Vᵢ: u ∈ C_j ∩ Vᵢ ⊆ X, and N_G(u) ∖ C_j = {w}, so
N_{Hᵢ}(u) ∖ X ⊆ (N_G(u) ∩ Vᵢ) ∖ (C_j ∩ Vᵢ) ⊆ {w} (using C_j ∩ Vᵢ ⊆ X). Suppose
w ∉ X. Then w ∈ N_{Hᵢ}(u) ∖ X (u and w are adjacent in Hᵢ since both lie in Vᵢ),
so N_{Hᵢ}(u) ∖ X = {w} exactly — i.e. u ∈ X has a unique Hᵢ-neighbor outside X,
contradicting that X is stalled in Hᵢ. So w ∈ X. Since C_m = V(G), we get
Vᵢ ⊆ X, i.e. X = Vᵢ. ∎

Therefore Z(Hᵢ) ≤ |S ∩ Vᵢ| + |Iᵢ| for every i, and summing,

Σᵢ Z(G[Vᵢ]) ≤ |S| + Σᵢ |Iᵢ| ≤ Z(G) + |B|. ∎

**Corollary 3.2 (bridge sum).** If e = uv is a bridge of G whose removal leaves
components A ∋ u and B ∋ v, then Z(G) ≥ Z(A) + Z(B) − 1.

**Remark 3.3 (relation to known results).** Lemma 3.1 also follows by iterating
the known edge-spread inequality Z(G) ≥ Z(G − e) − 1 (Edholm–Hogben–Huynh–
LaGrange–Row, *Vertex and edge spread of zero forcing number, maximum nullity,
and minimum rank of a graph*, Linear Algebra Appl. 436 (2012) 4352–4372) over
the |B| crossing edges, together with Z(disjoint union) = Σ Z(components). The
proof above is self-contained and is the form we validate.

**Validation (§10, check D).** 620 randomized exact tests (300 single-bridge
sums, 120 three-piece bridge chains, 200 random partitions with arbitrary
crossing sets), zero violations; and the lemma is **tight** on this family:
equality holds at every certified point k = 2..5 (check C).

---

## 4. The pieces

**Definition 4.1.** Let B¹ be K₃,₃ with one edge subdivided (7 vertices: parts
{a⁰,a¹,a²}, {b⁰,b¹,b²}, edge a⁰b⁰ subdivided by s). Let B² be K₃,₃ with two
*independent* edges subdivided (8 vertices: additionally a¹b¹ subdivided by t).
Explicit edge lists are emitted by the validator as `b1.edges`, `b2.edges`.

**Observation.** Deleting the k−1 bridges of G_k leaves exactly the k blocks as
components: G_k[V₁] ≅ G_k[V_k] ≅ B¹ and G_k[Vᵢ] ≅ B² for 1 < i < k. (Bridges are
the only edges between blocks, by Definition 1.1; machine-checked for the cut of
G_5 in §10 B.)

**Lemma 4.2.** Z(B¹) = 4 and Z(B²) = 4.

*Proof.* **Upper bounds** (explicit schedules; each step's validity is read off
the adjacency lists of Definition 4.1):

- B¹, take {a⁰, a¹, b⁰, b¹} blue. Then a¹ → b² (N(a¹) = {b⁰, b¹, b²}, only b²
  white); b¹ → a² (N(b¹) = {a⁰, a¹, a²}); a⁰ → s (N(a⁰) = {b¹, b², s}, b² now
  blue). All 7 blue.
- B², take {s, a¹, b⁰, b¹} blue. Then s → a⁰ (N(s) = {a⁰, b⁰}); a⁰ → b²
  (N(a⁰) = {b¹, b², s}); b⁰ → a² (N(b⁰) = {a¹, a², s}); a¹ → t
  (N(a¹) = {b⁰, b², t}, b² now blue). All 8 blue.

**Lower bounds** (finite facts, certified twice): no 3-subset of V(B¹) is a zero
forcing set (all C(7,3) = 35 closures computed) and no 3-subset of V(B²) is
(all C(8,3) = 56 closures computed). Certified by (a) `validate_induction.py`
§B (pure-Python bitmask arithmetic, plus an independent exhaustive
`z_exact` routine), and (b) the parent kill's independent Rust verifier:

```
rust_check.exe b1.edges zf 3   ->  NONE        (no 3-set forces)
rust_check.exe b1.edges zffind 4 -> WITNESS 0 1 3 4
rust_check.exe b2.edges zf 3   ->  NONE
rust_check.exe b2.edges zffind 4 -> WITNESS 0 1 3 5
```

Two implementations, two languages, two algorithms (combinations-enumeration
vs. pruned DFS). ∎

---

## 5. The zero forcing lower bound

**Theorem 5.1.** Z(G_k) ≥ 3k + 1 for every k ≥ 2.

*Proof.* Apply Lemma 3.1 with the partition {V₁, …, V_k} into blocks. The
crossing edges are exactly the k − 1 bridges (Definition 1.1). By the
Observation in §4 and Lemma 4.2,

Z(G_k) ≥ Σᵢ Z(G_k[Vᵢ]) − (k−1) = 4k − (k−1) = 3k + 1. ∎

**Tightness.** The certified exact values (parent WRITEUP, two independent
implementations plus a hostile Codex recomputation) are Z = 7, 10, 13, 16 at
k = 2, 3, 4, 5 — equal to 3k + 1 at every point, so Lemma 3.1 loses nothing on
this family. (Fresh Rust re-runs of the k = 4, 5 lower-bound certificates and
new solver-exact computations at k = 6, 7, 8, 10, 12: §10.4.)

---

## 6. The zero forcing upper bound

**Theorem 6.1.** Z(G_k) ≤ 3k + 1 for every k ≥ 2. Explicitly,

S_k := {a⁰₁, a¹₁, b⁰₁, b¹₁} ∪ ⋃_{i=2}^{k} {a¹ᵢ, b⁰ᵢ, b¹ᵢ}, |S_k| = 4 + 3(k−1) = 3k + 1,

is a zero forcing set of G_k.

*Proof.* We exhibit a sequence of valid single forces from S_k that ends with
every vertex blue; such a sequence is maximal (no white vertices remain), so by
Lemma 2.3(ii) its final set equals cl(S_k), i.e. cl(S_k) = V(G_k). Each step
below lists the forcing vertex's full neighborhood so validity can be checked
against Definition 1.1. We prove by induction on i the statement P(i): "after
phase i, all of V₁ ∪ … ∪ Vᵢ is blue, and additionally s_{i+1} is blue (if
i < k)".

**Phase 1.** Blue so far: S_k ∩ V₁ = {a⁰₁, a¹₁, b⁰₁, b¹₁}.
1. a¹₁ → b²₁ (N(a¹₁) = {b⁰₁, b¹₁, b²₁}; b⁰₁, b¹₁ blue).
2. b¹₁ → a²₁ (N(b¹₁) = {a⁰₁, a¹₁, a²₁}).
3. a⁰₁ → s₁ (N(a⁰₁) = {b¹₁, b²₁, s₁}; b²₁ blue by step 1).
4. s₁ → s₂ (N(s₁) = {a⁰₁, b⁰₁, s₂}; recall t₁ = s₁ carries the bridge).
P(1) holds.

**Phase i, 2 ≤ i ≤ k−1** (middle block). By P(i−1), all earlier blocks and sᵢ
are blue; also {a¹ᵢ, b⁰ᵢ, b¹ᵢ} ⊆ S_k.
1. sᵢ → a⁰ᵢ (N(sᵢ) = {a⁰ᵢ, b⁰ᵢ, t_{i−1}}; b⁰ᵢ ∈ S_k, t_{i−1} blue by P(i−1)).
2. a⁰ᵢ → b²ᵢ (N(a⁰ᵢ) = {b¹ᵢ, b²ᵢ, sᵢ}).
3. b⁰ᵢ → a²ᵢ (N(b⁰ᵢ) = {a¹ᵢ, a²ᵢ, sᵢ}).
4. a¹ᵢ → tᵢ (N(a¹ᵢ) = {b⁰ᵢ, b²ᵢ, tᵢ}; b²ᵢ blue by step 2).
5. tᵢ → s_{i+1} (N(tᵢ) = {a¹ᵢ, b¹ᵢ, s_{i+1}}; a¹ᵢ, b¹ᵢ ∈ S_k).
All 8 vertices of Vᵢ are now blue (a⁰, a², b², s, t forced; a¹, b⁰, b¹ in S_k),
so P(i) holds.

**Phase k** (end block). By P(k−1), sₖ is blue; {a¹ₖ, b⁰ₖ, b¹ₖ} ⊆ S_k.
1. sₖ → a⁰ₖ (N(sₖ) = {a⁰ₖ, b⁰ₖ, t_{k−1}}).
2. a⁰ₖ → b²ₖ (N(a⁰ₖ) = {b¹ₖ, b²ₖ, sₖ}).
3. b⁰ₖ → a²ₖ (N(b⁰ₖ) = {a¹ₖ, a²ₖ, sₖ}).
All of V(G_k) is blue. ∎

**Corollary 6.2.** Z(G_k) = 3k + 1 for every k ≥ 2.

**Validation (§10, check G).** cl(S_k) = V(G_k) and |S_k| = 3k+1 verified by
machine for every k ≤ 40; for k ≤ 5 the value 3k+1 is exhaustively optimal
(certified `NONE` at size 3k by Python + Rust, re-run fresh for k = 4, 5).

---

## 7. The domination upper bound

**Theorem 7.1.** γ(G_k) ≤ ⌊7k/3⌋ for every k ≥ 2.

*Proof.* Define four per-block configurations (closed neighborhoods are read off
Definition 1.1; middle-block adjacencies: N(a⁰)={b¹,b²,s}, N(a¹)={b⁰,b²,t},
N(a²)={b⁰,b¹,b²}, N(b⁰)={a¹,a²,s}, N(b¹)={a⁰,a²,t}, N(b²)={a⁰,a¹,a²},
N(s)={a⁰,b⁰,t_{i−1}}, N(t)={a¹,b¹,s_{i+1}}; end blocks: same with the t-edges
replaced by a¹b¹ and the s-bridge as appropriate):

| config | set (in block i) | covers within Vᵢ | covers outside Vᵢ | needs |
|---|---|---|---|---|
| 2A | {a⁰ᵢ, b⁰ᵢ} | middle: Vᵢ ∖ {tᵢ}; end: all of Vᵢ | — | (middle) tᵢ covered by s_{i+1} ∈ D |
| 2B | {a¹ᵢ, b¹ᵢ} | Vᵢ ∖ {sᵢ} (middle and end alike) | — | sᵢ covered by t_{i−1} ∈ D |
| T3 | {sᵢ, tᵢ, a²ᵢ} (middle only) | all of Vᵢ | t_{i−1} and s_{i+1} | — |
| T3′ | {a⁰ᵢ, b⁰ᵢ, tᵢ} (middle only) | all of Vᵢ | s_{i+1} | — |

(2A on a middle block: N[a⁰]∪N[b⁰] = {a⁰,b¹,b²,s} ∪ {b⁰,a¹,a²,s} = Vᵢ∖{tᵢ}; on
an end block the same union is all of Vᵢ since there is no tᵢ. 2B:
N[a¹]∪N[b¹] = {a¹,b⁰,b²,tᵢ} ∪ {b¹,a⁰,a²,tᵢ} = Vᵢ∖{sᵢ}; for an end block i = k,
N[a¹]∪N[b¹] = {a¹,b⁰,b¹,b²} ∪ {b¹,a⁰,a¹,a²} = Vᵢ∖{sᵢ} again. T3:
N[s]∪N[t]∪N[a²] ⊇ {s,a⁰,b⁰} ∪ {t,a¹,b¹} ∪ {a²,b⁰,b¹,b²} = Vᵢ, plus the bridge
ends t_{i−1}, s_{i+1}. T3′: {a⁰,b¹,b²,s} ∪ {b⁰,a¹,a²,s} ∪ {t,a¹,b¹,s_{i+1}} ⊇ Vᵢ
plus s_{i+1}.)

Assign configurations to blocks 1, …, k:

- k = 2: (2A, 2A).
- k = 3m+1, m ≥ 1: 2A on block 1, then m groups (2A, T3, 2B) on blocks
  (3j−1, 3j, 3j+1), j = 1..m.
- k = 3m+2, m ≥ 0: as for 3m+1 with m groups, then 2A on block k.
- k = 3m, m ≥ 1: 2A on block 1, then m−1 groups (2A, T3, 2B) on blocks
  2..k−2, then T3′ on block k−1 and 2B on block k.

Let D_k be the union of the assigned sets. Sizes: 4; 2+7m; 4+7m; 2+7(m−1)+5 =
7m — in each case exactly ⌊7k/3⌋ (since ⌊7(3m+1)/3⌋ = 7m+2, ⌊7(3m+2)/3⌋ = 7m+4,
⌊7·3m/3⌋ = 7m).

D_k dominates G_k: every T3/T3′ block and every end-2A block is fully covered
internally. The deficiencies and their external coverage:

- a middle 2A block i misses only tᵢ; in every assignment a middle 2A block is
  immediately followed by a T3 block, and sᵢ₊₁ ∈ T3 ⊆ D_k dominates tᵢ via the
  bridge.
- a 2B block i misses only sᵢ; in every assignment a 2B block is immediately
  preceded by a T3 or T3′ block, and tᵢ₋₁ ∈ D_k dominates sᵢ via the bridge.

Checking the assignment shapes: inside every (2A, T3, 2B) group both rules hold
by construction (the group's 2A is followed by its T3, its 2B is preceded by its
T3); block 1 and (for k ≡ 2) block k are end-2A, fully covered; for k ≡ 0 the
tail is (T3′ at k−1, 2B at k): block k−1 is fully covered and block k is a 2B
immediately preceded by T3′. The block before the tail (block k−2) is the last
group's 2B when m ≥ 2 (its deficiency sᵢ was already handled inside its group)
and is block 1's end-2A when m = 1 (k = 3, fully covered). Also every T3/T3′
sits on a middle block (indices 3j with 3 ≤ 3j ≤ k−1, and k−1 ≥ 2 respectively),
as required, and end-2A blocks have no deficiency. ∎

**Validation (§10, check F).** D_k built per this assignment dominates G_k with
|D_k| = ⌊7k/3⌋ for every k = 2..40.

---

## 8. The domination lower bound

Throughout this section D is an arbitrary dominating set of G_k and
dᵢ := |D ∩ Vᵢ|.

**Lemma 8.1 (per-block).** dᵢ ≥ 2 for every i.

*Proof.* Let Kᵢ = {a⁰ᵢ, a¹ᵢ, a²ᵢ, b⁰ᵢ, b¹ᵢ, b²ᵢ} (the six branch vertices). Every
neighbor of a vertex of Kᵢ lies in Vᵢ (branch vertices are adjacent only to
branch or subdivision vertices of their own block, Definition 1.1), so the six
vertices of Kᵢ must be dominated by D ∩ Vᵢ. G_k is cubic, so |N[x]| = 4 for
every x; in particular |N[x] ∩ Kᵢ| ≤ 4 < 6, and one vertex cannot dominate Kᵢ.
Hence dᵢ ≥ 2. ∎

**Lemma 8.2 (window).** For any three consecutive blocks i, i+1, i+2,

dᵢ + d_{i+1} + d_{i+2} ≥ 7.

*Proof.* Let W = Vᵢ ∪ V_{i+1} ∪ V_{i+2} and X = D ∩ W. Define the **free set**

F = {sᵢ : if i > 1} ∪ {t_{i+2} : if i+2 < k}.

By Definition 1.1, the only edges of G_k with exactly one endpoint in W are the
boundary bridges t_{i−1}sᵢ (when i > 1) and t_{i+2}s_{i+3} (when i+2 < k). Hence
every w ∈ W ∖ F satisfies N_{G_k}[w] ⊆ W, so w must be dominated by X, and the
domination happens inside the induced subgraph G_k[W]. (Vertices of F may or may
not be dominated from outside; discarding their constraints only weakens the
requirement on X, which is sound for a lower bound.) Therefore X is a
**quasi-dominating set**: N_{G_k[W]}[X] ⊇ W ∖ F.

Up to the explicit translation isomorphism below, the pair (G_k[W], F) is one of
four gadgets, and for each the minimum size of a quasi-dominating set is **7**
(finite fact, machine-certified in two independent implementations, §10 check E;
the worst case F — both free vertices present where applicable — is the one
checked):

| shape | (block types) | occurs when | |W| | F | min quasi-dom |
|---|---|---|---|---|---|
| EMM | (end, mid, mid) | i = 1, i+2 < k | 23 | {t_{i+2}} | 7 |
| MMM | (mid, mid, mid) | 1 < i, i+2 < k | 24 | {sᵢ, t_{i+2}} | 7 |
| MME | (mid, mid, end) | 1 < i, i+2 = k | 23 | {sᵢ} | 7 |
| EME | (end, mid, end) | i = 1, i+2 = k (i.e. k = 3, whole graph) | 22 | ∅ | 7 (= γ(G_3)) |

The gadget depends only on the type triple and on which free vertices exist,
both of which are determined by the case column; the validator instantiates
EMM/MMM/MME from G_5 (blocks 1–3, 2–4, 3–5) and EME from G_3, each with the
maximal F of its case.

**Translation isomorphism.** Blocks of the same type (end/middle) have
identical internal edge patterns under the local labels
a⁰, a¹, a², b⁰, b¹, b², s(, t), and bridges always join tᵢ to s_{i+1}
(Definition 1.1 is translation-invariant in i). Mapping each block of the window
to the block in the same position of the gadget by preserving local labels
therefore maps edges to edges bijectively (block-internal edges by equality of
patterns, the two window-internal bridges to the gadget's bridges) and maps F to
the gadget's free set. The validator additionally asserts, inside the gadget
builder, that every non-free window vertex has all its neighbors inside W and
every free vertex has exactly one neighbor outside W.

Since |X| ≥ 7 in each case, dᵢ + d_{i+1} + d_{i+2} = |X| ≥ 7. ∎

**Remark 8.3.** The free-set relaxation is what makes the finite check sound:
the gadget bound holds for *every* dominating set of *every* G_k, even ones that
dominate the boundary subdivision vertices from outside the window. The data
show the bound is sharp: the (2A, T3, 2B) group of Theorem 7.1 puts exactly 7 in
three consecutive blocks.

**Theorem 8.4.** γ(G_k) ≥ ⌊7k/3⌋ for every k ≥ 2.

*Proof.* Partition the block indices {1, …, k} into consecutive disjoint
segments and add the corresponding bounds (the Vᵢ are pairwise disjoint and
cover V(G_k), so γ(G_k) = Σᵢ dᵢ ≥ Σ_{segments} bound):

- k = 3m: triples {1,2,3}, {4,5,6}, …, {3m−2, 3m−1, 3m}. Shapes: EMM (or EME if
  m = 1), MMM, …, MME. Bound: 7m = ⌊7k/3⌋.
- k = 3m+1 (m ≥ 1): singleton {1} (Lemma 8.1: ≥ 2) + triples {2,3,4}, …,
  {3m−1, 3m, 3m+1}. Shapes: MMM, …, MME. Bound: 2 + 7m = ⌊7k/3⌋.
- k = 3m+2: singletons {1}, {k} + triples {2,3,4}, …, {3m−1, 3m, 3m+1} (all
  MMM). Bound: 4 + 7m = ⌊7k/3⌋. (For m = 0, k = 2: just the two singletons,
  bound 4 = ⌊14/3⌋.)

In each case the per-triple bound is Lemma 8.2 and the per-singleton bound is
Lemma 8.1. ∎

**Corollary 8.5.** γ(G_k) = ⌊7k/3⌋ for every k ≥ 2 (Theorems 7.1 + 8.4) —
matching the independently certified exact values 4, 7, 9, 11, 14, 16, 18 at
k = 2..8 and the CP-SAT values through k = 14 (§10.4).

---

## 9. Proof of Theorem A and Corollary B

By Lemma 1.2, G_k is connected, cubic, triangle-free, with n = 8k−2 (count:
2·7 + (k−2)·8). By Corollaries 6.2 and 8.5, Z(G_k) = 3k+1 and γ(G_k) = ⌊7k/3⌋.
Writing k = 3m + r (r ∈ {0,1,2}):

Z − γ = 3k + 1 − ⌊7k/3⌋ = (2k+3)/3, (2k+4)/3, (2k+5)/3 for r = 0, 1, 2
respectively, i.e. exactly ⌈(2k+3)/3⌉ → ∞. This proves Theorem A.

For Corollary B: given c ≥ 0, take k = ⌈3c/2⌉ + 1; then
Z − γ ≥ (2k+3)/3 ≥ (3c + 2 + 3)/3 > c + 1 > c, with n = 8k − 2 = O(c). The class
qualifier: triangle-free implies no diamond subgraph and a fortiori no induced
diamond. Hence connected cubic diamond-free graphs (either reading) have
unbounded Z − γ, and Conjecture 9 fails by an unbounded margin; sharpness or
any additive weakening Z ≤ γ + c is false for every c. Finally
Z/γ = (3k+1)/⌊7k/3⌋ → 9/7 > 1. ∎

At the certified data points: k = 2..5 give gaps 3, 3, 4, 5 — exactly the values
in the parent WRITEUP's table; the formulas extend them to all k.

---

## 10. Computational validation manifest

All validation is replayable:

```
cd problems\p2-factory\kills\davila-conj9\theorem
python validate_induction.py            # ~7 s, exits 0, all checks PASS
python ilp_crosscheck.py 14             # optional: gamma by CP-SAT, k = 2..14
python z_chrono_check.py 6              # optional: exact Z by CP-SAT (any k)
..\rust_check\target\release\rust_check.exe b1.edges zf 3      # NONE
..\rust_check\target\release\rust_check.exe b2.edges zf 3      # NONE
```

**10.1 What `validate_induction.py` certifies** (run 2026-06-12, all PASS, 7.0 s):

- **A (construction):** G_k is cubic, connected, triangle-free for k ≤ 40;
  n = 8k−2; the rebuilt edge sets equal those of the shipped
  `chain_indep_k{2..8}.edges` files; the non-bipartiteness 5-cycle exists.
- **B (pieces, Lemma 4.2):** the two explicit 4-sets force B¹, B²; **no 3-set
  forces** either piece (exhaustive, 35 + 56 closures, plus an independent
  `z_exact` routine); the five pieces of G_5 cut at its bridges each have Z = 4.
  Emits `b1.edges`/`b2.edges`; Rust dual-check returned `NONE` (size 3) and
  4-witnesses for both — two languages, two algorithms.
- **C (transfer arithmetic):** 4k − (k−1) = 3k+1 equals certified Z at k = 2..5.
- **D (Lemma 3.1, randomized):** 0 violations in 620 exact randomized trials
  (single bridges, 3-piece chains, arbitrary partitions; seeded, deterministic).
- **E (Lemmas 8.1/8.2):** quasi-domination minima: EMM = MMM = MME = **7**,
  EME (= G_3, i.e. γ(G_3)) = **7**, single blocks = **2** — each computed by two
  independent implementations (bitmask vs. set-based); structural side
  conditions (neighbors leaving the window are exactly the boundary bridges)
  asserted; the counting facts behind Lemma 8.1 verified.
- **F (Theorem 7.1):** D_k dominates and |D_k| = ⌊7k/3⌋ for k = 2..40.
- **G (Theorem 6.1):** cl(S_k) = V and |S_k| = 3k+1 for k = 2..40.
- **H (anchors):** exhaustive re-proofs: γ(G_2) ≥ 4, Z(G_2) ≥ 7, γ(G_3) ≥ 7,
  Z(G_3) ≥ 10 (C(22,9) = 497,420 closures, 5 s).

**10.2 Fresh Rust re-runs** (this directory's parent, 2026-06-12):
`chain_indep_k4.edges gamma 8 → NONE`, `zf 12 → NONE`,
`chain_indep_k5.edges gamma 10 → NONE`, `zf 15 → NONE` — re-confirming the
exhaustive lower-bound certificates γ(G_4) ≥ 9, Z(G_4) ≥ 13, γ(G_5) ≥ 11,
Z(G_5) ≥ 16 used in the tightness tables.

**10.3 Certified-values table vs. the proved formulas**

| k | n | γ certified | ⌊7k/3⌋ | Z certified | 3k+1 |
|---|----|----|----|----|----|
| 2 | 14 | 4 (exhaustive ×2) | 4 | 7 (exhaustive ×2) | 7 |
| 3 | 22 | 7 (exhaustive ×2) | 7 | 10 (exhaustive ×2) | 10 |
| 4 | 30 | 9 (exhaustive ×2 + Codex) | 9 | 13 (exhaustive ×2 + Codex) | 13 |
| 5 | 38 | 11 (exhaustive ×2) | 11 | 16 (exhaustive ×2) | 16 |
| 6 | 46 | 14 (Rust exhaustive) | 14 | 19 (CP-SAT optimal, §10.4) | 19 |
| 7 | 54 | 16 (Rust exhaustive) | 16 | 22 (CP-SAT optimal, §10.4) | 22 |
| 8 | 62 | 18 (Rust exhaustive) | 18 | 25 (CP-SAT optimal, §10.4) | 25 |

**10.4 CP-SAT cross-checks** (validation aid only, not part of the proof).
γ(G_k) by ILP (`ilp_crosscheck.py`) equals ⌊7k/3⌋ for every k = 2..14. Z(G_k)
by the standard chronological MIP model (`z_chrono_check.py`: initial-set
variables, forcing-time variables, forcer indicators; optimum = Z, proved
optimal by CP-SAT) equals 3k+1 at k = 5, 6, 7, 8, 10, 12 (Z = 16, 19, 22, 25,
31, 37; every solve < 2 s, every witness re-checked by the independent closure
routine). The k = 6, 7, 8, 10, 12 values are **new exact data points** beyond
the parent WRITEUP's table (which had only upper bounds there, estimating the
k = 6 brute-force lower bound alone at ~7 h), and all agree with Theorem A.
(A naive fort-cover loop was also tried at k = 6 and converged too slowly to be
useful — >2000 forts with the trivial lower bound still at 3; the chronological
model is the right tool at this size.)

**Lens compliance note.** Every structural lemma above was validated against
exact computation before/alongside its proof, on k ≤ 5 with the existing
certified values and beyond (k ≤ 12 for Z via the chronological model, k ≤ 14
for γ via ILP, k ≤ 40 for the explicit constructions), as the task required.

---

## 11. Honest gap list

1. **Machine-checked finite facts.** Four families of facts are certified by
   exhaustive computation rather than by human-readable proof: (i) Z(B¹) ≥ 4
   (35 subsets), (ii) Z(B²) ≥ 4 (56 subsets), (iii) the four window
   quasi-domination minima = 7 (≤ 190,000 coverage checks each), (iv) γ(G_3) ≥ 7
   for the EME case (74,613 subsets). All are finite, deterministic,
   exact-integer computations with no search heuristics; (i)–(ii) are verified
   in two languages/algorithms (Python enumeration + Rust pruned DFS), (iii)–(iv)
   in two independent Python implementations (bitmask vs. set-based). Caveat
   noted by the hostile referee: the two window-minimum implementations share
   the same graph *builder*, so they only doubly certify the minimization, not
   the gadget construction — however, the referee's own independent
   reconstruction of the gadgets (`referee_independent_audit.py`, written
   without reading the validator) reproduced all four minima = 7, closing that
   hole. A symmetry-reduced hand proof of (i)/(ii) (Aut(B¹) has orbits {s},
   {a⁰,b⁰}, {a¹,a²,b¹,b²}, so only a handful of 3-set orbits need checking)
   would be routine but has not been written out; (iii) by hand would be a long
   case analysis. We consider these on the same footing as the parent kill's
   exhaustive certificates.
2. **Standard preliminaries proved, not cited.** Order-independence/serialization
   of zero forcing (Lemma 2.3) is folklore; we prove it from the paper's
   round-based definition to keep the chain airtight. Similarly Lemma 3.1 is
   (as noted in Remark 3.3) an iteration of a known edge-spread inequality; our
   proof is self-contained, so no external correctness dependency remains.
3. **Window-to-gadget transfer.** Lemma 8.2 reduces an infinite family of
   windows to four gadgets via the translation isomorphism; this step is by-hand
   (it is immediate from the translation-invariant Definition 1.1), with the
   structural side conditions additionally machine-asserted for the instantiated
   gadgets. A skeptic should read the two paragraphs of Lemma 8.2 plus
   Definition 1.1; there is no hidden case.
4. **Bipartite version open.** G_k is triangle-free but not bipartite
   (Remark 1.3). Whether Z − γ is unbounded on connected cubic *bipartite*
   graphs remains open; the parenthetical "(bipartite, if true)" in the task
   prompt is **not** established by this construction.
5. **Solver-dependent checks are advisory only.** The CP-SAT results (§10.4)
   double-check the theorem at k ≤ 14 (γ) and k ≤ 12 (Z) but are not part of
   the proof chain; nothing in §§1–9 depends on ortools.
6. **Scope.** The theorem concerns this one family; it determines neither the
   optimal growth rate of Z − γ over the whole class (our family gives
   ≈ n/12; nothing here rules out faster) nor any upper bound of the form
   Z ≤ γ + f(n) for the class.

## 12. Hostile review (Codex, GPT-5.5, 2026-06-12)

A hostile referee pass on this document and the validator was run via the Codex
MCP server (threadId 019eba89-6a29-77e2-b123-b40fded4a884; full shell access;
instructed to break the proof, write its own independent code, and stress-test
the cut lemma adversarially). Verdict, verbatim (abridged to the substantive
content):

> **VERDICT: ACCEPT.** I tried to break the claim gamma(G_k)=floor(7k/3) and
> Z(G_k)=3k+1 for all k>=2. I did not find a fatal or serious flaw. The proof
> survives the audit. […] No fatal flaws. No serious flaws. […]
> I inspected the sensitive validator code. The window_gadget() free-set logic
> is correct: left boundary frees s_i, right boundary frees t_{i+2}, and the
> target is exactly W \ F. The structural assertions check that non-free
> vertices have no outside neighbor and free vertices have exactly one. The
> quasi-domination routines are not vacuous. The validator's forcing_pattern()
> and dominating_pattern() match the markdown constructions.
> I wrote and ran an independent checker: referee_independent_audit.py. It
> imports none of the validator code. Independent results: B1: exact Z=4. B2:
> exact Z=4. Window quasi-domination minima: EMM = 7, MMM = 7, MME = 7,
> EME = 7. Exact chain values: G_2: gamma=4, Z=7; G_3: gamma=7, Z=10; G_4:
> gamma=9, Z=13. The explicit forcing schedule was checked step-by-step for
> k=2..12; every listed force is legal. The explicit domination residue pattern
> was checked for k=2..12; all sizes and coverage are correct. Cut lemma stress
> test: 68,018 exact small graph/partition cases checked; no violation.
> Arithmetic identities checked: floor(7k/3) residues are 7m, 7m+2, 7m+4;
> 3k+1−floor(7k/3)=ceil((2k+3)/3). […] I found no circularity and no mismatch
> with the source paper's zero forcing definition.

The four cosmetic items the referee raised (placeholder §12; a useless
condition in the validator's edge-file check; "machine-certified twice"
overselling for the window gadgets since both implementations share a graph
builder; loose multiplicative phrasing in Corollary B) have all been fixed in
this version: the placeholder is replaced by this section, the dead condition
was deleted from `validate_induction.py`, gap-list item 1 now states the
shared-builder caveat and its closure by the referee's independent
reconstruction, and Corollary B now states the multiplicative claim precisely.
The referee's audit script is preserved as `referee_independent_audit.py`.
