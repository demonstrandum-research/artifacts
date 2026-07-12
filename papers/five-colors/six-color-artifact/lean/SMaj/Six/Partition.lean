/-
SMaj/Six/Partition.lean — the partition/canonicality half of the chain
decomposition and the port-POSITION calculus (campaign C8, lens
C8L3-lean-assembly, 2026-06-13; step 1 of the C7L3 WRITEUP handoff).

`SMaj/Six/ChainDecomp.lean` (campaign C7) banked piece EXISTENCE through
every edge (`exists_piece`) with the linkage-closure fact
(`IsPiece.saturated_of_degree_two`) and the weak port fact
(`IsPiece.end_of_junction`).  What the glue assembly additionally
consumes from the decomposition — and what this file closes — is:

* **the partition facts** (pretest P-E, now Q-E): the linkage relation
  `Linked` (reflexive-transitive closure of "two edges of G sharing a
  degree-2 vertex") is an equivalence (`linkSetoid`), a piece's edge set
  is CLOSED under it (`IsPiece.mem_of_linked`), any two edges of a piece
  are linked (`IsPiece.linked_of_mem`), hence a piece's edge set IS the
  linkage class of any of its edges (`IsPiece.mem_edges_iff_linked`)
  and any two pieces sharing an edge have EQUAL edge sets
  (`IsPiece.edges_toFinset_eq`) — the chain decomposition is canonical
  as a partition, and a choice of piece per linkage class is consistent;

* **the port-POSITION fact** (`IsPiece.eq_first_or_last`, strengthening
  `end_of_junction`): a piece edge incident to a degree-≠ 2 vertex `v`
  IS the first edge `s(x, p.snd)` (with `v = x`) or the last edge
  `s(p.penultimate, y)` (with `v = y`) — by VALUE, which under the
  trail's `edges_nodup` pins its list position.  This is what lets the
  assembly transport the Shannon color of an M-half to its port edge;

* **the slot calculus** for the `interior`/`chain_end` fields:
  `eq_or_eq_of_mem_edges_degree_two` (a walk carries ≤ deg v = 2 edges
  at `v`; two distinct ones exhaust them), the second-edge facts
  `IsPiece.edges_one_eq` / `IsPiece.edges_length_sub_two_eq` (the edge
  after a port is `s(p.snd, z)` at slot 1, resp. `s(p.penultimate, z)`
  at slot L − 2), and the other-edge slot lemmas
  `IsPiece.other_edge_slot_of_chain` (slots i − 1 / i + 1) and
  `IsPiece.other_edge_slot_of_cycle` (modular slots (i + L − 1) % L /
  (i + 1) % L) — exactly the index arithmetic of the fill's distance-2
  guarantee and of the pure-cycle pattern `exists_cycle_distance2`.

Machine pretest BEFORE proving (standing rule):
`lenses/C8L3-lean-assembly/pretest_partition.py`, exit 0 — Q-A..Q-F
model-check the intended statement semantics above on the maximal
walker's pieces (510,046 piece checks: EXHAUSTIVE all labeled graphs
n ≤ 6, both orientations of every edge, classics, 300 randoms n ≤ 14;
the Lean lemmas quantify over arbitrary `IsPiece` witnesses — strictly
more general than the walker-generated corpus; foil caveat S4).

Still owed to the assembly after this file (honest scope): steps 2–5 of
the C6L3 handoff — the piece CHOICE per linkage class, sites/`ix`, the
M-family `t`, the `shannon_six_indexed` instantiation, fills, and the
`IsGlueColoring` bundle.  `maj_le_six` remains `proof_wanted`.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Six.ChainDecomp

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Position foundation: edges by index -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `i`-th edge of a walk joins its `i`-th and `(i+1)`-st vertices
(pretest Q-A). -/
lemma edges_getElem {x y : V} (p : G.Walk x y) {i : ℕ}
    (hi : i < p.edges.length) :
    p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
  have hd : i < p.darts.length := by
    rw [Walk.length_darts]
    rwa [p.length_edges] at hi
  have h1 : p.edges[i] = (p.darts[i]'hd).edge := by
    show (p.darts.map Dart.edge)[i]'(by rwa [List.length_map]) = _
    rw [List.getElem_map]
  rw [h1, Walk.darts_getElem_eq_getVert i hd]
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex at a position strictly between the ends is internal (lies in
`support.tail.dropLast`). -/
lemma getVert_mem_internal {x y : V} (p : G.Walk x y) {n : ℕ}
    (h0 : 0 < n) (hn : n < p.length) :
    p.getVert n ∈ p.support.tail.dropLast := by
  have hlen : p.support.tail.dropLast.length = p.length - 1 := by
    rw [List.length_dropLast, List.length_tail, Walk.length_support]
    omega
  have hidx : n - 1 < p.support.tail.dropLast.length := by omega
  have hval : p.support.tail.dropLast[n - 1] = p.getVert n := by
    have h1 : p.getVert (n - 1 + 1) = p.getVert n := by
      rw [show n - 1 + 1 = n by omega]
    rw [← h1,
      p.getVert_eq_support_getElem (by omega : n - 1 + 1 ≤ p.length)]
    simp only [List.getElem_dropLast, List.getElem_tail]
  rw [← hval]
  exact List.getElem_mem hidx

/-! ### The port-POSITION fact (pretest Q-B) -/

omit [DecidableEq V] in
/-- **Port position** (strengthens `IsPiece.end_of_junction`): a piece
edge incident to a vertex of degree ≠ 2 is the FIRST edge `s(x, p.snd)`
(and the vertex is the start) or the LAST edge `s(p.penultimate, y)`
(and the vertex is the end).  Under `edges_nodup` this pins the edge's
list position to 0 resp. length − 1: at junctions, ports sit exactly at
the two outer slots. -/
theorem IsPiece.eq_first_or_last {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {v : V}
    (hvf : v ∈ f) (hdv : G.degree v ≠ 2) :
    (v = x ∧ f = s(x, p.snd)) ∨ (v = y ∧ f = s(p.penultimate, y)) := by
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hf
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hfeq : f = s(p.getVert i, p.getVert (i + 1)) := by
    rw [← hfi, edges_getElem p hi]
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hfeq] at hvf
    exact Sym2.mem_iff.mp hvf
  rcases hv' with hv | hv
  · -- v sits at position i: i = 0 or v is internal (degree 2)
    have hi0 : i = 0 := by
      by_contra h0
      exact hdv (hp.internal v
        (by rw [hv]; exact getVert_mem_internal p (by omega) hil))
    subst hi0
    refine Or.inl ⟨by rw [hv, Walk.getVert_zero], ?_⟩
    rw [hfeq, Walk.getVert_zero]
  · -- v sits at position i + 1: i + 1 = length or internal
    have hiL : i + 1 = p.length := by
      by_contra hL
      exact hdv (hp.internal v
        (by rw [hv]; exact getVert_mem_internal p (by omega) (by omega)))
    refine Or.inr ⟨by rw [hv, hiL, Walk.getVert_length], ?_⟩
    rw [hfeq]
    have h1 : p.getVert i = p.penultimate := by
      show p.getVert i = p.getVert (p.length - 1)
      rw [show p.length - 1 = i by omega]
    have h2 : p.getVert (i + 1) = y := by rw [hiL, Walk.getVert_length]
    rw [h1, h2]

/-! ### The linkage relation (pretest Q-E) -/

variable (G) in
/-- One linkage step: two edges of `G` sharing a degree-2 vertex. -/
def LinkStep (f g : Sym2 V) : Prop :=
  f ∈ G.edgeSet ∧ g ∈ G.edgeSet ∧ ∃ v : V, G.degree v = 2 ∧ v ∈ f ∧ v ∈ g

variable (G) in
/-- The linkage relation: the reflexive-transitive closure of `LinkStep`.
Its classes on `G.edgeFinset` are exactly the edge sets of the chain
decomposition (`IsPiece.mem_edges_iff_linked` below). -/
def Linked : Sym2 V → Sym2 V → Prop := Relation.ReflTransGen (LinkStep G)

omit [DecidableEq V] in
lemma LinkStep.symm {f g : Sym2 V} (h : LinkStep G f g) : LinkStep G g f := by
  obtain ⟨hf, hg, v, hdv, hvf, hvg⟩ := h
  exact ⟨hg, hf, v, hdv, hvg, hvf⟩

omit [DecidableEq V] in
lemma Linked.refl (f : Sym2 V) : Linked G f f := Relation.ReflTransGen.refl

omit [DecidableEq V] in
lemma Linked.symm {f g : Sym2 V} (h : Linked G f g) : Linked G g f :=
  Relation.ReflTransGen.symmetric (fun _ _ hs => hs.symm) h

omit [DecidableEq V] in
lemma Linked.trans {f g h : Sym2 V} (h₁ : Linked G f g) (h₂ : Linked G g h) :
    Linked G f h := Relation.ReflTransGen.trans h₁ h₂

variable (G) in
/-- Linkage as a setoid on `Sym2 V` (non-edges are isolated points): the
quotient indexes the pieces of the chain decomposition, and
`Quotient.out` gives the assembly its canonical representative per
class. -/
def linkSetoid : Setoid (Sym2 V) :=
  ⟨Linked G, ⟨Linked.refl, Linked.symm, Linked.trans⟩⟩

omit [DecidableEq V] in
/-- Linkage stays inside the edge set. -/
lemma Linked.mem_edgeSet {f g : Sym2 V} (h : Linked G f g)
    (hf : f ∈ G.edgeSet) : g ∈ G.edgeSet := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hstep⟩
  · exact hf
  · exact hstep.2.1

/-! ### Closure: a piece's edge set absorbs linkage -/

/-- **Linkage closure of a piece** (pretest Q-E, closure half): an edge
linked to a piece edge is itself a piece edge.  (Each step shares a
degree-2 vertex with an edge already on the piece, and the piece is
saturated there by `IsPiece.saturated_of_degree_two`.) -/
theorem IsPiece.mem_of_linked {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f g : Sym2 V} (hf : f ∈ p.edges)
    (h : Linked G f g) : g ∈ p.edges := by
  induction h with
  | refl => exact hf
  | @tail b c _ hstep ih =>
    obtain ⟨-, hc, v, hdv, hvb, hvc⟩ := hstep
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvb
    have hvs : v ∈ p.support := Walk.fst_mem_support_of_mem_edges p ih
    exact hp.saturated_of_degree_two hvs hdv c (mem_incFinset.mpr ⟨hc, hvc⟩)

/-! ### Connectivity: all edges of a piece are linked -/

omit [DecidableEq V] in
/-- Along a walk with degree-2 internals, every edge is linked to the
first edge (consecutive walk edges share an internal vertex). -/
private lemma linked_first_of_mem :
    ∀ {x z : V} (p : G.Walk x z),
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      ∀ f ∈ p.edges, Linked G s(x, p.snd) f := by
  intro x z p
  induction p with
  | nil =>
    intro _ f hf
    simp at hf
  | @cons a b c hadj q ih =>
    intro hint f hf
    rw [Walk.edges_cons] at hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · rw [Walk.snd_cons]
      exact Relation.ReflTransGen.refl
    · cases q with
      | nil => simp at hf'
      | @cons _ b' _ hadj' q' =>
        have hintq : ∀ v ∈ (Walk.cons hadj' q').support.tail.dropLast,
            G.degree v = 2 := by
          intro v hv
          apply hint
          rw [Walk.support_cons, List.tail_cons]
          rw [← List.tail_dropLast] at hv
          exact List.mem_of_mem_tail hv
        have hdb : G.degree b = 2 := by
          apply hint
          rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_self ..
        have hstep : LinkStep G
            s(a, (Walk.cons hadj (Walk.cons hadj' q')).snd)
            s(b, (Walk.cons hadj' q').snd) := by
          rw [Walk.snd_cons, Walk.snd_cons]
          exact ⟨G.mem_edgeSet.mpr hadj, G.mem_edgeSet.mpr hadj', b, hdb,
            Sym2.mem_mk_right a b, Sym2.mem_mk_left b b'⟩
        exact Relation.ReflTransGen.head hstep (ih hintq f hf')

omit [DecidableEq V] in
/-- **Piece connectivity** (pretest Q-E, connectivity half): any two
edges of a piece are linked. -/
theorem IsPiece.linked_of_mem {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f g : Sym2 V} (hf : f ∈ p.edges)
    (hg : g ∈ p.edges) : Linked G f g :=
  (linked_first_of_mem p hp.internal f hf).symm.trans
    (linked_first_of_mem p hp.internal g hg)

/-! ### The partition facts: canonical classes and uniqueness -/

/-- **The canonical-partition fact** (pretest Q-E): a piece's edge set is
exactly the linkage class of any of its edges (membership form, no
decidability needed).  The chain decomposition is therefore canonical:
pieces are indexed by the classes of `linkSetoid` on the edge set,
independent of how the walks were grown. -/
theorem IsPiece.mem_edges_iff_linked {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {g : Sym2 V} :
    g ∈ p.edges ↔ g ∈ G.edgeSet ∧ Linked G f g := by
  constructor
  · intro hg
    exact ⟨p.edges_subset_edgeSet hg, hp.linked_of_mem hf hg⟩
  · rintro ⟨-, hlink⟩
    exact hp.mem_of_linked hf hlink

/-- Membership form of the uniqueness fact: two pieces through a common
edge carry exactly the same edges. -/
theorem IsPiece.mem_edges_iff {x y x' y' : V} {p : G.Walk x y}
    {q : G.Walk x' y'} (hp : IsPiece G p) (hq : IsPiece G q) {f : Sym2 V}
    (hf : f ∈ p.edges) (hf' : f ∈ q.edges) {g : Sym2 V} :
    g ∈ p.edges ↔ g ∈ q.edges := by
  rw [hp.mem_edges_iff_linked hf, hq.mem_edges_iff_linked hf']

/-- **Piece edge-set uniqueness** (pretest Q-E, the C8 charter item): two
pieces through a common edge have EQUAL edge sets — the choice of piece
per linkage class is consistent, whatever walks the walker grew. -/
theorem IsPiece.edges_toFinset_eq {x y x' y' : V} {p : G.Walk x y}
    {q : G.Walk x' y'} (hp : IsPiece G p) (hq : IsPiece G q) {f : Sym2 V}
    (hf : f ∈ p.edges) (hf' : f ∈ q.edges) :
    p.edges.toFinset = q.edges.toFinset := by
  ext g
  rw [List.mem_toFinset, List.mem_toFinset]
  exact hp.mem_edges_iff hq hf hf'

/-! ### The slot calculus (pretests Q-C, Q-D, Q-F) -/

/-- **The pair fact** (pretest Q-C): a walk carries at most
`deg v = 2` edges at `v`, so two DISTINCT walk edges at `v` exhaust
them: any walk edge at `v` is one of the two. -/
lemma eq_or_eq_of_mem_edges_degree_two {x y : V} {p : G.Walk x y} {v : V}
    (hdv : G.degree v = 2) {e₁ e₂ : Sym2 V} (h₁ : e₁ ∈ p.edges)
    (h₂ : e₂ ∈ p.edges) (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) (hne : e₁ ≠ e₂)
    {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f) : f = e₁ ∨ f = e₂ := by
  have hsub : {g ∈ p.edges.toFinset | v ∈ g} ⊆ G.incidenceFinset v := by
    intro g hg
    rw [Finset.mem_filter, List.mem_toFinset] at hg
    exact mem_incFinset.mpr ⟨p.edges_subset_edgeSet hg.1, hg.2⟩
  have hcard : #{g ∈ p.edges.toFinset | v ∈ g} ≤ 2 := by
    have h := Finset.card_le_card hsub
    rwa [card_incidenceFinset_eq_degree, hdv] at h
  have hpsub : ({e₁, e₂} : Finset (Sym2 V)) ⊆
      {g ∈ p.edges.toFinset | v ∈ g} := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h₁, hv₁⟩
    · rw [Finset.mem_singleton] at hg
      subst hg
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h₂, hv₂⟩
  have heq : ({e₁, e₂} : Finset (Sym2 V)) =
      {g ∈ p.edges.toFinset | v ∈ g} :=
    Finset.eq_of_subset_of_card_le hpsub
      (by rw [Finset.card_pair hne]; exact hcard)
  have hfm : f ∈ ({e₁, e₂} : Finset (Sym2 V)) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hf, hvf⟩
  simpa using hfm

omit [DecidableEq V] in
/-- A piece whose start is no degree-2 vertex but whose second vertex is
has length ≥ 2 (a one-edge piece would make the second vertex an end). -/
theorem IsPiece.two_le_length_of_snd {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdw : G.degree p.snd = 2) :
    2 ≤ p.length := by
  rcases hp.ends with ⟨-, hdy⟩ | ⟨-, hall⟩
  · by_contra h
    have h1 : p.length = 1 := by
      have := hp.ne
      omega
    have hsy : p.snd = y := by
      show p.getVert 1 = y
      rw [← h1]
      exact p.getVert_length
    exact hdy (hsy ▸ hdw)
  · exact absurd (hall x p.start_mem_support) hdx

omit [DecidableEq V] in
/-- Mirror of `two_le_length_of_snd` at the far end. -/
theorem IsPiece.two_le_length_of_penultimate {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdy : G.degree y ≠ 2)
    (hdw : G.degree p.penultimate = 2) : 2 ≤ p.length := by
  rcases hp.ends with ⟨hdx, -⟩ | ⟨-, hall⟩
  · by_contra h
    have h1 : p.length = 1 := by
      have := hp.ne
      omega
    have hsx : p.penultimate = x := by
      show p.getVert (p.length - 1) = x
      rw [h1]
      exact p.getVert_zero
    exact hdx (hsx ▸ hdw)
  · exact absurd (hall y p.end_mem_support) hdy

/-- **The second-edge fact** (pretest Q-D): on a piece whose start `x` is
a junction/pendant and whose second vertex `w := p.snd` is internal
(degree 2), the edge after the port to the OTHER neighbor `z ≠ x` of `w`
is exactly slot 1: `p.edges[1] = s(p.snd, z)`.  This is where the
`chain_end` field's inward edge lives. -/
theorem IsPiece.edges_one_eq {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdw : G.degree p.snd = 2)
    {z : V} (hz : G.Adj p.snd z) (hzx : z ≠ x) :
    ∃ h : 1 < p.edges.length, p.edges[1] = s(p.snd, z) := by
  have hlen : 2 ≤ p.length := hp.two_le_length_of_snd hdx hdw
  have h1 : 1 < p.edges.length := by
    rw [p.length_edges]
    omega
  have h0 : 0 < p.edges.length := by omega
  refine ⟨h1, ?_⟩
  have he0 : p.edges[0] = s(x, p.snd) := by
    rw [edges_getElem p h0, Walk.getVert_zero]
  have he1 : p.edges[1] = s(p.getVert 1, p.getVert 2) := edges_getElem p h1
  have hne : p.edges[0] ≠ p.edges[1] := fun h =>
    absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
  have hmem : s(p.snd, z) ∈ p.edges := by
    apply hp.saturated_of_degree_two (p.getVert_mem_support 1) hdw
    exact mem_incFinset.mpr
      ⟨G.mem_edgeSet.mpr hz, Sym2.mem_mk_left p.snd z⟩
  rcases eq_or_eq_of_mem_edges_degree_two hdw (List.getElem_mem h0)
      (List.getElem_mem h1)
      (by rw [he0]; exact Sym2.mem_mk_right x p.snd)
      (by rw [he1]; exact Sym2.mem_mk_left _ _)
      hne hmem (Sym2.mem_mk_left p.snd z) with h | h
  · exfalso
    rw [he0] at h
    rcases Sym2.eq_iff.mp h with ⟨h1', -⟩ | ⟨-, h2'⟩
    · exact hdx (h1' ▸ hdw)
    · exact hzx h2'
  · exact h.symm

/-- Mirror of `edges_one_eq` at the far end: the edge before the last
port is slot `length − 2`: `p.edges[p.edges.length − 2] =
s(p.penultimate, z)` for the other neighbor `z ≠ y` of the penultimate
vertex. -/
theorem IsPiece.edges_length_sub_two_eq {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdy : G.degree y ≠ 2)
    (hdw : G.degree p.penultimate = 2) {z : V}
    (hz : G.Adj p.penultimate z) (hzy : z ≠ y) :
    ∃ h : p.edges.length - 2 < p.edges.length,
      p.edges[p.edges.length - 2] = s(p.penultimate, z) := by
  have hlen : 2 ≤ p.length := hp.two_le_length_of_penultimate hdy hdw
  have hL : p.edges.length = p.length := p.length_edges
  have hsub : p.edges.length - 2 < p.edges.length := by omega
  have hlast : p.edges.length - 1 < p.edges.length := by omega
  refine ⟨hsub, ?_⟩
  have helast : p.edges[p.edges.length - 1] = s(p.penultimate, y) := by
    rw [edges_getElem p hlast, hL,
      show p.length - 1 + 1 = p.length by omega, p.getVert_length]
  have hesub : p.edges[p.edges.length - 2] =
      s(p.getVert (p.length - 2), p.penultimate) := by
    rw [edges_getElem p hsub, hL,
      show p.length - 2 + 1 = p.length - 1 by omega]
  have hne : p.edges[p.edges.length - 1] ≠ p.edges[p.edges.length - 2] :=
    fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
  have hpen : p.penultimate ∈ p.support := p.getVert_mem_support _
  have hmem : s(p.penultimate, z) ∈ p.edges := by
    apply hp.saturated_of_degree_two hpen hdw
    exact mem_incFinset.mpr
      ⟨G.mem_edgeSet.mpr hz, Sym2.mem_mk_left p.penultimate z⟩
  rcases eq_or_eq_of_mem_edges_degree_two hdw (List.getElem_mem hlast)
      (List.getElem_mem hsub)
      (by rw [helast]; exact Sym2.mem_mk_left _ _)
      (by rw [hesub]; exact Sym2.mem_mk_right _ _)
      hne hmem (Sym2.mem_mk_left p.penultimate z) with h | h
  · exfalso
    rw [helast] at h
    rcases Sym2.eq_iff.mp h with ⟨-, h2'⟩ | ⟨h1', -⟩
    · exact hzy h2'
    · exact hdy (h1' ▸ hdw)
  · exact h.symm

/-- **Chain slot lemma** (pretest Q-F): on a CHAIN piece (both end
degrees ≠ 2), the other piece edge at a degree-2 endpoint `v` of
`p.edges[i]` sits at slot `i − 1` (if `v` is the near vertex) or `i + 1`
(if `v` is the far vertex) — the index arithmetic consumed by the fill's
distance-2 guarantee on `interior` rows. -/
theorem IsPiece.other_edge_slot_of_chain {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdy : G.degree y ≠ 2)
    {i : ℕ} (hi : i < p.edges.length) {v : V} (hv : v ∈ p.edges[i])
    (hdv : G.degree v = 2) {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f)
    (hne : f ≠ p.edges[i]) :
    (v = p.getVert i ∧ 0 < i ∧
      ∃ h : i - 1 < p.edges.length, f = p.edges[i - 1]) ∨
    (v = p.getVert (i + 1) ∧
      ∃ h : i + 1 < p.edges.length, f = p.edges[i + 1]) := by
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hei : p.edges[i] = s(p.getVert i, p.getVert (i + 1)) :=
    edges_getElem p hi
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hei] at hv
    exact Sym2.mem_iff.mp hv
  rcases hv' with hveq | hveq
  · -- near vertex: i ≥ 1 since position 0 is the start x (degree ≠ 2)
    have h0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exact absurd (by rw [hveq, Walk.getVert_zero] at hdv; exact hdv) hdx
      · exact h
    have hprevlt : i - 1 < p.edges.length := by omega
    have heprev : p.edges[i - 1] = s(p.getVert (i - 1), p.getVert i) := by
      rw [edges_getElem p hprevlt, show i - 1 + 1 = i by omega]
    have hneprev : p.edges[i] ≠ p.edges[i - 1] := fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
    rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
        (List.getElem_mem hprevlt)
        (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
        (by rw [heprev, hveq]; exact Sym2.mem_mk_right _ _)
        hneprev hf hvf with h | h
    · exact absurd h hne
    · exact Or.inl ⟨hveq, h0, hprevlt, h⟩
  · -- far vertex: i + 1 ≤ length − 1 since position length is y
    have hL : i + 1 < p.length := by
      rcases Nat.lt_or_ge (i + 1) p.length with h | h
      · exact h
      · exfalso
        have hiL : i + 1 = p.length := by omega
        rw [hveq, hiL, Walk.getVert_length] at hdv
        exact hdy hdv
    have hnextlt : i + 1 < p.edges.length := by
      rw [p.length_edges]
      exact hL
    have henext : p.edges[i + 1] =
        s(p.getVert (i + 1), p.getVert (i + 2)) := edges_getElem p hnextlt
    have hnenext : p.edges[i] ≠ p.edges[i + 1] := fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
    rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
        (List.getElem_mem hnextlt)
        (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
        (by rw [henext, hveq]; exact Sym2.mem_mk_left _ _)
        hnenext hf hvf with h | h
    · exact absurd h hne
    · exact Or.inr ⟨hveq, hnextlt, h⟩

/-- **Cycle slot lemma** (pretest Q-F): on a CLOSED piece all of whose
support vertices have degree 2 (a pure cycle), the other piece edge at a
vertex `v` of `p.edges[i]` sits at the MODULAR slot `(i + L − 1) % L`
(near vertex) or `(i + 1) % L` (far vertex), `L := p.edges.length` —
the wraparound arithmetic consumed by `exists_cycle_distance2` on
`interior` rows of pure cycles. -/
theorem IsPiece.other_edge_slot_of_cycle {x : V} {p : G.Walk x x}
    (hp : IsPiece G p) (hall : ∀ v ∈ p.support, G.degree v = 2)
    {i : ℕ} (hi : i < p.edges.length) {v : V} (hv : v ∈ p.edges[i])
    {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f)
    (hne : f ≠ p.edges[i]) :
    (v = p.getVert i ∧
      ∃ h : (i + p.edges.length - 1) % p.edges.length < p.edges.length,
        f = p.edges[(i + p.edges.length - 1) % p.edges.length]) ∨
    (v = p.getVert (i + 1) ∧
      ∃ h : (i + 1) % p.edges.length < p.edges.length,
        f = p.edges[(i + 1) % p.edges.length]) := by
  have h3 : 3 ≤ p.length := hp.three_le_length
  have hL : p.edges.length = p.length := p.length_edges
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hei : p.edges[i] = s(p.getVert i, p.getVert (i + 1)) :=
    edges_getElem p hi
  have hdv : G.degree v = 2 := by
    apply hall
    rw [hei] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact p.getVert_mem_support i
    · exact p.getVert_mem_support (i + 1)
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hei] at hv
    exact Sym2.mem_iff.mp hv
  rcases hv' with hveq | hveq
  · -- near vertex: previous slot, wrapping at i = 0
    left
    refine ⟨hveq, ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- wrap: the other edge at the basepoint is the last edge
      have hmod : (0 + p.edges.length - 1) % p.edges.length =
          p.edges.length - 1 := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      refine ⟨by omega, ?_⟩
      have hlastlt : p.edges.length - 1 < p.edges.length := by omega
      have helast : p.edges[p.edges.length - 1] =
          s(p.getVert (p.length - 1), x) := by
        rw [edges_getElem p hlastlt, hL,
          show p.length - 1 + 1 = p.length by omega, p.getVert_length]
      have hnelast : p.edges[0] ≠ p.edges[p.edges.length - 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hlastlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
          (by rw [helast, hveq, Walk.getVert_zero]
              exact Sym2.mem_mk_right _ _)
          hnelast hf hvf with h | h
      · exact absurd h hne
      · exact h
    · -- interior: the previous slot, no wrap
      have hmod : (i + p.edges.length - 1) % p.edges.length = i - 1 := by
        rw [show i + p.edges.length - 1 = p.edges.length + (i - 1) by omega,
          Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have hprevlt : i - 1 < p.edges.length := by omega
      refine ⟨hprevlt, ?_⟩
      have heprev : p.edges[i - 1] =
          s(p.getVert (i - 1), p.getVert i) := by
        rw [edges_getElem p hprevlt, show i - 1 + 1 = i by omega]
      have hneprev : p.edges[i] ≠ p.edges[i - 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hprevlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
          (by rw [heprev, hveq]; exact Sym2.mem_mk_right _ _)
          hneprev hf hvf with h | h
      · exact absurd h hne
      · exact h
  · -- far vertex: next slot, wrapping at i + 1 = length
    right
    refine ⟨hveq, ?_⟩
    rcases Nat.lt_or_ge (i + 1) p.edges.length with hlt | hge
    · -- interior: the next slot, no wrap
      have hmod : (i + 1) % p.edges.length = i + 1 := Nat.mod_eq_of_lt hlt
      rw [hmod]
      refine ⟨hlt, ?_⟩
      have henext : p.edges[i + 1] =
          s(p.getVert (i + 1), p.getVert (i + 2)) := edges_getElem p hlt
      have hnenext : p.edges[i] ≠ p.edges[i + 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
          (by rw [henext, hveq]; exact Sym2.mem_mk_left _ _)
          hnenext hf hvf with h | h
      · exact absurd h hne
      · exact h
    · -- wrap: the other edge at the basepoint is the first edge
      have hiL : i + 1 = p.edges.length := by omega
      have hmod : (i + 1) % p.edges.length = 0 := by
        rw [hiL, Nat.mod_self]
      rw [hmod]
      have h0lt : 0 < p.edges.length := by omega
      refine ⟨h0lt, ?_⟩
      have he0 : p.edges[0] = s(x, p.getVert 1) := by
        rw [edges_getElem p h0lt, Walk.getVert_zero]
      have hne0 : p.edges[i] ≠ p.edges[0] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem h0lt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
          (by rw [he0, hveq, show i + 1 = p.length by omega,
                p.getVert_length]
              exact Sym2.mem_mk_left _ _)
          hne0 hf hvf with h | h
      · exact absurd h hne
      · exact h

/-! ### Honest scope note

Banked here: the partition/canonicality facts (linkage equivalence,
closure, connectivity, canonical classes, edge-set uniqueness), the
port-POSITION fact, and the slot calculus (pair fact, second-edge facts,
chain/cycle other-edge slots) — step 1 of the C7L3 handoff in full.
NOT yet formalized (steps 2–5, still owed): the piece CHOICE per linkage
class, sites/`ix`, the M-family `t : ι → Sym2 N`, the
`shannon_six_indexed` instantiation, the fills, and the `IsGlueColoring`
bundle.  `maj_le_six` remains `proof_wanted`. -/

end SMaj
