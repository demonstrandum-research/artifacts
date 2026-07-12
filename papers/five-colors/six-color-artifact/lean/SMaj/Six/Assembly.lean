/-
SMaj/Six/Assembly.lean — step 2 of the `maj_le_six` assembly: the piece
CHOICE per linkage class, the sites/grouping `glueIx`, the M-node type,
the member family `t : Member G → Sym2 (MNode G)`, the per-node ≤ 4
bound, and the Shannon member coloring (campaign C8, lens
C8L3-lean-assembly session 2, 2026-06-13).

`SMaj/Six/Partition.lean` made the chain decomposition canonical (a
piece's edge set is the linkage class of any of its edges).  This file
consumes that canonicality to CHOOSE one piece per linkage class
(`classPiece`, via `Quotient`-representatives — consistent by
`IsPiece.edges_toFinset_eq`) and builds the contraction multigraph M of
the ≤ 6 construction as an indexed family, exactly in the shape
`shannon_six_indexed` (campaign C6) consumes:

* `glueIx` — the glue grouping: `evenIx G 4` at junctions (degree ≥ 3;
  group sizes ≤ 4, group counts ≤ ⌈d/4⌉ = the `junction_groups` field),
  `evenIx G 1` at degree ≤ 2 vertices (singleton groups — the l = 2
  monochromatic chains FORCE rainbow-freeness there);
* `MNode` — M-nodes: junction/kept group sites `(v, k)` (`k` bounded by
  `Fintype.card V + 1`, keeping the node type FINITE for Shannon) ⊕ one
  middle node per linkage class (`Quotient (linkSetoid G)`);
* `Member` — the M-edges: per CHAIN class one member (the whole chain)
  when its piece has ≤ 2 edges, two members (L/R halves through the
  middle node) when ≥ 3; pure cycles contribute none;
* `mfam` — the family itself, with `mfam_not_isDiag` (looplessness; a
  closed trail has ≥ 3 edges, so short chains have distinct ends) and
  `mfam_count_le` (per-node count ≤ 4: at a group site the members
  inject into the ≤ 4 edges of the group via their PORT edges —
  first/last edges of the chosen pieces, distinct by `edges_nodup`; at
  a middle node only the class's own two halves appear);
* `exists_member_coloring` — `shannon_six_indexed` instantiated: a
  6-coloring of the members, distinct at shared M-nodes.  This is the
  (G3) coloring layer of the glue construction, on the REAL M of an
  arbitrary graph.

Machine pretest BEFORE proving (standing rule):
`lenses/C8L3-lean-assembly/pretest_assembly.py`, exit 0 — R-A..R-F pin
the design on 255,050 edge checks (EXHAUSTIVE all labeled graphs n ≤ 5
and n = 6, classics incl. a degree-9 star of chains, 300 randoms
n ≤ 14): fiber bounds, member well-formedness/looplessness, per-node
counts, the member → port-edge injection, port coverage, and Shannon
6-colorability (the pretest's own first run caught that GREEDY needs 7
colors — 6 genuinely needs the banked Shannon theorem).

Still owed to the assembly after this file (honest scope): the port
coloring/its agreement with `satSet`, the fills, the global coloring,
the `IsGlueColoring` bundle, and `maj_le_six` (which remains
`proof_wanted`), plus `rainbow_of_groupSizes` (Vizing).
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Master
import SMaj.Six.ChainDecomp
import SMaj.Six.Partition
import SMaj.Six.Construct

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Per-vertex forms of the even-grouping facts (`SMaj/Master.lean`
proves them inline inside `exists_even_grouping`; the assembly needs
them per vertex and per fiber). -/

/-- Group sizes of `evenIx` are ≤ s, per vertex and group. -/
lemma evenIx_fiber_le (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (hs : 1 ≤ s) (v : V) (k : ℕ) :
    #{f ∈ G.incidenceFinset v | evenIx G s v f = k} ≤ s := by
  calc #{f ∈ G.incidenceFinset v | evenIx G s v f = k}
      ≤ #{i ∈ Finset.range #(G.incidenceFinset v) | i / s = k} := by
        apply card_le_card_of_injOn
          (fun f => if h : f ∈ G.incidenceFinset v
            then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0)
        · intro f hf
          rw [mem_coe, mem_filter] at hf
          obtain ⟨hmem, hval⟩ := hf
          rw [evenIx, dif_pos hmem] at hval
          show (if h : f ∈ G.incidenceFinset v
            then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0) ∈ _
          rw [dif_pos hmem, mem_coe, mem_filter, mem_range]
          exact ⟨((G.incidenceFinset v).equivFin ⟨f, hmem⟩).isLt, hval⟩
        · intro f₁ h₁ f₂ h₂ heq
          rw [mem_coe, mem_filter] at h₁ h₂
          simp only [dif_pos h₁.1, dif_pos h₂.1] at heq
          have hfin : ((G.incidenceFinset v).equivFin ⟨f₁, h₁.1⟩) =
              ((G.incidenceFinset v).equivFin ⟨f₂, h₂.1⟩) :=
            Fin.val_injective heq
          exact Subtype.ext_iff.mp
            ((G.incidenceFinset v).equivFin.injective hfin)
    _ ≤ s := card_div_fiber_le _ hs k

/-- Group counts of `evenIx` are ≤ h_s(d), per vertex. -/
lemma groups_evenIx_le (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (hs : 1 ≤ s) (v : V) :
    groups G (evenIx G s) v ≤ hfun s (G.degree v) := by
  rw [groups]
  split_ifs with hd
  · exact Nat.zero_le _
  · rw [hfun, if_neg (by omega)]
    calc #((G.incidenceFinset v).image (evenIx G s v))
        ≤ #(Finset.range ((G.degree v - 1) / s + 1)) := by
          apply card_le_card
          intro k hk
          rw [mem_image] at hk
          obtain ⟨f, hf, hfk⟩ := hk
          rw [evenIx, dif_pos hf] at hfk
          rw [mem_range]
          have hlt : ((G.incidenceFinset v).equivFin ⟨f, hf⟩ : ℕ) <
              G.degree v := by
            have h := ((G.incidenceFinset v).equivFin ⟨f, hf⟩).isLt
            have hc : #(G.incidenceFinset v) = G.degree v := by
              rw [card_incidenceFinset_eq_degree]
            omega
          subst hfk
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
      _ = (G.degree v + s - 1) / s := by
          rw [card_range, ← Nat.add_div_right _ (by omega : 0 < s)]
          congr 1
          omega

/-- `evenIx G 1` is injective on the incidence finset (singleton
groups): the rainbow field is free at its vertices. -/
lemma evenIx_one_inj {v : V} {f₁ f₂ : Sym2 V}
    (h₁ : f₁ ∈ G.incidenceFinset v) (h₂ : f₂ ∈ G.incidenceFinset v)
    (h : evenIx G 1 v f₁ = evenIx G 1 v f₂) : f₁ = f₂ := by
  rw [evenIx, evenIx, dif_pos h₁, dif_pos h₂, Nat.div_one, Nat.div_one] at h
  exact Subtype.ext_iff.mp
    ((G.incidenceFinset v).equivFin.injective (Fin.val_injective h))

/-! ### The glue grouping -/

variable (G) in
/-- **The glue grouping** (the `ix` of the future `IsGlueColoring`):
`evenIx G 4` at junctions (degree ≥ 3), singleton groups (`evenIx G 1`)
at degree ≤ 2 vertices.  The l = 2 chains are monochromatic in the ≤ 6
construction, so their shared degree-2 vertex must not group its two
edges together — singleton groups make the rainbow field free there. -/
noncomputable def glueIx : V → Sym2 V → ℕ := fun v =>
  if 3 ≤ G.degree v then evenIx G 4 v else evenIx G 1 v

lemma glueIx_eq_junction {v : V} (h : 3 ≤ G.degree v) :
    glueIx G v = evenIx G 4 v := by
  unfold glueIx
  exact if_pos h

lemma glueIx_eq_low {v : V} (h : ¬3 ≤ G.degree v) :
    glueIx G v = evenIx G 1 v := by
  unfold glueIx
  exact if_neg h

/-- Every `glueIx` group has at most 4 members. -/
lemma glueIx_fiber_le (v : V) (k : ℕ) :
    #{f ∈ G.incidenceFinset v | glueIx G v f = k} ≤ 4 := by
  by_cases h : 3 ≤ G.degree v
  · rw [glueIx_eq_junction h]
    exact evenIx_fiber_le G (by omega) v k
  · rw [glueIx_eq_low h]
    exact le_trans (evenIx_fiber_le G le_rfl v k) (by omega)

/-- At junctions, `glueIx` uses at most ⌈d/4⌉ groups — the
`junction_groups` field of the glue bundle. -/
lemma groups_glueIx_le {v : V} (h : 3 ≤ G.degree v) :
    groups G (glueIx G) v ≤ hfun 4 (G.degree v) := by
  have heq : groups G (glueIx G) v = groups G (evenIx G 4) v := by
    unfold groups
    rw [glueIx_eq_junction h]
  rw [heq]
  exact groups_evenIx_le G (by omega) v

/-- At degree ≤ 2 vertices, `glueIx` groups are singletons: two incident
edges in one group are equal (the rainbow field is free there). -/
lemma glueIx_inj_low {v : V} (h : ¬3 ≤ G.degree v) {f₁ f₂ : Sym2 V}
    (h₁ : f₁ ∈ G.incidenceFinset v) (h₂ : f₂ ∈ G.incidenceFinset v)
    (heq : glueIx G v f₁ = glueIx G v f₂) : f₁ = f₂ := by
  rw [glueIx_eq_low h] at heq
  exact evenIx_one_inj h₁ h₂ heq

/-- `glueIx` values are bounded by `Fintype.card V` — the group index
fits in `Fin (Fintype.card V + 1)`, keeping the M-node type finite. -/
lemma glueIx_lt (v : V) (f : Sym2 V) :
    glueIx G v f < Fintype.card V + 1 := by
  have hgen : ∀ s : ℕ, evenIx G s v f < Fintype.card V + 1 := by
    intro s
    rw [evenIx]
    split_ifs with h
    · have h1 : ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) <
          #(G.incidenceFinset v) := Fin.isLt _
      have h2 : #(G.incidenceFinset v) ≤ Fintype.card V := by
        rw [card_incidenceFinset_eq_degree, ← card_neighborFinset_eq_degree]
        exact card_le_univ _
      have h3 := Nat.div_le_self
        ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) s
      omega
    · omega
  by_cases h : 3 ≤ G.degree v
  · rw [glueIx_eq_junction h]; exact hgen 4
  · rw [glueIx_eq_low h]; exact hgen 1

/-! ### Pieces as bundled data, and the choice per linkage class -/

variable (G) in
/-- A piece of the chain decomposition, bundled with its endpoints (the
walk-level certificate is `IsPiece`, `SMaj/Six/ChainDecomp.lean`). -/
structure Piece where
  a : V
  b : V
  walk : G.Walk a b
  piece : IsPiece G walk

namespace Piece

/-- The first edge, by value (matches `IsPiece.eq_first_or_last`). -/
def firstEdge (P : Piece G) : Sym2 V := s(P.a, P.walk.snd)

/-- The last edge, by value (matches `IsPiece.eq_first_or_last`). -/
def lastEdge (P : Piece G) : Sym2 V := s(P.walk.penultimate, P.b)

/-- Pure-cycle discriminator: chains have start degree ≠ 2, pure cycles
start degree 2 (a piece's ends-dichotomy separates exactly there). -/
def IsCycle (P : Piece G) : Prop := G.degree P.a = 2

omit [DecidableEq V] in
lemma chain_ends (P : Piece G) (h : ¬P.IsCycle) :
    G.degree P.a ≠ 2 ∧ G.degree P.b ≠ 2 := by
  rcases P.piece.ends with h1 | ⟨-, hall⟩
  · exact h1
  · exact absurd (hall P.a P.walk.start_mem_support) h

omit [DecidableEq V] in
lemma cycle_spec (P : Piece G) (h : P.IsCycle) :
    P.a = P.b ∧ ∀ v ∈ P.walk.support, G.degree v = 2 := by
  rcases P.piece.ends with ⟨h1, -⟩ | h2
  · exact absurd h h1
  · exact h2

omit [DecidableEq V] in
lemma edges_length_pos (P : Piece G) : 0 < P.walk.edges.length := by
  rw [P.walk.length_edges]
  exact Nat.pos_of_ne_zero P.piece.ne

omit [DecidableEq V] in
/-- The first edge sits at slot 0. -/
lemma firstEdge_eq (P : Piece G) :
    ∃ h : 0 < P.walk.edges.length, P.walk.edges[0] = P.firstEdge := by
  refine ⟨P.edges_length_pos, ?_⟩
  rw [edges_getElem P.walk P.edges_length_pos, Walk.getVert_zero]
  rfl

omit [DecidableEq V] in
/-- The last edge sits at slot `length − 1`. -/
lemma lastEdge_eq (P : Piece G) :
    ∃ h : P.walk.edges.length - 1 < P.walk.edges.length,
      P.walk.edges[P.walk.edges.length - 1] = P.lastEdge := by
  have h0 := P.edges_length_pos
  have hL : P.walk.edges.length = P.walk.length := P.walk.length_edges
  refine ⟨by omega, ?_⟩
  rw [edges_getElem P.walk (by omega), hL,
    show P.walk.length - 1 + 1 = P.walk.length by omega,
    P.walk.getVert_length]
  rfl

omit [DecidableEq V] in
lemma firstEdge_mem (P : Piece G) : P.firstEdge ∈ P.walk.edges := by
  obtain ⟨h, heq⟩ := P.firstEdge_eq
  rw [← heq]
  exact List.getElem_mem h

omit [DecidableEq V] in
lemma lastEdge_mem (P : Piece G) : P.lastEdge ∈ P.walk.edges := by
  obtain ⟨h, heq⟩ := P.lastEdge_eq
  rw [← heq]
  exact List.getElem_mem h

omit [DecidableEq V] in
/-- On a piece with ≥ 2 edges, the first and last edges differ
(`edges_nodup`). -/
lemma firstEdge_ne_lastEdge (P : Piece G) (h2 : 2 ≤ P.walk.length) :
    P.firstEdge ≠ P.lastEdge := by
  obtain ⟨hf, hfe⟩ := P.firstEdge_eq
  obtain ⟨hl, hle⟩ := P.lastEdge_eq
  intro heq
  have h : P.walk.edges[0] = P.walk.edges[P.walk.edges.length - 1] := by
    rw [hfe, hle, heq]
  have h01 := (P.piece.trail.edges_nodup.getElem_inj_iff).mp h
  have hL : P.walk.edges.length = P.walk.length := P.walk.length_edges
  omega

omit [DecidableEq V] in
/-- Short pieces (< 3 edges) have distinct ends: a closed trail has ≥ 3
edges — the looplessness input for whole-chain members. -/
lemma a_ne_b_of_length_lt_three (P : Piece G) (hl : P.walk.length < 3) :
    P.a ≠ P.b := by
  obtain ⟨a, b, w, hp⟩ := P
  show a ≠ b
  rintro rfl
  exact absurd (three_le_length_of_closed hp.trail hp.ne) (by
    simp only at hl
    omega)

end Piece

/-- Every edge lies on some (bundled) piece — `exists_piece`
repackaged. -/
lemma exists_piece_through {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, e ∈ P.walk.edges := by
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    obtain ⟨x, y, p, hp, hm⟩ := exists_piece (G.mem_edgeSet.mp he)
    exact ⟨⟨x, y, p, hp⟩, hm⟩

variable (G) in
/-- The edge classes: linkage classes represented by an edge.  These
index the pieces of the canonical decomposition. -/
abbrev EdgeClass : Type _ :=
  {q : Quotient (linkSetoid G) // q.out ∈ G.edgeSet}

variable (G) in
/-- **The piece choice**: one piece per edge class, through the class's
canonical representative.  Consistent by `IsPiece.edges_toFinset_eq`
(any two pieces through a common edge have equal edge sets). -/
noncomputable def classPiece (q : EdgeClass G) : Piece G :=
  (exists_piece_through q.2).choose

variable (G) in
lemma classPiece_mem (q : EdgeClass G) :
    q.1.out ∈ (classPiece G q).walk.edges :=
  (exists_piece_through q.2).choose_spec

variable (G) in
/-- Every edge of a class's piece belongs to that class. -/
lemma classPiece_class_eq {q : EdgeClass G} {g : Sym2 V}
    (hg : g ∈ (classPiece G q).walk.edges) :
    Quotient.mk (linkSetoid G) g = q.1 := by
  have h1 : Linked G g q.1.out :=
    (classPiece G q).piece.linked_of_mem hg (classPiece_mem G q)
  calc Quotient.mk (linkSetoid G) g
      = Quotient.mk (linkSetoid G) q.1.out := Quotient.sound h1
    _ = q.1 := Quotient.out_eq _

omit [DecidableEq V] in
/-- The class representative of an edge is an edge. -/
lemma out_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (Quotient.mk (linkSetoid G) e).out ∈ G.edgeSet :=
  Linked.mem_edgeSet
    (Linked.symm (Quotient.exact
      (Quotient.out_eq (Quotient.mk (linkSetoid G) e)))) he

variable (G) in
/-- **The canonical piece through an edge** — a function of the edge's
linkage class only. -/
noncomputable def pieceOf (e : Sym2 V) (he : e ∈ G.edgeSet) : Piece G :=
  classPiece G ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩

variable (G) in
lemma mem_pieceOf {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (pieceOf G e he).walk.edges :=
  (pieceOf G e he).piece.mem_of_linked (classPiece_mem G _)
    (Quotient.exact (Quotient.out_eq (Quotient.mk (linkSetoid G) e)))

variable (G) in
/-- Class-constancy of the piece choice: linked edges get THE SAME
piece (not merely pieces with equal edge sets). -/
lemma pieceOf_eq_of_linked {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (hf : f ∈ G.edgeSet) (h : Linked G e f) :
    pieceOf G e he = pieceOf G f hf := by
  unfold pieceOf
  congr 1
  exact Subtype.ext (Quotient.sound h)

variable (G) in
/-- Every edge of `pieceOf e` has the same canonical piece. -/
lemma pieceOf_eq_of_mem {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (hf : f ∈ G.edgeSet) (hmem : f ∈ (pieceOf G e he).walk.edges) :
    pieceOf G f hf = pieceOf G e he :=
  pieceOf_eq_of_linked G hf he
    ((pieceOf G e he).piece.linked_of_mem hmem (mem_pieceOf G he))

variable (G) in
/-- **Ports of the canonical piece** (`eq_first_or_last` transported):
a junction-incident edge is the first or last edge of its canonical
piece, with the junction at the corresponding end. -/
lemma pieceOf_port {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V}
    (hv : v ∈ e) (hdv : G.degree v ≠ 2) :
    (v = (pieceOf G e he).a ∧ e = (pieceOf G e he).firstEdge) ∨
    (v = (pieceOf G e he).b ∧ e = (pieceOf G e he).lastEdge) :=
  (pieceOf G e he).piece.eq_first_or_last (mem_pieceOf G he) hv hdv

/-! ### M-nodes and members -/

variable (G) in
/-- **The M-nodes** of the contraction multigraph: group sites `(v, k)`
(junction groups at degree ≥ 3, singleton sites at degree ≤ 2 — with
the group index bounded to keep the type FINITE, `glueIx_lt`) ⊕ one
middle node per linkage class. -/
abbrev MNode : Type _ :=
  (V × Fin (Fintype.card V + 1)) ⊕ Quotient (linkSetoid G)

variable (G) in
/-- The group site of the edge `f` at the vertex `v`. -/
noncomputable def nodeAt (v : V) (f : Sym2 V) : MNode G :=
  Sum.inl (v, ⟨glueIx G v f, glueIx_lt v f⟩)

lemma nodeAt_eq_inl_iff {v' v : V} {f : Sym2 V}
    {k : Fin (Fintype.card V + 1)} :
    nodeAt G v' f = Sum.inl (v, k) ↔ v' = v ∧ glueIx G v' f = k.1 := by
  simp [nodeAt, Fin.ext_iff]

lemma nodeAt_ne_inr {v : V} {f : Sym2 V}
    {q : Quotient (linkSetoid G)} : nodeAt G v f ≠ Sum.inr q := by
  simp [nodeAt]

namespace Piece

/-- The M-node at a piece's start (its first-edge group site). -/
noncomputable def startNode (P : Piece G) : MNode G :=
  nodeAt G P.a P.firstEdge

/-- The M-node at a piece's end (its last-edge group site). -/
noncomputable def endNode (P : Piece G) : MNode G :=
  nodeAt G P.b P.lastEdge

lemma startNode_ne_endNode (P : Piece G) (hab : P.a ≠ P.b) :
    P.startNode ≠ P.endNode := by
  unfold startNode endNode nodeAt
  simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq, not_and]
  intro h
  exact absurd h hab

end Piece

variable (G) in
/-- **Member validity**: `inl q` (the whole chain, or its L-half when
the piece has ≥ 3 edges) exists for every CHAIN class; `inr q` (the
R-half) additionally needs ≥ 3 edges.  Pure cycles contribute no
members — their edges are colored by `exists_cycle_distance2`, not
through M. -/
def MemberSpec : EdgeClass G ⊕ EdgeClass G → Prop
  | Sum.inl q => ¬(classPiece G q).IsCycle
  | Sum.inr q => ¬(classPiece G q).IsCycle ∧
      3 ≤ (classPiece G q).walk.length

variable (G) in
/-- **The members** — the M-edges of the contraction multigraph. -/
abbrev Member : Type _ := {m : EdgeClass G ⊕ EdgeClass G // MemberSpec G m}

variable (G) in
/-- The linkage class of a member. -/
def Member.cls : Member G → EdgeClass G
  | ⟨Sum.inl q, _⟩ => q
  | ⟨Sum.inr q, _⟩ => q

variable (G) in
/-- **The M-family** (the `t : ι → Sym2 N` of `shannon_six_indexed`):
the whole-chain member joins the two end sites; the L/R halves of a
long chain join their end site to the class's middle node. -/
noncomputable def mfam : Member G → Sym2 (MNode G)
  | ⟨Sum.inl q, _⟩ =>
      if 3 ≤ (classPiece G q).walk.length
      then s((classPiece G q).startNode, Sum.inr q.1)
      else s((classPiece G q).startNode, (classPiece G q).endNode)
  | ⟨Sum.inr q, _⟩ => s(Sum.inr q.1, (classPiece G q).endNode)

variable (G) in
/-- **Looplessness** of the M-family (`hloop` of
`shannon_six_indexed`): half members join a site to a middle node;
whole members join the two end sites of a chain with < 3 edges, whose
ends are DISTINCT vertices (a closed trail has ≥ 3 edges). -/
lemma mfam_not_isDiag (m : Member G) : ¬(mfam G m).IsDiag := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3, Sym2.mk_isDiag_iff]
      exact fun h => nodeAt_ne_inr h
    · simp only [mfam, if_neg h3, Sym2.mk_isDiag_iff]
      exact (classPiece G q).startNode_ne_endNode
        ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
  · simp only [mfam, Sym2.mk_isDiag_iff]
    exact fun h => nodeAt_ne_inr h.symm

/-! ### The port-edge injection and the per-node count bound -/

variable (G) in
open Classical in
/-- The port edge of a member at a target node: the member's first or
last edge, picked toward the node (only meaningful when the node lies
on the member — see `mfam_count_junction`). -/
noncomputable def portEdge (nd : MNode G) : Member G → Sym2 V
  | ⟨Sum.inl q, _⟩ =>
      if (classPiece G q).startNode = nd then (classPiece G q).firstEdge
      else (classPiece G q).lastEdge
  | ⟨Sum.inr q, _⟩ => (classPiece G q).lastEdge

variable (G) in
lemma portEdge_mem (nd : MNode G) (m : Member G) :
    portEdge G nd m ∈ (classPiece G (Member.cls G m)).walk.edges := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · simp only [portEdge, Member.cls]
    split_ifs
    · exact (classPiece G q).firstEdge_mem
    · exact (classPiece G q).lastEdge_mem
  · simp only [portEdge, Member.cls]
    exact (classPiece G q).lastEdge_mem

variable (G) in
/-- A whole/L member through a group site has it as its START node, and
its port edge there is the FIRST edge — unless the site is the end node
of a short chain, where the port edge is the LAST edge.  Packaged as:
the port edge is incident to `v` inside group `k`. -/
lemma portEdge_spec {v : V} {k : Fin (Fintype.card V + 1)}
    {m : Member G} (hnd : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    portEdge G (Sum.inl (v, k)) m ∈ G.incidenceFinset v ∧
      glueIx G v (portEdge G (Sum.inl (v, k)) m) = k.1 := by
  obtain ⟨mv, hspec⟩ := m
  have hinc : ∀ (P : Piece G), P.startNode = Sum.inl (v, k) →
      P.firstEdge ∈ G.incidenceFinset v ∧
        glueIx G v P.firstEdge = k.1 := by
    intro P h
    obtain ⟨hva, hix⟩ := nodeAt_eq_inl_iff.mp h
    subst hva
    refine ⟨mem_incFinset.mpr ⟨P.walk.edges_subset_edgeSet P.firstEdge_mem,
      Sym2.mem_mk_left _ _⟩, hix⟩
  have hinc' : ∀ (P : Piece G), P.endNode = Sum.inl (v, k) →
      P.lastEdge ∈ G.incidenceFinset v ∧
        glueIx G v P.lastEdge = k.1 := by
    intro P h
    obtain ⟨hva, hix⟩ := nodeAt_eq_inl_iff.mp h
    subst hva
    refine ⟨mem_incFinset.mpr ⟨P.walk.edges_subset_edgeSet P.lastEdge_mem,
      Sym2.mem_mk_right _ _⟩, hix⟩
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3] at hnd
      have hs : (classPiece G q).startNode = Sum.inl (v, k) := by
        rcases Sym2.mem_iff.mp hnd with h | h
        · exact h.symm
        · exact absurd h.symm (by simp)
      simp only [portEdge, if_pos hs]
      exact hinc _ hs
    · simp only [mfam, if_neg h3] at hnd
      rcases Sym2.mem_iff.mp hnd with h | h
      · simp only [portEdge, if_pos h.symm]
        exact hinc _ h.symm
      · have hne : (classPiece G q).startNode ≠
            (classPiece G q).endNode :=
          (classPiece G q).startNode_ne_endNode
            ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
        have hcond : ¬((classPiece G q).startNode = Sum.inl (v, k)) := by
          intro hc
          exact hne (hc.trans h)
        simp only [portEdge, if_neg hcond]
        exact hinc' _ h.symm
  · simp only [mfam] at hnd
    have hs : (classPiece G q).endNode = Sum.inl (v, k) := by
      rcases Sym2.mem_iff.mp hnd with h | h
      · exact absurd h.symm (by simp)
      · exact h.symm
    simp only [portEdge]
    exact hinc' _ hs

variable (G) in
/-- The L-half's port edge at a site it contains is the FIRST edge
(when the piece is long, its middle node is not a site). -/
lemma portEdge_inl_of_three_le {v : V} {k : Fin (Fintype.card V + 1)}
    {q : EdgeClass G} {h : MemberSpec G (Sum.inl q)}
    (h3 : 3 ≤ (classPiece G q).walk.length)
    (hnd : (Sum.inl (v, k) : MNode G) ∈ mfam G ⟨Sum.inl q, h⟩) :
    portEdge G (Sum.inl (v, k)) ⟨Sum.inl q, h⟩ =
      (classPiece G q).firstEdge := by
  simp only [mfam, if_pos h3] at hnd
  have hs : (classPiece G q).startNode = Sum.inl (v, k) := by
    rcases Sym2.mem_iff.mp hnd with h' | h'
    · exact h'.symm
    · exact absurd h'.symm (by simp)
  simp only [portEdge, if_pos hs]

variable (G) in
/-- **Port-member uniqueness** (the injection behind the site count,
and the rainbow input's uniqueness half): two members through a common
group site with THE SAME port edge there are equal.  (They share a
linkage class via the port edge; within a class, the L and R halves
have distinct ports by `edges_nodup`.) -/
theorem port_member_unique {v : V} {k : Fin (Fintype.card V + 1)}
    {m m' : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m)
    (hm' : (Sum.inl (v, k) : MNode G) ∈ mfam G m')
    (heq : portEdge G (Sum.inl (v, k)) m =
      portEdge G (Sum.inl (v, k)) m') : m = m' := by
  -- the two members share a linkage class
  have hc : Member.cls G m = Member.cls G m' := by
    apply Subtype.ext
    rw [← classPiece_class_eq G (portEdge_mem G _ m),
      ← classPiece_class_eq G (portEdge_mem G _ m'), heq]
  -- same constructor ⇒ equal; mixed ⇒ first = last edge, absurd
  obtain ⟨mv, hs⟩ := m
  obtain ⟨mv', hs'⟩ := m'
  apply Subtype.ext
  rcases mv with q | q <;> rcases mv' with q' | q'
  · simp only [Member.cls] at hc
    subst hc
    rfl
  · -- L/whole vs R: the R-half forces length ≥ 3, whence the
    -- L port is the first edge and the R port the last
    exfalso
    simp only [Member.cls] at hc
    subst hc
    have h3 : 3 ≤ (classPiece G q).walk.length := hs'.2
    rw [portEdge_inl_of_three_le G h3 hm] at heq
    simp only [portEdge] at heq
    exact (classPiece G q).firstEdge_ne_lastEdge (by omega) heq
  · exfalso
    simp only [Member.cls] at hc
    subst hc
    have h3 : 3 ≤ (classPiece G q).walk.length := hs.2
    rw [portEdge_inl_of_three_le G h3 hm'] at heq
    simp only [portEdge] at heq
    exact (classPiece G q).firstEdge_ne_lastEdge (by omega) heq.symm
  · simp only [Member.cls] at hc
    subst hc
    rfl

variable (G) in
/-- **The junction-site count** (`hdeg` at group sites): the members at
a site `(v, k)` inject via their port edges into the ≤ 4 edges of the
group `k` at `v`. -/
lemma mfam_count_junction [Fintype (Member G)] [DecidableEq (MNode G)]
    (v : V) (k : Fin (Fintype.card V + 1)) :
    #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inl (v, k) : MNode G) ∈ mfam G m} ≤ 4 := by
  classical
  calc #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inl (v, k) : MNode G) ∈ mfam G m}
      ≤ #{f ∈ G.incidenceFinset v | glueIx G v f = k.1} := by
        apply card_le_card_of_injOn (portEdge G (Sum.inl (v, k)))
        · intro m hm
          rw [mem_coe, mem_filter] at hm
          obtain ⟨hf, hix⟩ := portEdge_spec G hm.2
          rw [mem_coe, mem_filter]
          exact ⟨hf, hix⟩
        · intro m hm m' hm' heq
          rw [mem_coe, mem_filter] at hm hm'
          exact port_member_unique G hm.2 hm'.2 heq
    _ ≤ 4 := glueIx_fiber_le v k.1

variable (G) in
/-- Only the two halves of a class touch its middle node. -/
lemma cls_eq_of_inr_mem {q₀ : Quotient (linkSetoid G)} {m : Member G}
    (h : (Sum.inr q₀ : MNode G) ∈ mfam G m) : (Member.cls G m).1 = q₀ := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3] at h
      rcases Sym2.mem_iff.mp h with h' | h'
      · exact absurd h'.symm nodeAt_ne_inr
      · simp only [Member.cls]
        exact (Sum.inr.inj h').symm
    · simp only [mfam, if_neg h3] at h
      rcases Sym2.mem_iff.mp h with h' | h' <;>
        exact absurd h'.symm nodeAt_ne_inr
  · simp only [mfam] at h
    rcases Sym2.mem_iff.mp h with h' | h'
    · simp only [Member.cls]
      exact (Sum.inr.inj h').symm
    · exact absurd h'.symm nodeAt_ne_inr

variable (G) in
/-- **The middle-node count** (`hdeg` at middle nodes): at most the two
halves of the class — inject by the constructor tag. -/
lemma mfam_count_middle [Fintype (Member G)] [DecidableEq (MNode G)]
    (q₀ : Quotient (linkSetoid G)) :
    #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inr q₀ : MNode G) ∈ mfam G m} ≤ 4 := by
  classical
  calc #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inr q₀ : MNode G) ∈ mfam G m}
      ≤ #(Finset.univ : Finset Bool) := by
        apply card_le_card_of_injOn (fun m => m.1.isLeft)
        · intro m _
          exact mem_coe.mpr (mem_univ _)
        · intro m hm m' hm' hleft
          rw [mem_coe, mem_filter] at hm hm'
          have h1 := cls_eq_of_inr_mem G hm.2
          have h2 := cls_eq_of_inr_mem G hm'.2
          have hc : Member.cls G m = Member.cls G m' :=
            Subtype.ext (h1.trans h2.symm)
          obtain ⟨mv, hs⟩ := m
          obtain ⟨mv', hs'⟩ := m'
          apply Subtype.ext
          rcases mv with q | q <;> rcases mv' with q' | q' <;>
            simp only [Member.cls] at hc <;>
            simp only [Sum.isLeft] at hleft
          · subst hc; rfl
          · exact absurd hleft (by simp)
          · exact absurd hleft (by simp)
          · subst hc; rfl
    _ ≤ 4 := by
        rw [Finset.card_univ, Fintype.card_bool]
        omega

/-! ### Port coverage: every junction-incident edge is a member's port
(pretest R-E — the rainbow input's existence half; uniqueness is
`port_member_unique`) -/

variable (G) in
/-- The whole/L member contains the start site, with the first edge as
its port there. -/
lemma member_port_start {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle) :
    (classPiece G q).startNode ∈ mfam G ⟨Sum.inl q, hnc⟩ ∧
    portEdge G ((classPiece G q).startNode) ⟨Sum.inl q, hnc⟩ =
      (classPiece G q).firstEdge := by
  constructor
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3]
      exact Sym2.mem_mk_left _ _
    · simp only [mfam, if_neg h3]
      exact Sym2.mem_mk_left _ _
  · simp only [portEdge]
    exact if_pos trivial

variable (G) in
/-- On a long chain, the R-half contains the end site, with the last
edge as its port there. -/
lemma member_port_end_long {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    (classPiece G q).endNode ∈ mfam G ⟨Sum.inr q, ⟨hnc, h3⟩⟩ ∧
    portEdge G ((classPiece G q).endNode) ⟨Sum.inr q, ⟨hnc, h3⟩⟩ =
      (classPiece G q).lastEdge := by
  constructor
  · simp only [mfam]
    exact Sym2.mem_mk_right _ _
  · simp only [portEdge]

variable (G) in
/-- On a short chain, the whole member contains the end site, with the
last edge as its port there (the start site differs from the end site,
so the port selector picks the last edge). -/
lemma member_port_end_short {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    (classPiece G q).endNode ∈ mfam G ⟨Sum.inl q, hnc⟩ ∧
    portEdge G ((classPiece G q).endNode) ⟨Sum.inl q, hnc⟩ =
      (classPiece G q).lastEdge := by
  have hne := (classPiece G q).startNode_ne_endNode
    ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
  constructor
  · simp only [mfam, if_neg h3]
    exact Sym2.mem_mk_right _ _
  · simp only [portEdge]
    rw [if_neg hne]

variable (G) in
/-- **Port coverage** (pretest R-E): every edge at a vertex of
degree ≠ 2 is the port edge of a member through the corresponding
group site.  With `port_member_unique`, "the member of a port" is
well-defined — the future port coloring gives every junction-incident
edge its member's Shannon color, which is the `rainbow` field's
input. -/
theorem exists_port_member {v : V} (hdv : G.degree v ≠ 2) {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hv : v ∈ e) :
    ∃ m : Member G, nodeAt G v e ∈ mfam G m ∧
      portEdge G (nodeAt G v e) m = e := by
  have hnc : ¬(pieceOf G e he).IsCycle := by
    intro hcyc
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    have hmem : s(v, w) ∈ (pieceOf G e he).walk.edges := by
      rw [← hw]
      exact mem_pieceOf G he
    exact hdv (((pieceOf G e he).cycle_spec hcyc).2 v
      ((pieceOf G e he).walk.fst_mem_support_of_mem_edges hmem))
  rcases pieceOf_port G he hv hdv with ⟨hva, hef⟩ | ⟨hvb, hel⟩
  · -- v is the start: the whole/L member through the start site
    obtain ⟨hmem, hport⟩ := member_port_start G
      (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc
    have hnd : nodeAt G v e = (pieceOf G e he).startNode :=
      congrArg₂ (nodeAt G) hva hef
    refine ⟨⟨Sum.inl ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
      hnc⟩, ?_, ?_⟩
    · rw [hnd]
      exact hmem
    · rw [hnd]
      exact hport.trans hef.symm
  · -- v is the end: the R-half (long) or the whole member (short)
    have hnd : nodeAt G v e = (pieceOf G e he).endNode :=
      congrArg₂ (nodeAt G) hvb hel
    by_cases h3 : 3 ≤ (pieceOf G e he).walk.length
    · obtain ⟨hmem, hport⟩ := member_port_end_long G
        (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc h3
      refine ⟨⟨Sum.inr ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
        ⟨hnc, h3⟩⟩, ?_, ?_⟩
      · rw [hnd]
        exact hmem
      · rw [hnd]
        exact hport.trans hel.symm
    · obtain ⟨hmem, hport⟩ := member_port_end_short G
        (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc h3
      refine ⟨⟨Sum.inl ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
        hnc⟩, ?_, ?_⟩
      · rw [hnd]
        exact hmem
      · rw [hnd]
        exact hport.trans hel.symm

/-! ### The Shannon member coloring -/

/-- **The member coloring exists** (`shannon_six_indexed` on the real
M-family of an arbitrary graph): a 6-coloring of the members, distinct
whenever two members share an M-node.  Specialized downstream: at a
group site this is the rainbow input (distinct port colors within a
group), at a middle node the l = 3 port distinctness `isFill_exists`
needs.  All finiteness/decidability is supplied classically — the
linkage quotient is finite but not constructively enumerable here. -/
theorem exists_member_coloring (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ col : Member G → Fin 6, ∀ m m' : Member G, m ≠ m' →
      ∀ a : MNode G, a ∈ mfam G m → a ∈ mfam G m' → col m ≠ col m' := by
  classical
  haveI : Fintype (Quotient (linkSetoid G)) := Fintype.ofFinite _
  haveI : Fintype (MNode G) := Fintype.ofFinite _
  haveI : Fintype (Member G) := Fintype.ofFinite _
  refine shannon_six_indexed (mfam G) (mfam_not_isDiag G) ?_
  intro a
  rcases a with ⟨v, k⟩ | q
  · exact mfam_count_junction G v k
  · exact mfam_count_middle G q

/-! ### Honest scope note

Banked here: the per-vertex grouping facts (`glueIx`), the piece choice
per linkage class (`classPiece`/`pieceOf`, class-constant), the port
fact transported (`pieceOf_port`), the M-node/member family with
looplessness and the per-node ≤ 4 bound, and the Shannon member
coloring `exists_member_coloring` — step 2 of the C6L3/C7L3 handoff.
NOT yet formalized (steps 3–5, still owed): the port coloring and its
`satSet` agreement, the fills (`isFill_exists` instantiation), the
pure-cycle coloring hookup, the global coloring and the
`IsGlueColoring` bundle.  `maj_le_six` remains `proof_wanted`. -/

end SMaj
