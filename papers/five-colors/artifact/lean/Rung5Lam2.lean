/-
# RUNG-5 Λ-LADDER, rung Λ2 REINFORCEMENT (rung5_lam2_kempe) — the same
# VERBATIM statement as rung5_lam2, with a DIFFERENT DIET: the
# kernel-proved SMKernel EdgeColoring machinery is VENDORED in this
# project (SMKernel/EdgeColoring/*, byte-identical from canonical — every
# named lemma below is PROVED, zero sorries in that tree).  EXPLORATORY.
# Λ2 is the campaign's one shared prerequisite (both Λ4 partials name it).

Base modules (do not modify either):
- Maj5Base.lean = the frozen maj5 artifact (defs `mdeg`, `IsMulticoloring`
  used by the target; its single `maj_le_five` sorry is out of scope).
- SMKernel/ = the SimpleGraph edge-coloring kit, ALL PROVED:
  `SimpleGraph.IsProperEdgeColoring`, `presentColors`/`missingColors` (+
  `card_presentColors_of_isProperEdgeColoring`,
  `card_missingColors_of_isProperEdgeColoring`,
  `mem_presentColors_iff_exists_adj`, `degree_deleteEdges_of_adj`),
  `kempeGraph` (+ `degree_kempeGraph_le_two`,
  `card_filter_color_neighbors_le_one`, `neighborFinset_kempeGraph_eq`),
  `kempeSwapColor`/`kempeSwap`/`IsKempeClosed` (+
  `IsProperEdgeColoring.kempeSwap_of_isKempeClosed`,
  `kempeSwap_apply_eq_of_not_mem`,
  `kempeSwap_apply_eq_kempeSwapColor_of_mem`,
  `presentColors_kempeSwap_of_mem/of_not_mem`,
  `missingColors_kempeSwap_of_mem/of_not_mem`),
  `reachFinset` (+ `isKempeClosed_reachFinset`, `reachFinset_eq_of_mem`,
  `mem_reachFinset`, `self_mem_reachFinset`),
  `EdgeColorable` (+ `EdgeColorable.of_missing_inter` — the one-edge
  extension when the two ends share a missing color),
  `disjoint_missingColors_of_not_edgeColorable` (Lemma A),
  `reachable_kempeGraph_of_missing` (Lemma B linkage),
  `not_reachable_kempeGraph_of_missing_of_ne` (separation).

ROUTE (classical Vizing at Δ ≤ 4 with 5 = Δ + 1 colors, run on the
SimpleGraph side and transported):
1. `hsimple` makes the multigraph SIMPLE: define (privately) the graph
   `G_mult` on α with `Adj a b := 0 < mult a b` (symmetric by `hsymm`,
   loopless by `hloop`, decidable); `mdeg = degree`, so Δ(G_mult) ≤ 4.
2. Prove (privately) `G_mult.EdgeColorable 5` by strong induction on the
   edge count: delete an edge s(u,v) (`deleteEdges`), color the remainder
   (IH), and extend.  If the deletion-coloring misses a common color at
   u and v, extend directly — this is EXACTLY the vendored
   `EdgeColorable.of_missing_inter` (its statement is for a coloring of
   `G.deleteEdges {s(u,v)}`, which is the IH's shape).  Otherwise run the
   Vizing fan at u: every vertex misses ≥ 1 of the 5 colors (degree ≤ 4;
   vendored `card_missingColors_of_isProperEdgeColoring` +
   `degree_deleteEdges_of_adj` give |φ̄| = 5 − d + 1 ≥ 2 at the endpoints
   — NOTE the slack: at Δ ≤ 4 with 5 colors both endpoints miss ≥ 2, and
   fan rotations shorten dramatically); when the fan blocks on a repeated
   color, flip the (α,β)-Kempe chain through the blocking vertex:
   `kempeSwap` on `reachFinset` (closure = `isKempeClosed_reachFinset`;
   properness = `IsProperEdgeColoring.kempeSwap_of_isKempeClosed`;
   palette bookkeeping = the `missingColors_kempeSwap_*` laws; the chain
   cannot join both fan ends = `not_reachable_kempeGraph_of_missing_of_ne`
   / Lemma B — this trio is exactly what the kit was built for).
3. Transport back: from `f : Sym2 α → Fin 5` proper on `G_mult`, define
   `φ a b := if 0 < mult a b then {f s(a, b)} else ∅`; `IsMulticoloring`
   follows from properness + `hsimple` (card 1 = mult when positive,
   disjointness at a common vertex = properness).

TASK: fill the sorry in THIS file only.  Do not change any definition or
statement (in this file or the base modules).  No axioms beyond
propext/Classical.choice/Quot.sound.  Private helper lemmas strongly
encouraged (the fan rotation is the natural standalone piece — the Kempe
half is already proved for you).  If the theorem resists, return with
the sorry intact, your proved private lemmas, and a precise gap
diagnosis — do not weaken or restate.
-/
import Maj5Base
import SMKernel.EdgeColoring.Linkage

set_option maxRecDepth 8000

namespace SMaj.Lam2

-- semantics pins (same as the sibling rung5_lam2): one edge, one color
example : IsMulticoloring (C := Fin 5)
    (fun i j : Fin 2 => if i ≠ j then 1 else 0)
    (fun i j => if i ≠ j then {0} else ∅) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
-- the vendored kit is live: K₄'s matching coloring is proper (kernel demo)
example : (⊤ : SimpleGraph (Fin 4)).IsProperEdgeColoring
    (fun e => if e = s(0, 1) ∨ e = s(2, 3) then (0 : Fin 5)
      else if e = s(0, 2) ∨ e = s(1, 3) then 1 else 2) := by decide

/-! ## Λ2 proof (Fable prover lane, 2026-07-11)

Route (payload header, realized): Vizing at Δ ≤ 4 with 5 colors on the
SimpleGraph side, transported to the matrix encoding.  The Δ ≤ 4 slack
collapses the general fan to SIX terminal cases: with x y₀ the uncolored
edge, y₁ (color β₀ ∈ φ̄(y₀)) and y₂ (color β₁ ∈ φ̄(y₁)) the only two fan
steps ever needed, the third fan color β₂ ∈ φ̄(y₂) satisfies
  β₂ ∈ φ̄(x)   → 2-step rotation;
  β₂ ∈ φ̄(y₀)  → (α,β₂)-Kempe swap through y₂ + rotation (kit Lemma B +
                 separation give x, y₀ off the chain);
  β₂ ∈ φ̄(y₁)  → chain flip: swap reach(y₂); if x lands in the chain,
                 β₂ transfers to φ̄(x) and a 1-step rotation finishes
                 (x, y₁, y₂ cannot all lie on one (α,β₂)-chain — three
                 degree-≤1 vertices in a Δ ≤ 2 component);
  β₂ fresh    → pure counting: φ̄(y₀) ⊆ present(x) (Lemma A), but
                 |present(x)| ≤ 3 and β₁, β₂ ∈ present(x) ∖ φ̄(y₀) leave
                 |φ̄(y₀)| ≤ 1 < 2.  (β₂ = β₀ is inside the φ̄(y₀) case;
                 β₂ = β₁ is impossible — β₁ is present at y₂.)
The two β₁-cases are the same tree one level up.  Everything Kempe is
the vendored kit; the two private component lemmas of Linkage.lean are
transplanted verbatim below (they are `private` there, same pin). -/

open SimpleGraph

section KitTransplant

/- Transplanted verbatim from SMKernel/EdgeColoring/Linkage.lean (private
there; same toolchain pin, same simp environment — Aristotle-returned,
audited 2026-07-11). -/

/-- In a proper coloring, a vertex missing one of the two Kempe colors has
Kempe-degree ≤ 1 (only its single other-color edge can survive). -/
private theorem degree_kempeGraph_le_one_of_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {n : ℕ} {c : Sym2 V → Fin n} {u : V} {α β : Fin n}
    (hc : H.IsProperEdgeColoring c)
    (hα : α ∈ H.missingColors c u ∨ β ∈ H.missingColors c u) :
    (H.kempeGraph c α β).degree u ≤ 1 := by
  cases' hα with hα hα;
  · have h_subset : (H.kempeGraph c α β).neighborFinset u ⊆ Finset.filter (fun w => c s(u, w) = β) (H.neighborFinset u) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.kempeGraph ];
      intro v hv hv'; specialize hα; simp_all +decide [ SimpleGraph.mem_missingColors ] ;
    exact le_trans ( Finset.card_le_card h_subset ) ( SimpleGraph.card_filter_color_neighbors_le_one H hc u β );
  · have hB_empty : Finset.filter (fun w => c s(u, w) = β) (H.neighborFinset u) = ∅ := by
      simp_all +decide [ Finset.ext_iff, SimpleGraph.mem_missingColors ];
    rw [ SimpleGraph.degree, SimpleGraph.neighborFinset_kempeGraph_eq ];
    rw [ hB_empty, Finset.union_empty ] ; exact SimpleGraph.card_filter_color_neighbors_le_one H hc u α

/-- Pure graph fact: in a finite graph with maximum degree ≤ 2, a single
connected component cannot contain three distinct vertices each of degree
≤ 1 (a path has only two ends, a cycle has none). -/
private theorem reachable_three_deg_le_one_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x ≤ 2)
    {a b w : V} (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (hda : H.degree a ≤ 1) (hdb : H.degree b ≤ 1) (hdw : H.degree w ≤ 1)
    (hrab : H.Reachable a b) (hraw : H.Reachable a w) :
    False := by
  set K := {x : V | H.Reachable a x} with hK_def
  have hK_finite : K.Finite := by
    exact Set.toFinite K;
  set H' := H.induce K with hH'_def;
  have hH'_connected : H'.Connected := by
    rw [ SimpleGraph.connected_iff_exists_forall_reachable ];
    refine' ⟨ ⟨ a, _ ⟩, _ ⟩;
    exact SimpleGraph.Reachable.refl a;
    have h_walk : ∀ {u v : V}, H.Reachable u v → ∀ {hu : u ∈ K} {hv : v ∈ K}, H'.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v huv hu hv; induction huv;
      induction' ‹_› with u v huv ih;
      · exact SimpleGraph.Reachable.refl _;
      · rename_i h₁ h₂ h₃;
        have h_walk : H.Reachable a huv := by
          exact hu.trans ( SimpleGraph.Adj.reachable h₁ );
        exact SimpleGraph.Reachable.trans ( SimpleGraph.Adj.reachable <| by aesop ) ( h₃ );
    grind;
  have hH'_degree : ∀ x : K, H'.degree x = H.degree x := by
    intro x; rw [ SimpleGraph.degree, SimpleGraph.degree ] ;
    refine' Finset.card_bij ( fun y hy => y ) _ _ _ <;> simp +decide [ SimpleGraph.neighborFinset ];
    · exact fun y hy hxy => hxy;
    · exact fun y hy => ⟨ x.2.trans ( SimpleGraph.Adj.reachable hy ), hy ⟩;
  have h_handshake : ∑ x : K, H'.degree x = 2 * H'.edgeFinset.card := by
    convert SimpleGraph.sum_degrees_eq_twice_card_edges H' using 1
  have h_connectivity : Fintype.card K ≤ H'.edgeFinset.card + 1 := by
    convert hH'_connected.card_vert_le_card_edgeSet_add_one using 1;
    · rw [ Nat.card_eq_fintype_card ];
    · simp +decide [ SimpleGraph.edgeFinset ];
  have h_sum_bound : ∑ x : K, H'.degree x ≤ 2 * Fintype.card K - 3 := by
    have h_sum_bound : ∑ x : K, H'.degree x ≤ ∑ x : K, 2 - ∑ x ∈ ({⟨a, by
      exact SimpleGraph.Reachable.refl a⟩, ⟨b, by
      exact hrab⟩, ⟨w, by
      exact hraw⟩} : Finset K), (2 - H'.degree x) := by
      all_goals generalize_proofs at *;
      refine' le_tsub_of_add_le_right _;
      rw [ ← Finset.sum_sdiff ( Finset.subset_univ { ⟨ a, by assumption ⟩, ⟨ b, by assumption ⟩, ⟨ w, by assumption ⟩ } ) ];
      rw [ ← Finset.sum_sdiff ( Finset.subset_univ { ⟨ a, by assumption ⟩, ⟨ b, by assumption ⟩, ⟨ w, by assumption ⟩ } ) ];
      rw [ add_assoc ];
      exact add_le_add ( Finset.sum_le_sum fun x hx => hH'_degree x ▸ hdeg _ ) ( by rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by rw [ add_tsub_cancel_of_le ] ; exact hH'_degree x ▸ hdeg _ )
    generalize_proofs at *;
    simp_all +decide [ mul_comm ];
    exact h_sum_bound.trans ( Nat.sub_le_sub_left ( by omega ) _ );
  rw [ Nat.le_sub_iff_add_le ] at h_sum_bound;
  · linarith;
  · rw [ Fintype.card_subtype ];
    exact le_trans ( by decide ) ( Nat.mul_le_mul_left 2 ( Finset.two_lt_card.mpr ⟨ a, by aesop_cat, b, by aesop_cat, w, by aesop_cat ⟩ ) )

end KitTransplant

/-! ### The rotation step: recoloring one edge to a both-ends-missing color -/

section Recolor

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {H : SimpleGraph W} [DecidableRel H.Adj]

/-- Recolor the single edge `e` to `γ`. -/
private def recolor {n : ℕ} (c : Sym2 W → Fin n) (e : Sym2 W) (γ : Fin n) :
    Sym2 W → Fin n := fun f => if f = e then γ else c f

private lemma recolor_apply_self {n : ℕ} (c : Sym2 W → Fin n) (e : Sym2 W)
    (γ : Fin n) : recolor c e γ e = γ := if_pos rfl

private lemma recolor_apply_of_ne {n : ℕ} (c : Sym2 W → Fin n) {e f : Sym2 W}
    (γ : Fin n) (h : f ≠ e) : recolor c e γ f = c f := if_neg h

/-- An edge incident to `x` toward a neighbor is in the incidence finset. -/
private lemma mk_mem_incidenceFinset {x w : W} (h : H.Adj x w) :
    s(x, w) ∈ H.incidenceFinset x :=
  (H.mem_incidenceFinset x _).mpr ⟨H.mem_edgeSet.mpr h, Sym2.mem_mk_left _ _⟩

/-- Recoloring one edge to a color missing at both its ends preserves
properness. -/
private lemma isProperEdgeColoring_recolor {n : ℕ} {c : Sym2 W → Fin n}
    (hc : H.IsProperEdgeColoring c) {x y : W} (hxy : H.Adj x y) {γ : Fin n}
    (hγx : γ ∈ H.missingColors c x) (hγy : γ ∈ H.missingColors c y) :
    H.IsProperEdgeColoring (recolor c s(x, y) γ) := by
  intro u v w huv huw hvw
  by_cases h1 : s(u, v) = s(x, y) <;> by_cases h2 : s(u, w) = s(x, y)
  · exact absurd (h1.trans h2.symm) (fun h => hvw (Sym2.congr_right.mp h))
  · rw [recolor, if_pos h1, recolor, if_neg h2]
    -- γ is missing at both x and y; u ∈ {x, y}, and s(u,w) is incident to u
    have hu : u = x ∨ u = y := by
      rcases Sym2.eq_iff.mp h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hmem : s(u, w) ∈ H.incidenceFinset u := mk_mem_incidenceFinset huw
    rcases hu with rfl | rfl
    · exact fun h => ((H.mem_missingColors).mp hγx _ hmem) h.symm
    · exact fun h => ((H.mem_missingColors).mp hγy _ hmem) h.symm
  · rw [recolor, if_neg h1, recolor, if_pos h2]
    have hu : u = x ∨ u = y := by
      rcases Sym2.eq_iff.mp h2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hmem : s(u, v) ∈ H.incidenceFinset u := mk_mem_incidenceFinset huv
    rcases hu with rfl | rfl
    · exact fun h => ((H.mem_missingColors).mp hγx _ hmem) h
    · exact fun h => ((H.mem_missingColors).mp hγy _ hmem) h
  · rw [recolor, if_neg h1, recolor, if_neg h2]
    exact hc huv huw hvw

/-- Vertices off the recolored edge keep their missing sets. -/
private lemma missingColors_recolor_of_not_mem {n : ℕ} {c : Sym2 W → Fin n}
    {e : Sym2 W} {γ : Fin n} {v : W} (hv : v ∉ e) :
    H.missingColors (recolor c e γ) v = H.missingColors c v := by
  unfold SimpleGraph.missingColors SimpleGraph.presentColors
  congr 1
  apply Finset.image_congr
  intro f hf
  rw [Finset.mem_coe, H.mem_incidenceFinset] at hf
  have hne : f ≠ e := by
    intro h
    exact hv (h ▸ hf.2)
  exact recolor_apply_of_ne c γ hne

/-- After recoloring `s(x,y)` away from its old color `β`, `β` becomes
missing at `x` (properness made `s(x,y)` its unique `β`-edge at `x`). -/
private lemma old_color_missing_recolor {n : ℕ} {c : Sym2 W → Fin n}
    (hc : H.IsProperEdgeColoring c) {x y : W} (hxy : H.Adj x y) {γ : Fin n}
    (hγ : γ ≠ c s(x, y)) :
    c s(x, y) ∈ H.missingColors (recolor c s(x, y) γ) x := by
  rw [H.mem_missingColors]
  intro f hf
  by_cases h : f = s(x, y)
  · rw [h, recolor_apply_self]
    exact hγ
  · rw [recolor_apply_of_ne c γ h]
    -- f is another edge at x; properness separates it from s(x,y)
    rw [mem_incidenceFinset] at hf
    obtain ⟨w, hw, rfl⟩ := H.exists_adj_eq_of_mem_incidenceSet hf
    have hwy : w ≠ y := by
      intro hcontra
      exact h (by rw [hcontra])
    exact hc hw hxy hwy

end Recolor

/-! ### Small bookkeeping helpers -/

section Helpers

variable {W : Type*} [Fintype W] [DecidableEq W]

private lemma not_mem_sym2 {v a b : W} (h1 : v ≠ a) (h2 : v ≠ b) :
    v ∉ s(a, b) := by
  rw [Sym2.mem_iff]
  push_neg
  exact ⟨h1, h2⟩

/-- The other endpoint of the deleted edge is not an `H`-neighbor of `x`. -/
private lemma ne_of_deleteEdges_adj {G : SimpleGraph W} [DecidableRel G.Adj]
    {x y0 y1 : W} (h : (G.deleteEdges {s(x, y0)}).Adj x y1) : y0 ≠ y1 := by
  intro heq
  subst heq
  rw [deleteEdges_adj] at h
  exact h.2 (Set.mem_singleton _)

/-- Edge deletion never raises degrees. -/
private lemma degree_deleteEdges_le {G : SimpleGraph W} [DecidableRel G.Adj]
    (s : Set (Sym2 W)) [DecidableRel (G.deleteEdges s).Adj] (v : W) :
    (G.deleteEdges s).degree v ≤ G.degree v := by
  apply Finset.card_le_card
  intro w hw
  rw [mem_neighborFinset] at hw ⊢
  exact (deleteEdges_adj.mp hw).1

/-- Mirror of the kit's `degree_deleteEdges_of_adj` at the RIGHT endpoint
of the deleted edge. -/
private lemma degree_deleteEdges_right {G : SimpleGraph W}
    [DecidableRel G.Adj] {x y0 : W} (hadj : G.Adj x y0) :
    (G.deleteEdges {s(x, y0)}).degree y0 = G.degree y0 - 1 := by
  have h1 : (G.deleteEdges {s(x, y0)}).neighborFinset y0 =
      (G.neighborFinset y0).erase x := by
    ext w
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset,
      deleteEdges_adj]
    constructor
    · rintro ⟨hadj', hne⟩
      refine ⟨?_, hadj'⟩
      rintro rfl
      exact hne (Set.mem_singleton_iff.mpr Sym2.eq_swap)
    · rintro ⟨hne, hadj'⟩
      refine ⟨hadj', ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      rcases Sym2.eq_iff.mp hmem with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact (G.ne_of_adj hadj).symm h1
      · exact hne h2
  rw [SimpleGraph.degree, h1,
    Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hadj.symm),
    ← SimpleGraph.degree]

/-- A color missing before a Kempe swap and off the swap pair stays
missing (in or out of the swapped set). -/
private lemma mem_missing_kempeSwap_of_ne {H : SimpleGraph W}
    [DecidableRel H.Adj] {n : ℕ} {c : Sym2 W → Fin n} {α β' : Fin n}
    {K : Finset W} (hclosed : H.IsKempeClosed c α β' K) {v : W} {β : Fin n}
    (hβ : β ∈ H.missingColors c v) (h1 : β ≠ α) (h2 : β ≠ β') :
    β ∈ H.missingColors (kempeSwap c α β' K) v := by
  by_cases hv : v ∈ K
  · rw [missingColors_kempeSwap_of_mem H hclosed hv]
    exact Finset.mem_image.mpr ⟨β, hβ, kempeSwapColor_of_ne h1 h2⟩
  · rw [missingColors_kempeSwap_of_not_mem H hv]
    exact hβ

/-- Inside the swapped set, a missing `β'` becomes a missing `α`. -/
private lemma alpha_mem_missing_kempeSwap {H : SimpleGraph W}
    [DecidableRel H.Adj] {n : ℕ} {c : Sym2 W → Fin n} {α β' : Fin n}
    {K : Finset W} (hclosed : H.IsKempeClosed c α β' K) {v : W}
    (hv : v ∈ K) (hβ' : β' ∈ H.missingColors c v) :
    α ∈ H.missingColors (kempeSwap c α β' K) v := by
  rw [missingColors_kempeSwap_of_mem H hclosed hv]
  exact Finset.mem_image.mpr ⟨β', hβ', kempeSwapColor_right⟩

/-- Inside the swapped set, a missing `α` becomes a missing `β'`. -/
private lemma beta_mem_missing_kempeSwap {H : SimpleGraph W}
    [DecidableRel H.Adj] {n : ℕ} {c : Sym2 W → Fin n} {α β' : Fin n}
    {K : Finset W} (hclosed : H.IsKempeClosed c α β' K) {v : W}
    (hv : v ∈ K) (hα : α ∈ H.missingColors c v) :
    β' ∈ H.missingColors (kempeSwap c α β' K) v := by
  rw [missingColors_kempeSwap_of_mem H hclosed hv]
  exact Finset.mem_image.mpr ⟨α, hα, kempeSwapColor_left⟩

end Helpers

/-! ### Fan rotations (one and two steps) -/

section Fan

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

/-- **One-step fan rotation**: uncolored edge `x y0`; a colored neighbor
`y1` of `x` whose edge color is missing at `y0`; a color `γ` missing at
both `x` and `y1`.  Recolor `s(x,y1) ↦ γ` and extend. -/
private lemma extend_of_fan1 {x y0 y1 : W} (hadj : G.Adj x y0)
    {c : Sym2 W → Fin 5}
    (hc : (G.deleteEdges {s(x, y0)}).IsProperEdgeColoring c)
    (hy1 : (G.deleteEdges {s(x, y0)}).Adj x y1)
    (hβ0y0 : c s(x, y1) ∈ (G.deleteEdges {s(x, y0)}).missingColors c y0)
    {γ : Fin 5}
    (hγx : γ ∈ (G.deleteEdges {s(x, y0)}).missingColors c x)
    (hγy1 : γ ∈ (G.deleteEdges {s(x, y0)}).missingColors c y1) :
    G.EdgeColorable 5 := by
  have hprop2 : (G.deleteEdges {s(x, y0)}).IsProperEdgeColoring
      (recolor c s(x, y1) γ) :=
    isProperEdgeColoring_recolor hc hy1 hγx hγy1
  have hγβ0 : γ ≠ c s(x, y1) := fun h =>
    ((G.deleteEdges {s(x, y0)}).mem_missingColors).mp hγx _
      (mk_mem_incidenceFinset hy1) h.symm
  have hmx : c s(x, y1) ∈ (G.deleteEdges {s(x, y0)}).missingColors
      (recolor c s(x, y1) γ) x :=
    old_color_missing_recolor hc hy1 hγβ0
  have hy0mem : y0 ∉ s(x, y1) :=
    not_mem_sym2 (G.ne_of_adj hadj).symm (ne_of_deleteEdges_adj hy1)
  have hmy0 : c s(x, y1) ∈ (G.deleteEdges {s(x, y0)}).missingColors
      (recolor c s(x, y1) γ) y0 := by
    rw [missingColors_recolor_of_not_mem hy0mem]
    exact hβ0y0
  exact EdgeColorable.of_missing_inter G hadj hprop2 hmx hmy0

/-- **Two-step fan rotation**: additionally a second colored neighbor
`y2` whose edge color is missing at `y1`; a color `γ` missing at both
`x` and `y2`.  Recolor `s(x,y2) ↦ γ`, then fall to `extend_of_fan1`. -/
private lemma extend_of_fan2 {x y0 y1 y2 : W} (hadj : G.Adj x y0)
    {c : Sym2 W → Fin 5}
    (hc : (G.deleteEdges {s(x, y0)}).IsProperEdgeColoring c)
    (hy1 : (G.deleteEdges {s(x, y0)}).Adj x y1)
    (hy2 : (G.deleteEdges {s(x, y0)}).Adj x y2) (hne12 : y1 ≠ y2)
    (hβ0y0 : c s(x, y1) ∈ (G.deleteEdges {s(x, y0)}).missingColors c y0)
    (hβ1y1 : c s(x, y2) ∈ (G.deleteEdges {s(x, y0)}).missingColors c y1)
    {γ : Fin 5}
    (hγx : γ ∈ (G.deleteEdges {s(x, y0)}).missingColors c x)
    (hγy2 : γ ∈ (G.deleteEdges {s(x, y0)}).missingColors c y2) :
    G.EdgeColorable 5 := by
  have hprop2 : (G.deleteEdges {s(x, y0)}).IsProperEdgeColoring
      (recolor c s(x, y2) γ) :=
    isProperEdgeColoring_recolor hc hy2 hγx hγy2
  have hγβ1 : γ ≠ c s(x, y2) := fun h =>
    ((G.deleteEdges {s(x, y0)}).mem_missingColors).mp hγx _
      (mk_mem_incidenceFinset hy2) h.symm
  have hedge_ne : s(x, y1) ≠ s(x, y2) := fun h =>
    hne12 (Sym2.congr_right.mp h)
  have hy0mem : y0 ∉ s(x, y2) :=
    not_mem_sym2 (G.ne_of_adj hadj).symm (ne_of_deleteEdges_adj hy2)
  have hy1mem : y1 ∉ s(x, y2) :=
    not_mem_sym2 (fun h => (G.deleteEdges {s(x, y0)}).ne_of_adj hy1 h.symm)
      hne12
  apply extend_of_fan1 G hadj hprop2 hy1 ?_ (γ := c s(x, y2)) ?_ ?_
  · -- the y1-edge keeps its color, still missing at y0
    rw [show recolor c s(x, y2) (γ := γ) s(x, y1) = c s(x, y1) from
      recolor_apply_of_ne c γ hedge_ne,
      missingColors_recolor_of_not_mem hy0mem]
    exact hβ0y0
  · exact old_color_missing_recolor hc hy2 hγβ1
  · rw [missingColors_recolor_of_not_mem hy1mem]
    exact hβ1y1

end Fan

/-! ### Present/missing complementation -/

section PresentMissing

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {H : SimpleGraph W} [DecidableRel H.Adj]

private lemma mem_present_of_not_missing {n : ℕ} {c : Sym2 W → Fin n}
    {v : W} {β : Fin n} (h : β ∉ H.missingColors c v) :
    β ∈ H.presentColors c v := by
  simpa [SimpleGraph.missingColors] using h

private lemma not_missing_of_present {n : ℕ} {c : Sym2 W → Fin n}
    {v : W} {β : Fin n} (h : β ∈ H.presentColors c v) :
    β ∉ H.missingColors c v := by
  simp [SimpleGraph.missingColors, h]

end PresentMissing

/-! ### The extension theorem: at Δ ≤ 4 with 5 colors, every deletion
coloring extends -/

section Extend

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

private lemma extend_always (hdeg : ∀ v, G.degree v ≤ 4)
    {x y0 : W} (hadj : G.Adj x y0)
    (hcol : (G.deleteEdges {s(x, y0)}).EdgeColorable 5) :
    G.EdgeColorable 5 := by
  by_contra hG
  obtain ⟨c, hc⟩ := hcol
  set H := G.deleteEdges {s(x, y0)} with hH
  -- Lemma A: the endpoint palettes are disjoint
  have hdisj : Disjoint (H.missingColors c x) (H.missingColors c y0) :=
    disjoint_missingColors_of_not_edgeColorable G hG hadj hc
  -- endpoint palettes have ≥ 2 colors
  have hcardx : 2 ≤ (H.missingColors c x).card := by
    rw [card_missingColors_of_isProperEdgeColoring H hc x, Fintype.card_fin]
    have h1 : H.degree x = G.degree x - 1 := degree_deleteEdges_of_adj G hadj
    have h2 := hdeg x
    have h3 : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y0, hadj⟩
    omega
  have hcardy0 : 2 ≤ (H.missingColors c y0).card := by
    rw [card_missingColors_of_isProperEdgeColoring H hc y0, Fintype.card_fin]
    have h1 : H.degree y0 = G.degree y0 - 1 := degree_deleteEdges_right hadj
    have h2 := hdeg y0
    have h3 : 0 < G.degree y0 :=
      (G.degree_pos_iff_exists_adj y0).mpr ⟨x, hadj.symm⟩
    omega
  -- every vertex misses at least one of the 5 colors
  have hmissnon : ∀ v : W, ∃ β, β ∈ H.missingColors c v := by
    intro v
    have h1 : (H.missingColors c v).card = 5 - H.degree v := by
      rw [card_missingColors_of_isProperEdgeColoring H hc v, Fintype.card_fin]
    have h2 : H.degree v ≤ G.degree v := degree_deleteEdges_le _ v
    have h3 := hdeg v
    obtain ⟨β, hβ⟩ := Finset.card_pos.mp (by omega :
      0 < (H.missingColors c v).card)
    exact ⟨β, hβ⟩
  obtain ⟨α, hα⟩ := hmissnon x
  obtain ⟨β0, hβ0⟩ := Finset.card_pos.mp (by omega :
    0 < (H.missingColors c y0).card)
  -- β0 is present at x: fan vertex y1
  have hβ0x : β0 ∉ H.missingColors c x := fun h =>
    (Finset.disjoint_left.mp hdisj h) hβ0
  have hβ0px : β0 ∈ H.presentColors c x := mem_present_of_not_missing hβ0x
  obtain ⟨y1, hy1, hcy1⟩ := (H.mem_presentColors_iff_exists_adj).mp hβ0px
  have hne_y0y1 : y0 ≠ y1 := ne_of_deleteEdges_adj hy1
  obtain ⟨β1, hβ1⟩ := hmissnon y1
  -- β0 is present at y1 (the edge x y1 itself)
  have hβ0py1 : β0 ∈ H.presentColors c y1 := by
    rw [H.mem_presentColors_iff_exists_adj]
    exact ⟨x, hy1.symm, by rw [show s(y1, x) = s(x, y1) from Sym2.eq_swap]
                           exact hcy1⟩
  have hβ1_ne_β0 : β1 ≠ β0 := fun h =>
    not_missing_of_present hβ0py1 (h ▸ hβ1)
  have hβ0_ne_α : β0 ≠ α := fun h => not_missing_of_present hβ0px (h ▸ hα)
  by_cases hβ1x : β1 ∈ H.missingColors c x
  · -- β1 ∈ φ̄(x): one-step rotation
    exact hG (extend_of_fan1 G hadj hc hy1 (by rw [hcy1]; exact hβ0)
      hβ1x hβ1)
  by_cases hβ1y0 : β1 ∈ H.missingColors c y0
  · -- β1 ∈ φ̄(y0): (α,β1)-swap through y1, then one-step rotation with α
    have hclosed : H.IsKempeClosed c α β1
        ((H.kempeGraph c α β1).reachFinset y1) :=
      isKempeClosed_reachFinset H c α β1 y1
    have hnotreach : ¬(H.kempeGraph c α β1).Reachable x y1 :=
      not_reachable_kempeGraph_of_missing_of_ne G hG hadj hc hα hβ1y0
        (H.ne_of_adj hy1).symm hne_y0y1.symm (Or.inr hβ1)
    have hxK : x ∉ (H.kempeGraph c α β1).reachFinset y1 := by
      rw [mem_reachFinset]
      exact fun h => hnotreach h.symm
    have hy0K : y0 ∉ (H.kempeGraph c α β1).reachFinset y1 := by
      rw [mem_reachFinset]
      intro h
      exact hnotreach ((reachable_kempeGraph_of_missing G hG hadj hc hα
        hβ1y0).trans h.symm)
    have hy1K : y1 ∈ (H.kempeGraph c α β1).reachFinset y1 :=
      self_mem_reachFinset _ y1
    have hc' : H.IsProperEdgeColoring (kempeSwap c α β1
        ((H.kempeGraph c α β1).reachFinset y1)) :=
      IsProperEdgeColoring.kempeSwap_of_isKempeClosed H hc hclosed
    have hαx' : α ∈ H.missingColors (kempeSwap c α β1
        ((H.kempeGraph c α β1).reachFinset y1)) x := by
      rw [missingColors_kempeSwap_of_not_mem H hxK]
      exact hα
    have hαy1' : α ∈ H.missingColors (kempeSwap c α β1
        ((H.kempeGraph c α β1).reachFinset y1)) y1 :=
      alpha_mem_missing_kempeSwap hclosed hy1K hβ1
    have hβ0y0' : (kempeSwap c α β1
        ((H.kempeGraph c α β1).reachFinset y1)) s(x, y1) ∈
        H.missingColors (kempeSwap c α β1
          ((H.kempeGraph c α β1).reachFinset y1)) y0 := by
      rw [kempeSwap_apply_eq_of_not_mem hxK, hcy1,
        missingColors_kempeSwap_of_not_mem H hy0K]
      exact hβ0
    exact hG (extend_of_fan1 G hadj hc' hy1 hβ0y0' hαx' hαy1')
  -- β1 is fresh: present at x, giving the second fan vertex y2
  have hβ1px : β1 ∈ H.presentColors c x := mem_present_of_not_missing hβ1x
  obtain ⟨y2, hy2, hcy2⟩ := (H.mem_presentColors_iff_exists_adj).mp hβ1px
  have hne_y0y2 : y0 ≠ y2 := ne_of_deleteEdges_adj hy2
  have hne_y1y2 : y1 ≠ y2 := by
    intro h
    rw [← h, hcy1] at hcy2
    exact hβ1_ne_β0 hcy2.symm
  have hβ1py2 : β1 ∈ H.presentColors c y2 := by
    rw [H.mem_presentColors_iff_exists_adj]
    exact ⟨x, hy2.symm, by rw [show s(y2, x) = s(x, y2) from Sym2.eq_swap]
                           exact hcy2⟩
  obtain ⟨β2, hβ2⟩ := hmissnon y2
  have hβ2_ne_β1 : β2 ≠ β1 := fun h =>
    not_missing_of_present hβ1py2 (h ▸ hβ2)
  have hβ1_ne_α : β1 ≠ α := fun h => not_missing_of_present hβ1px (h ▸ hα)
  by_cases hβ2x : β2 ∈ H.missingColors c x
  · -- β2 ∈ φ̄(x): two-step rotation
    exact hG (extend_of_fan2 G hadj hc hy1 hy2 hne_y1y2
      (by rw [hcy1]; exact hβ0) (by rw [hcy2]; exact hβ1) hβ2x hβ2)
  by_cases hβ2y0 : β2 ∈ H.missingColors c y0
  · -- β2 ∈ φ̄(y0): (α,β2)-swap through y2, then two-step rotation with α
    have hclosed : H.IsKempeClosed c α β2
        ((H.kempeGraph c α β2).reachFinset y2) :=
      isKempeClosed_reachFinset H c α β2 y2
    have hnotreach : ¬(H.kempeGraph c α β2).Reachable x y2 :=
      not_reachable_kempeGraph_of_missing_of_ne G hG hadj hc hα hβ2y0
        (H.ne_of_adj hy2).symm hne_y0y2.symm (Or.inr hβ2)
    have hxK : x ∉ (H.kempeGraph c α β2).reachFinset y2 := by
      rw [mem_reachFinset]
      exact fun h => hnotreach h.symm
    have hy0K : y0 ∉ (H.kempeGraph c α β2).reachFinset y2 := by
      rw [mem_reachFinset]
      intro h
      exact hnotreach ((reachable_kempeGraph_of_missing G hG hadj hc hα
        hβ2y0).trans h.symm)
    have hy2K : y2 ∈ (H.kempeGraph c α β2).reachFinset y2 :=
      self_mem_reachFinset _ y2
    have hc' : H.IsProperEdgeColoring (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) :=
      IsProperEdgeColoring.kempeSwap_of_isKempeClosed H hc hclosed
    have hαx' : α ∈ H.missingColors (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) x := by
      rw [missingColors_kempeSwap_of_not_mem H hxK]
      exact hα
    have hαy2' : α ∈ H.missingColors (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) y2 :=
      alpha_mem_missing_kempeSwap hclosed hy2K hβ2
    have hβ0y0' : (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) s(x, y1) ∈
        H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) y0 := by
      rw [kempeSwap_apply_eq_of_not_mem hxK, hcy1,
        missingColors_kempeSwap_of_not_mem H hy0K]
      exact hβ0
    have hβ1y1' : (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) s(x, y2) ∈
        H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) y1 := by
      rw [kempeSwap_apply_eq_of_not_mem hxK, hcy2]
      exact mem_missing_kempeSwap_of_ne hclosed hβ1 hβ1_ne_α hβ2_ne_β1.symm
    exact hG (extend_of_fan2 G hadj hc' hy1 hy2 hne_y1y2 hβ0y0' hβ1y1'
      hαx' hαy2')
  by_cases hβ2y1 : β2 ∈ H.missingColors c y1
  · -- β2 ∈ φ̄(y1): the chain flip
    have hβ0_ne_β2 : β0 ≠ β2 := fun h =>
      not_missing_of_present hβ0py1 (h ▸ hβ2y1)
    have hclosed : H.IsKempeClosed c α β2
        ((H.kempeGraph c α β2).reachFinset y2) :=
      isKempeClosed_reachFinset H c α β2 y2
    have hy2K : y2 ∈ (H.kempeGraph c α β2).reachFinset y2 :=
      self_mem_reachFinset _ y2
    have hc' : H.IsProperEdgeColoring (kempeSwap c α β2
        ((H.kempeGraph c α β2).reachFinset y2)) :=
      IsProperEdgeColoring.kempeSwap_of_isKempeClosed H hc hclosed
    by_cases hxK : x ∈ (H.kempeGraph c α β2).reachFinset y2
    · -- x on the chain: y1 is not; β2 transfers to φ̄(x); 1-step rotation
      have hy1K : y1 ∉ (H.kempeGraph c α β2).reachFinset y2 := by
        intro hy1K
        rw [mem_reachFinset] at hxK hy1K
        exact reachable_three_deg_le_one_false (H.kempeGraph c α β2)
          (fun z => degree_kempeGraph_le_two H hc α β2 z)
          (H.ne_of_adj hy2).symm hne_y1y2.symm (H.ne_of_adj hy1)
          (degree_kempeGraph_le_one_of_missing H hc (Or.inr hβ2))
          (degree_kempeGraph_le_one_of_missing H hc (Or.inl hα))
          (degree_kempeGraph_le_one_of_missing H hc (Or.inr hβ2y1))
          hxK hy1K
      have hβ2x' : β2 ∈ H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) x :=
        beta_mem_missing_kempeSwap hclosed hxK hα
      have hβ2y1' : β2 ∈ H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) y1 := by
        rw [missingColors_kempeSwap_of_not_mem H hy1K]
        exact hβ2y1
      have hβ0y0' : (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) s(x, y1) ∈
          H.missingColors (kempeSwap c α β2
            ((H.kempeGraph c α β2).reachFinset y2)) y0 := by
        rw [show s(x, y1) = s(y1, x) from Sym2.eq_swap,
          kempeSwap_apply_eq_of_not_mem hy1K,
          show s(y1, x) = s(x, y1) from Sym2.eq_swap, hcy1]
        exact mem_missing_kempeSwap_of_ne hclosed hβ0 hβ0_ne_α hβ0_ne_β2
      exact hG (extend_of_fan1 G hadj hc' hy1 hβ0y0' hβ2x' hβ2y1')
    · -- x off the chain: α transfers to φ̄(y2); 2-step rotation with α
      have hαx' : α ∈ H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) x := by
        rw [missingColors_kempeSwap_of_not_mem H hxK]
        exact hα
      have hαy2' : α ∈ H.missingColors (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) y2 :=
        alpha_mem_missing_kempeSwap hclosed hy2K hβ2
      have hβ0y0' : (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) s(x, y1) ∈
          H.missingColors (kempeSwap c α β2
            ((H.kempeGraph c α β2).reachFinset y2)) y0 := by
        rw [kempeSwap_apply_eq_of_not_mem hxK, hcy1]
        exact mem_missing_kempeSwap_of_ne hclosed hβ0 hβ0_ne_α hβ0_ne_β2
      have hβ1y1' : (kempeSwap c α β2
          ((H.kempeGraph c α β2).reachFinset y2)) s(x, y2) ∈
          H.missingColors (kempeSwap c α β2
            ((H.kempeGraph c α β2).reachFinset y2)) y1 := by
        rw [kempeSwap_apply_eq_of_not_mem hxK, hcy2]
        exact mem_missing_kempeSwap_of_ne hclosed hβ1 hβ1_ne_α
          hβ2_ne_β1.symm
      exact hG (extend_of_fan2 G hadj hc' hy1 hy2 hne_y1y2 hβ0y0' hβ1y1'
        hαx' hαy2')
  · -- β2 fresh: counting contradiction — φ̄(y0) ⊆ present(x) = {β0,β1,β2}
    -- yet avoids β1 and β2, so |φ̄(y0)| ≤ 1 < 2
    have hβ2px : β2 ∈ H.presentColors c x := mem_present_of_not_missing hβ2x
    have hβ2_ne_β0 : β2 ≠ β0 := fun h => hβ2y0 (h ▸ hβ0)
    have hsubset : ({β0, β1, β2} : Finset (Fin 5)) ⊆
        H.presentColors c x := by
      intro γ' hγ'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hγ'
      rcases hγ' with rfl | rfl | rfl
      · exact hβ0px
      · exact hβ1px
      · exact hβ2px
    have hcard3 : ({β0, β1, β2} : Finset (Fin 5)).card = 3 :=
      Finset.card_eq_three.mpr
        ⟨β0, β1, β2, hβ1_ne_β0.symm, hβ2_ne_β0.symm, hβ2_ne_β1.symm, rfl⟩
    have hcardpx : (H.presentColors c x).card ≤ 3 := by
      rw [card_presentColors_of_isProperEdgeColoring H hc x]
      have h1 : H.degree x = G.degree x - 1 := degree_deleteEdges_of_adj G hadj
      have h2 := hdeg x
      omega
    have hpx_eq : H.presentColors c x = {β0, β1, β2} :=
      (Finset.eq_of_subset_of_card_le hsubset
        (by rw [hcard3]; exact hcardpx)).symm
    have hsub : H.missingColors c y0 ⊆ {β0} := by
      intro γ' hγ'
      have hγ'px : γ' ∈ H.presentColors c x :=
        mem_present_of_not_missing
          (fun h => (Finset.disjoint_left.mp hdisj h) hγ')
      rw [hpx_eq] at hγ'px
      simp only [Finset.mem_insert, Finset.mem_singleton] at hγ'px
      rcases hγ'px with h | h | h
      · exact Finset.mem_singleton.mpr h
      · exact absurd (h ▸ hγ') hβ1y0
      · exact absurd (h ▸ hγ') hβ2y0
    have hle1 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle1
    omega

end Extend

/-! ### Vizing at Δ ≤ 4, five colors: induction on the edge count -/

section Vizing

variable {W : Type*} [Fintype W] [DecidableEq W]

private lemma colorable_of_no_edges {G : SimpleGraph W} [DecidableRel G.Adj]
    (h : G.edgeFinset = ∅) : G.EdgeColorable 5 := by
  refine ⟨fun _ => 0, ?_⟩
  intro u v w huv _ _
  have hmem : s(u, v) ∈ G.edgeFinset := by
    rw [mem_edgeFinset]
    exact huv
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty _)

private theorem aux_colorable (n : ℕ) :
    ∀ (G : SimpleGraph W) [DecidableRel G.Adj], G.edgeFinset.card ≤ n →
      (∀ v, G.degree v ≤ 4) → G.EdgeColorable 5 := by
  induction n with
  | zero =>
    intro G _ hcard _
    exact colorable_of_no_edges (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro G _ hcard hdeg
    by_cases hE : G.edgeFinset = ∅
    · exact colorable_of_no_edges hE
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      induction e using Sym2.ind with
      | _ x y0 =>
        have hadj : G.Adj x y0 := by
          rw [mem_edgeFinset] at he
          exact he
        have hsub : (G.deleteEdges {s(x, y0)}).edgeFinset ⊆
            G.edgeFinset.erase s(x, y0) := by
          intro f hf
          rw [mem_edgeFinset, edgeSet_deleteEdges] at hf
          rw [Finset.mem_erase, mem_edgeFinset]
          exact ⟨fun h => hf.2 (h ▸ Set.mem_singleton _), hf.1⟩
        have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨_, he⟩
        have hcard' : (G.deleteEdges {s(x, y0)}).edgeFinset.card ≤ n := by
          have h1 := Finset.card_le_card hsub
          have h2 : (G.edgeFinset.erase s(x, y0)).card =
              G.edgeFinset.card - 1 := Finset.card_erase_of_mem he
          omega
        have hdeg' : ∀ v, (G.deleteEdges {s(x, y0)}).degree v ≤ 4 :=
          fun v => le_trans (degree_deleteEdges_le _ v) (hdeg v)
        exact extend_always G hdeg hadj
          (ih (G.deleteEdges {s(x, y0)}) hcard' hdeg')

/-- **Vizing's bound at Δ ≤ 4** (the Λ2 core): every simple graph with all
degrees ≤ 4 is properly 5-edge-colorable. -/
private theorem edgeColorable_five_of_degree_le_four (G : SimpleGraph W)
    [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 4) :
    G.EdgeColorable 5 :=
  aux_colorable G.edgeFinset.card G le_rfl hdeg

end Vizing

/-- TARGET Λ2 (VERBATIM from synthesis.md §4; identical to the sibling
rung5_lam2 pin). -/
theorem exists_five_multicoloring_of_simple
    {α : Type*} [Fintype α] [DecidableEq α]
    (mult : α → α → ℕ) (hsymm : ∀ a b, mult a b = mult b a)
    (hloop : ∀ a, mult a a = 0)
    (hdeg : ∀ a, mdeg mult a ≤ 4) (hsimple : ∀ a b, mult a b ≤ 1) :
    ∃ f, IsMulticoloring (C := Fin 5) mult f := by
  classical
  -- the support graph of the (simple) multiplicity matrix
  let Gm : SimpleGraph α :=
    { Adj := fun a b => 0 < mult a b
      symm := by
        intro a b h
        show 0 < mult b a
        rw [hsymm b a]
        exact h
      loopless := ⟨by
        intro a h
        rw [show mult a a = 0 from hloop a] at h
        exact lt_irrefl 0 h⟩ }
  haveI : DecidableRel Gm.Adj := fun a b =>
    inferInstanceAs (Decidable (0 < mult a b))
  -- degrees transfer: the support degree is at most the matrix degree
  have hdegm : ∀ a, Gm.degree a ≤ 4 := by
    intro a
    refine le_trans ?_ (hdeg a)
    have h1 : Gm.degree a =
        (Finset.univ.filter fun b => 0 < mult a b).card := by
      rw [SimpleGraph.degree]
      congr 1
      ext b
      rw [mem_neighborFinset, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
    rw [h1, mdeg]
    calc (Finset.univ.filter fun b => 0 < mult a b).card
        = ∑ b ∈ Finset.univ.filter (fun b => 0 < mult a b), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ b ∈ Finset.univ.filter (fun b => 0 < mult a b), mult a b :=
          Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
      _ ≤ ∑ b, mult a b :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Vizing at Δ ≤ 4 on the support graph
  obtain ⟨f, hf⟩ := edgeColorable_five_of_degree_le_four Gm hdegm
  -- transport back to the matrix encoding
  refine ⟨fun a b => if 0 < mult a b then {f s(a, b)} else ∅, ?_, ?_, ?_⟩
  · intro u v
    show (if 0 < mult u v then ({f s(u, v)} : Finset (Fin 5)) else ∅) =
      (if 0 < mult v u then ({f s(v, u)} : Finset (Fin 5)) else ∅)
    by_cases h : 0 < mult u v
    · rw [if_pos h, if_pos (by rw [hsymm v u]; exact h)]
      rw [show s(u, v) = s(v, u) from Sym2.eq_swap]
    · rw [if_neg h, if_neg (fun h2 => h (by rw [hsymm u v]; exact h2))]
  · intro u v
    show (if 0 < mult u v then ({f s(u, v)} : Finset (Fin 5)) else ∅).card =
      mult u v
    by_cases h : 0 < mult u v
    · rw [if_pos h, Finset.card_singleton]
      have := hsimple u v
      omega
    · rw [if_neg h, Finset.card_empty]
      omega
  · intro u v w hvw
    show Disjoint (if 0 < mult u v then ({f s(u, v)} : Finset (Fin 5)) else ∅)
      (if 0 < mult u w then ({f s(u, w)} : Finset (Fin 5)) else ∅)
    by_cases h1 : 0 < mult u v
    · by_cases h2 : 0 < mult u w
      · rw [if_pos h1, if_pos h2, Finset.disjoint_singleton]
        exact hf h1 h2 hvw
      · rw [if_neg h2]
        exact Finset.disjoint_empty_right _
    · rw [if_neg h1]
      exact Finset.disjoint_empty_left _

end SMaj.Lam2
