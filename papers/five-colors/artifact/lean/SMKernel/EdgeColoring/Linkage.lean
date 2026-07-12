/-
SMKernel/EdgeColoring/Linkage.lean — the coloring-extension lemma, Lemma A,
and the Kempe-component API (charter §3 layout, [smk2→]).

KERNEL-RETURNED, tranche smk2 v2 resubmissions (self-contained packaging;
proofs produced AGAINST THE CANONICAL VENDORED SOURCES, so transplant is
verbatim — no simp-environment hazard this time):
- smk2_extend_v2 (Aristotle a94c3d2e, audited 2026-07-11): extension +
  Lemma A — supersedes the addendum-12 quarantine.
- smk2_component_v2 (Aristotle 823e5a62 v2, audited 2026-07-11): reach-set
  closure, component-invariance, missing-set invariance off K.

Criticality of the uncolored edge is consumed EXACTLY in Lemma A/extension
(TR Thm 2.1 trivial-fan instance); everything downstream (Lemma B, Thm 7.1,
7.2) walks through these five lemmas plus the KempeSwap laws.
-/
import SMKernel.EdgeColoring.KiersteadPath

namespace SimpleGraph

set_option linter.unusedVariables false in
/-- An uncolored edge whose two ends share a missing color extends: `G` is
`n`-edge-colorable.  (`hadj` keeps the statement aligned with its use at
critical edges; the extension argument itself does not consume it.) -/
theorem EdgeColorable.of_missing_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {v0 v1 : V} (hadj : G.Adj v0 v1)
    {c : Sym2 V → Fin n}
    (hc : (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c) {γ : Fin n}
    (h0 : γ ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v0)
    (h1 : γ ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v1) :
    G.EdgeColorable n := by
  use fun e => if e = s(v0, v1) then γ else c e;
  intro u v w hu hv hw;
  by_cases huv : s(u, v) = s(v0, v1) <;> by_cases huw : s(u, w) = s(v0, v1) <;> simp_all +decide [ SimpleGraph.deleteEdges ];
  · grind +suggestions;
  · cases huv <;> simp_all +decide [ SimpleGraph.missingColors ];
    · contrapose! h0;
      unfold SimpleGraph.presentColors; simp +decide [ *, SimpleGraph.incidenceFinset ] ;
      exact ⟨ s(v0, w), by aesop ⟩;
    · contrapose! h1; simp_all +decide [ SimpleGraph.presentColors ] ;
      exact ⟨ s(v1, w), by aesop ⟩;
  · cases huw <;> simp_all +decide [ SimpleGraph.missingColors ];
    · simp_all +decide [ SimpleGraph.presentColors ];
    · contrapose! h1; simp_all +decide [ SimpleGraph.presentColors ] ;
      exact ⟨ s(v1, v), by aesop ⟩;
  · have := hc ( show ( G \ fromEdgeSet { s(v0, v1) } ).Adj u v from ?_ ) ( show ( G \ fromEdgeSet { s(v0, v1) } ).Adj u w from ?_ ) hw; simp_all +decide;
    · lia;
    · simp_all +decide;
    · simp_all +decide

/-- **Lemma A** (TR Thm 2.1(a), trivial fan).  At a critical edge the two
end palettes are disjoint. -/
theorem disjoint_missingColors_of_not_edgeColorable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {v0 v1 : V} {c : Sym2 V → Fin n}
    (hG : ¬G.EdgeColorable n) (hadj : G.Adj v0 v1)
    (hc : (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c) :
    Disjoint ((G.deleteEdges {s(v0, v1)}).missingColors c v0)
      ((G.deleteEdges {s(v0, v1)}).missingColors c v1) := by
  contrapose! hG;
  rw [ Finset.not_disjoint_iff ] at hG;
  exact EdgeColorable.of_missing_inter G hadj hc hG.choose_spec.1 hG.choose_spec.2

/-- The reachability set of any vertex in the Kempe subgraph is
Kempe-closed (no `{α,β}`-edge crosses its boundary). -/
theorem isKempeClosed_reachFinset
    {V C : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [DecidableEq C]
    (c : Sym2 V → C) (α β : C) (v : V) :
    H.IsKempeClosed c α β ((H.kempeGraph c α β).reachFinset v) := by
  intro u w hadj;
  simp +decide [ SimpleGraph.reachFinset ];
  exact ⟨ fun h => h.trans ( SimpleGraph.Adj.reachable hadj ), fun h => h.trans ( SimpleGraph.Adj.reachable hadj.symm ) ⟩

/-- Reach-sets are component-invariant: any member generates the same
reach-set. -/
theorem reachFinset_eq_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {v w : V}
    (hw : w ∈ H.reachFinset v) :
    H.reachFinset w = H.reachFinset v := by
  ext x;
  simp +decide [ reachFinset ] at hw ⊢;
  exact ⟨ fun h => hw.trans h, fun h => hw.symm.trans h ⟩

/-- Vertices outside the swapped set keep their missing sets. -/
theorem missingColors_kempeSwap_of_not_mem
    {V C : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [Fintype C] [DecidableEq C]
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v : V}
    (hv : v ∉ K) :
    H.missingColors (kempeSwap c α β K) v = H.missingColors c v := by
  convert congr_arg _ ( presentColors_kempeSwap_of_not_mem _ hv )

/-! ### Lemma B (kernel-returned, smk2_linkage_v2, Aristotle 282f216c,
audited 2026-07-11; cross-confirmed by smk3_clause_c T1/T2 and
smk4_step T1/T2 independent proofs) -/

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

/-- **Lemma B, linkage form** (TR Thm 2.1(b), trivial fan).  At a critical
edge, for α ∈ φ̄(v₀) and β ∈ φ̄(v₁), the (α,β)-Kempe subgraph of the
deletion links v₀ to v₁. -/
theorem reachable_kempeGraph_of_missing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {v0 v1 : V} {α β : Fin n} {c : Sym2 V → Fin n}
    (hG : ¬G.EdgeColorable n) (hadj : G.Adj v0 v1)
    (hc : (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c)
    (hα : α ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v0)
    (hβ : β ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v1) :
    ((G.deleteEdges {s(v0, v1)}).kempeGraph c α β).Reachable v0 v1 := by
  classical
  by_contra h
  set H := G.deleteEdges {s(v0, v1)} with hH
  set K := (H.kempeGraph c α β).reachFinset v0 with hK
  have hclosed : H.IsKempeClosed c α β K := isKempeClosed_reachFinset H c α β v0
  have hproper' : H.IsProperEdgeColoring (kempeSwap c α β K) :=
    IsProperEdgeColoring.kempeSwap_of_isKempeClosed H hc hclosed
  have hv0 : v0 ∈ K := self_mem_reachFinset _ v0
  have hv1 : v1 ∉ K := by
    rw [hK, mem_reachFinset]; exact h
  have hmiss0 : β ∈ H.missingColors (kempeSwap c α β K) v0 := by
    rw [missingColors_kempeSwap_of_mem H hclosed hv0, Finset.mem_image]
    exact ⟨α, hα, kempeSwapColor_left⟩
  have hmiss1 : β ∈ H.missingColors (kempeSwap c α β K) v1 := by
    unfold SimpleGraph.missingColors
    rw [presentColors_kempeSwap_of_not_mem H hv1]
    simpa [SimpleGraph.missingColors] using hβ
  exact hG (EdgeColorable.of_missing_inter G hadj hproper' hmiss0 hmiss1)

/-- **Separation corollary** (the downstream-facing form of "the
(α,β)-chain through v₀ is a path with ends exactly v₀, v₁"): no third
vertex missing α or β lies on the v₀-chain. -/
theorem not_reachable_kempeGraph_of_missing_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {c : Sym2 V → Fin n}
    {v0 v1 w : V} {α β : Fin n}
    (hG : ¬G.EdgeColorable n)
    (hadj : G.Adj v0 v1)
    (hc : (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c)
    (hα : α ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v0)
    (hβ : β ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v1)
    (hw0 : w ≠ v0) (hw1 : w ≠ v1)
    (hw : α ∈ (G.deleteEdges {s(v0, v1)}).missingColors c w ∨
      β ∈ (G.deleteEdges {s(v0, v1)}).missingColors c w) :
    ¬((G.deleteEdges {s(v0, v1)}).kempeGraph c α β).Reachable v0 w := by
  classical
  set H := G.deleteEdges {s(v0, v1)} with hH
  intro hreach
  have hrab : (H.kempeGraph c α β).Reachable v0 v1 :=
    reachable_kempeGraph_of_missing G hG hadj hc hα hβ
  have hdeg : ∀ x, (H.kempeGraph c α β).degree x ≤ 2 :=
    fun x => degree_kempeGraph_le_two H hc α β x
  have hd0 : (H.kempeGraph c α β).degree v0 ≤ 1 :=
    degree_kempeGraph_le_one_of_missing H hc (Or.inl hα)
  have hd1 : (H.kempeGraph c α β).degree v1 ≤ 1 :=
    degree_kempeGraph_le_one_of_missing H hc (Or.inr hβ)
  have hdw : (H.kempeGraph c α β).degree w ≤ 1 :=
    degree_kempeGraph_le_one_of_missing H hc hw
  exact reachable_three_deg_le_one_false (H.kempeGraph c α β) hdeg
    (G.ne_of_adj hadj) (Ne.symm hw0) (Ne.symm hw1) hd0 hd1 hdw hrab hreach

end SimpleGraph
