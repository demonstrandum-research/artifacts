/-
Pins3.lean — the STRIKE-A §9 Lean ladder for the t ≤ 2 descent theorem.

Companion to Pins2.lean (same self-containment discipline: imports Pins2 only,
which is self-contained over the frozen Maj5Base).  Statements authored round 14
(2026-07-12) from STRIKE-A.md (commit 10bf2ea); every pin's number below refers
to STRIKE-A §9's ladder and the document section carrying its informal proof.

Status vocabulary (as in Pins2):
* PROVED            — sorry-free here.
* LADDER-PIN        — informally proved in STRIKE-A; formal bridge open (sorry).
* MERGE-PIN         — item 12 (Lemma MERGE′), the ONE open mathematical debt,
                      here fused with item 13 (its ledger instantiation) into
                      `strict_merge_of_blocked` until the debris-linkage
                      formalism (§9 item 11) is authored in a dedicated round.

Deferred (documented): §9 item 11 (`splice_ledger_connected_debris`, the debris
linkage of a toggle) needs its own formalization campaign; its ASSEMBLY role is
absorbed by the fused MERGE-PIN below.  The Δω identity half of item 6 is
deferred with it; item 6's validity half is pin `three_edge_toggle_valid`.
-/

import Pins2

set_option autoImplicit false

open Finset SimpleGraph

namespace Rung4Moonshot

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Toggle vocabulary (STRIKE-A §0)

A toggle is a finite set of edges; toggling replaces each half by its symmetric
difference with `T`.  Decidability of the toggled adjacency is taken
classically (pin-file infrastructure; nothing downstream computes with it). -/

/-- The graph `H △ T`: edges of `H` outside `T` together with `T`-edges not in
`H` (as always, `fromEdgeSet` discards any diagonal element). -/
noncomputable def toggled (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ↑(symmDiff H.edgeFinset T)

noncomputable instance instDecToggled (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Sym2 V)) : DecidableRel (toggled H T).Adj :=
  Classical.decRel _

/-- A valid toggle for the split `(H, K)` of `G`: a set of `G`-edges whose
toggle yields a split again (STRIKE-A §0). -/
def IsValidToggle (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T : Finset (Sym2 V)) : Prop :=
  ↑T ⊆ G.edgeSet ∧ IsEdgeSplit G (toggled H T) (toggled K T)

/-- A strict toggle: the total odd-cycle count drops. -/
def IsStrictToggle (H K : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel K.Adj] (T : Finset (Sym2 V)) : Prop :=
  oddCycleCount (toggled H T) + oddCycleCount (toggled K T) <
    oddCycleCount H + oddCycleCount K

set_option maxHeartbeats 2000000 in
/-- LADDER-PIN 1 (§0; vertex-local characterization of valid toggles).
`h`/`k` count the `T`-edges at `v` on each side; deg-4 vertices balance, deg-3
vertices absorb a one-edge imbalance on their light side only. -/
lemma toggle_valid_iff
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (T : Finset (Sym2 V)) (hT : ↑T ⊆ G.edgeSet) :
    IsValidToggle G H K T ↔
      ∀ v : V,
        (G.degree v = 4 →
          #{e ∈ T | e ∈ H.incidenceFinset v} = #{e ∈ T | e ∈ K.incidenceFinset v}) ∧
        (H.degree v = 2 ∧ K.degree v = 1 →
          #{e ∈ T | e ∈ H.incidenceFinset v} = #{e ∈ T | e ∈ K.incidenceFinset v} ∨
          #{e ∈ T | e ∈ H.incidenceFinset v} = #{e ∈ T | e ∈ K.incidenceFinset v} + 1) ∧
        (H.degree v = 1 ∧ K.degree v = 2 →
          #{e ∈ T | e ∈ K.incidenceFinset v} = #{e ∈ T | e ∈ H.incidenceFinset v} ∨
          #{e ∈ T | e ∈ K.incidenceFinset v} = #{e ∈ T | e ∈ H.incidenceFinset v} + 1) := by
  constructor;
  · rintro ⟨ hT₁, hT₂ ⟩ v;
    have h_deg_toggled : (toggled H T).degree v = H.degree v + (T.filter (fun e => e ∈ K.incidenceFinset v)).card - (T.filter (fun e => e ∈ H.incidenceFinset v)).card ∧ (toggled K T).degree v = K.degree v + (T.filter (fun e => e ∈ H.incidenceFinset v)).card - (T.filter (fun e => e ∈ K.incidenceFinset v)).card := by
      have h_deg_toggled : (toggled H T).incidenceFinset v = (H.incidenceFinset v \ T.filter (fun e => e ∈ H.incidenceFinset v)) ∪ (T.filter (fun e => e ∈ K.incidenceFinset v)) ∧ (toggled K T).incidenceFinset v = (K.incidenceFinset v \ T.filter (fun e => e ∈ K.incidenceFinset v)) ∪ (T.filter (fun e => e ∈ H.incidenceFinset v)) := by
        constructor <;> ext e <;> simp +decide [ toggled ];
        · cases hsplit ; simp_all +decide [ SimpleGraph.incidenceSet, symmDiff ];
          by_cases he : e ∈ H.edgeSet <;> by_cases he' : e ∈ T <;> simp_all +decide [ SimpleGraph.edgeSet ];
          · cases e ; aesop;
          · cases e ; simp_all +decide [ edgeSetEmbedding ];
            have := hT₁ he'; simp_all +decide [ Sym2.fromRel ] ;
            exact fun h => by rintro rfl; exact this.ne rfl;
        · rcases e with ⟨ u, v ⟩ ; simp +decide [ symmDiff ] ;
          by_cases hu : u = v <;> simp +decide [ hu, SimpleGraph.incidenceSet ];
          by_cases h : K.Adj u v <;> simp +decide [ h ];
          · have := hsplit.2.1 u v; aesop;
          · intro he hv; have := hT he; simp_all +decide [ SimpleGraph.adj_comm ] ;
            have := hsplit.1 u v; aesop;
      have h_deg_toggled : (toggled H T).degree v = (H.incidenceFinset v \ T.filter (fun e => e ∈ H.incidenceFinset v)).card + (T.filter (fun e => e ∈ K.incidenceFinset v)).card ∧ (toggled K T).degree v = (K.incidenceFinset v \ T.filter (fun e => e ∈ K.incidenceFinset v)).card + (T.filter (fun e => e ∈ H.incidenceFinset v)).card := by
        rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
        · exact ⟨ by rw [ ← h_deg_toggled.1, SimpleGraph.card_incidenceFinset_eq_degree ], by rw [ ← h_deg_toggled.2, SimpleGraph.card_incidenceFinset_eq_degree ] ⟩;
        · simp +contextual [ Finset.disjoint_left ];
        · simp +contextual [ Finset.disjoint_left ];
      simp_all +decide [ Finset.card_sdiff, SimpleGraph.card_incidenceFinset_eq_degree ];
      constructor <;> rw [ tsub_add_eq_add_tsub ];
      · congr 2 ; ext ; aesop;
      · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( SimpleGraph.card_incidenceFinset_eq_degree _ _ |> le_of_eq );
      · congr 2 with e ; simp +decide [ SimpleGraph.incidenceSet ];
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( by simp +decide [ SimpleGraph.card_incidenceFinset_eq_degree ] );
    have h_deg_toggled_le : (toggled H T).degree v ≤ 2 ∧ (toggled K T).degree v ≤ 2 := by
      exact ⟨ hT₂.2.2.2.2.1 v, hT₂.2.2.2.2.2.1 v ⟩;
    have h_deg_toggled_le : H.degree v + K.degree v = G.degree v := by
      exact hsplit.2.2.2.2.2.2 v;
    have h_deg_toggled_le : H.degree v ≤ 2 ∧ K.degree v ≤ 2 := by
      exact ⟨ hsplit.2.2.2.2.1 v, hsplit.2.2.2.2.2.1 v ⟩;
    omega;
  · intro h;
    refine' ⟨ hT, _, _, _, _, _ ⟩;
    · intro u v; have := hsplit.1 u v; simp_all +decide [ toggled ] ;
      by_cases hu : u = v <;> simp_all +decide [ symmDiff ];
      by_cases huv : s(u, v) ∈ T <;> simp_all +decide [ SimpleGraph.adj_comm ];
      have := hT huv; simp_all +decide [ SimpleGraph.adj_comm ] ;
      exact not_and_or.mp fun h => hsplit.2.1 u v h.1 h.2;
    · intro u v hu hv;
      obtain ⟨hT_sub, hT_disjoint⟩ := hsplit;
      unfold toggled at hu hv; simp_all +decide [ SimpleGraph.fromEdgeSet_adj ] ;
      cases hu.1 <;> cases hv <;> simp_all +decide [ symmDiff ];
      have := hT ( by tauto : s(u, v) ∈ T ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
    · intro u v;
      unfold toggled;
      simp +decide [ symmDiff ];
      rintro ( ⟨ huv, h ⟩ | ⟨ ⟨ huv, h ⟩, h' ⟩ ) <;> have := hsplit.1 u v <;> simp_all +decide [ SimpleGraph.adj_comm ];
      exact this.mp ( hT huv );
    · intro u v huv;
      cases hsplit ; simp_all +decide [ toggled ];
      cases huv.1 <;> simp_all +decide [ symmDiff ];
      exact Or.resolve_right ( ‹∀ u v, G.Adj u v ↔ H.Adj u v ∨ K.Adj u v› u v |>.1 ( hT ( by tauto ) ) ) ( by tauto );
    · refine' ⟨ _, _, _ ⟩;
      · intro v
        have h_deg : (toggled H T).degree v + (T.filter (fun e => e ∈ H.incidenceFinset v)).card = H.degree v + (T.filter (fun e => e ∈ K.incidenceFinset v)).card := by
          have h_deg : (toggled H T).degree v = (H.incidenceFinset v \ T).card + (T.filter (fun e => e ∈ K.incidenceFinset v)).card := by
            have h_deg : (toggled H T).incidenceFinset v = (H.incidenceFinset v \ T) ∪ (T.filter (fun e => e ∈ K.incidenceFinset v)) := by
              ext e; simp [toggled];
              constructor <;> intro he <;> simp_all +decide [ SimpleGraph.incidenceSet, symmDiff ];
              · cases he.1 <;> simp_all +decide [ IsEdgeSplit ];
                rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
                exact hsplit.1 u v |>.1 ( hT ( by tauto ) ) |> Or.resolve_left <| by tauto;
              · have := hsplit.2.1; simp_all +decide [ Set.subset_def ] ;
                cases e ; aesop;
            rw [ ← Finset.card_union_of_disjoint, ← h_deg, SimpleGraph.card_incidenceFinset_eq_degree ];
            exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₁ |>.2 ( Finset.mem_filter.mp hx₂ |>.1 );
          have h_deg : (H.incidenceFinset v \ T).card + (T.filter (fun e => e ∈ H.incidenceFinset v)).card = H.degree v := by
            rw [ ← Finset.card_union_of_disjoint ];
            · convert SimpleGraph.card_incidenceFinset_eq_degree H v using 2 ; ext e ; by_cases he : e ∈ T <;> simp +decide [ he ];
            · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₁ |>.2 ( Finset.mem_filter.mp hx₂ |>.1 );
          grind;
        cases hdeg v <;> simp_all +decide [ IsEdgeSplit ];
        grind +qlia;
      · intro v
        have h_deg_K : (toggled K T).degree v = K.degree v + (Finset.card (T.filter (fun e => e ∈ H.incidenceFinset v))) - (Finset.card (T.filter (fun e => e ∈ K.incidenceFinset v))) := by
          have h_deg_K : (toggled K T).degree v = (K.incidenceFinset v \ T.filter (fun e => e ∈ K.incidenceFinset v)).card + (T.filter (fun e => e ∈ H.incidenceFinset v)).card := by
            have h_deg_K : (toggled K T).incidenceFinset v = (K.incidenceFinset v \ T.filter (fun e => e ∈ K.incidenceFinset v)) ∪ (T.filter (fun e => e ∈ H.incidenceFinset v)) := by
              ext e; simp [toggled];
              simp +decide [ SimpleGraph.incidenceSet, symmDiff ];
              by_cases he : e ∈ K.edgeSet <;> by_cases he' : e ∈ T <;> simp +decide [ he, he' ];
              · intro he'' hv; have := hsplit.2.1; simp_all +decide [ SimpleGraph.adj_comm ] ;
                rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
              · have := hsplit.1; simp_all +decide [ SimpleGraph.edgeSet ] ;
                cases e ; simp_all +decide [ edgeSetEmbedding ];
                have := hT he'; simp_all +decide [ Sym2.fromRel ] ;
                exact fun h => by rintro rfl; exact this.ne rfl;
            rw [ ← Finset.card_union_of_disjoint, ← h_deg_K, SimpleGraph.card_incidenceFinset_eq_degree ];
            simp +contextual [ Finset.disjoint_left ];
          rw [ h_deg_K, Finset.card_sdiff ];
          rw [ Finset.inter_eq_left.mpr ];
          · rw [ Nat.sub_add_comm ];
            · rw [ SimpleGraph.card_incidenceFinset_eq_degree ];
            · exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( SimpleGraph.card_incidenceFinset_eq_degree K v |> le_of_eq );
          · exact fun x hx => Finset.mem_filter.mp hx |>.2;
        cases hdeg v <;> simp_all +decide [ IsEdgeSplit ];
        grind;
      · intro v
        have h_deg_sum : (toggled H T).degree v + (toggled K T).degree v = H.degree v + K.degree v := by
          have h_deg_sum : (toggled H T).degree v + (toggled K T).degree v = (G.degree v) := by
            have h_adj : ∀ u, (toggled H T).Adj v u ∨ (toggled K T).Adj v u ↔ G.Adj v u := by
              intro u
              simp [toggled, hsplit.1];
              by_cases hvu : v = u <;> simp +decide [ hvu, symmDiff ];
              by_cases h : H.Adj v u <;> by_cases h' : K.Adj v u <;> simp +decide [ h, h' ];
              · exact absurd ( hsplit.2.1 v u h ) ( by simp +decide [ h' ] );
              · tauto;
              · exact em _;
              · intro h''; have := hT h''; simp_all +decide [ SimpleGraph.adj_comm ] ;
                have := hsplit.1 u v; simp_all +decide [ SimpleGraph.adj_comm ] ;
            have h_disjoint : Disjoint ((toggled H T).neighborFinset v) ((toggled K T).neighborFinset v) := by
              simp +decide [ Finset.disjoint_left, SimpleGraph.neighborFinset ];
              intro u hu hv; have := hsplit.2.1 v u; simp_all +decide [ toggled ] ;
              cases hu.1 <;> cases hv <;> simp_all +decide [ symmDiff ];
              have := hT ( by tauto : s(v, u) ∈ T ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
              have := hsplit.1 u v; simp_all +decide [ SimpleGraph.adj_comm ] ;
            convert congr_arg Finset.card ( show ( toggled H T ).neighborFinset v ∪ ( toggled K T ).neighborFinset v = G.neighborFinset v from ?_ ) using 1;
            · rw [ Finset.card_union_of_disjoint h_disjoint, SimpleGraph.degree, SimpleGraph.degree ];
            · ext u; simp [h_adj];
          exact h_deg_sum.trans ( hsplit.2.2.2.2.2.2 v ▸ rfl );
        exact h_deg_sum.trans ( hsplit.2.2.2.2.2.2 v )

/-- LADDER-PIN 1b (§0, last paragraph).  Two splits differ by a valid toggle,
so non-minimality is exactly the existence of a strict valid toggle. -/
lemma not_minimal_iff_exists_strict_toggle
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) :
    (¬ IsOddCycleMinimalSplit G H K) ↔
      ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
  constructor <;> intro h;
  · -- By definition of `IsOddCycleMinimalSplit`, there exist `K₀` and `K₁` such that `IsEdgeSplit G K₀ K₁` and `oddCycleCount K₀ + oddCycleCount K₁ < oddCycleCount H + oddCycleCount K`.
    obtain ⟨K₀, K₁, hK₀K₁, hK₀K₁_lt⟩ : ∃ K₀ K₁ : SimpleGraph V, ∃ j₀ : DecidableRel K₀.Adj, ∃ j₁ : DecidableRel K₁.Adj, IsEdgeSplit G K₀ K₁ ∧ oddCycleCount K₀ + oddCycleCount K₁ < oddCycleCount H + oddCycleCount K := by
      contrapose! h; unfold IsOddCycleMinimalSplit at *; aesop;
    obtain ⟨ j₁, hK₀K₁, hK₀K₁_lt ⟩ := hK₀K₁_lt;
    refine' ⟨ symmDiff H.edgeFinset K₀.edgeFinset, _, _ ⟩;
    · refine' ⟨ _, _ ⟩;
      · simp +decide [ symmDiff, Set.subset_def ];
        rintro ⟨ u, v ⟩ ( ⟨ hu, hv ⟩ | ⟨ hu, hv ⟩ ) <;> simp_all +decide [ IsEdgeSplit ];
        have := hK₀K₁.1 u v; simp_all +decide [ SimpleGraph.adj_comm ] ;
      · convert hK₀K₁ using 1;
        · ext u v; simp +decide [ toggled, symmDiff ] ;
          grind;
        · ext u v; simp +decide [ toggled, symmDiff ] ;
          cases hsplit ; cases hK₀K₁ ; simp_all +decide [ SimpleGraph.adj_comm ];
          grind +splitImp;
    · convert hK₀K₁_lt using 1;
      unfold IsStrictToggle;
      rw [ show toggled H ( symmDiff H.edgeFinset K₀.edgeFinset ) = K₀ from ?_, show toggled K ( symmDiff H.edgeFinset K₀.edgeFinset ) = K₁ from ?_ ];
      · ext u v; simp +decide [ toggled, symmDiff ] ;
        have := hsplit.1; have := hK₀K₁.1; simp_all +decide [ IsEdgeSplit ] ;
        grind +splitImp;
      · ext u v; simp +decide [ toggled, symmDiff ] ;
        by_cases hu : H.Adj u v <;> by_cases hv : K₀.Adj u v <;> simp +decide [ hu, hv ];
  · obtain ⟨ T, hT₁, hT₂ ⟩ := h; unfold IsOddCycleMinimalSplit; simp_all +decide ;
    exact ⟨ _, _, ⟨ _, _, hT₁.2 ⟩, hT₂ ⟩

/-- PROVED (ladder item 2, Lemma 1.1).  If every minimal split of `G` admits a
clean transversal, then every bad split has a strictly smaller split — i.e. the
descent core's conclusion.  (Uses the kernel-proved `exists_oddCycleMinimal_split`.) -/
lemma descent_of_no_bad_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hgood : ∀ (M₀ M₁ : SimpleGraph V)
      (j₀ : DecidableRel M₀.Adj) (j₁ : DecidableRel M₁.Adj),
      IsOddCycleMinimalSplit G M₀ M₁ →
      ∃ d : Finset V → V,
        (∀ S ∈ oddCycleSupports M₀, d S ∈ S ∧ CleanVertex G M₁ (d S)) ∧
        (∀ S' ∈ oddCycleSupports M₁,
          ¬ (S' ⊆ (oddCycleSupports M₀).image d)))
    (H₀ H₁ : SimpleGraph V)
    [i₀ : DecidableRel H₀.Adj] [i₁ : DecidableRel H₁.Adj]
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hbad :
      ¬ ∃ d : Finset V → V,
        (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
        (∀ S' ∈ oddCycleSupports H₁,
          ¬ (S' ⊆ (oddCycleSupports H₀).image d))) :
    ∃ (K₀ K₁ : SimpleGraph V)
      (_ : DecidableRel K₀.Adj) (_ : DecidableRel K₁.Adj),
      IsEdgeSplit G K₀ K₁ ∧
      oddCycleCount K₀ + oddCycleCount K₁ <
        oddCycleCount H₀ + oddCycleCount H₁ := by
  obtain ⟨M₀, M₁, j₀, j₁, hmin⟩ := exists_oddCycleMinimal_split G hdeg
  by_cases hlt : oddCycleCount M₀ + oddCycleCount M₁ <
      oddCycleCount H₀ + oddCycleCount H₁
  · exact ⟨M₀, M₁, j₀, j₁, hmin.1, hlt⟩
  · exfalso
    have hle := hmin.2 H₀ H₁ i₀ i₁ hsplit
    refine hbad (hgood H₀ H₁ i₀ i₁ ⟨hsplit, ?_⟩)
    intro K₀ K₁ k₀ k₁ hK
    have := hmin.2 K₀ K₁ k₀ k₁ hK
    omega

/-! ## Short-toggle laws at a minimal split (STRIKE-A §2) -/

/-
Auxiliary (H-side of the C1 one-edge toggle).  Deleting a cycle edge
`s(z, z')` of an odd `H`-cycle from a max-degree-≤2 graph strictly drops the
odd-cycle count: the cycle through `z` is destroyed and nothing new is created.
-/
private lemma oddCycleCount_toggle_H_lt
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg2 : ∀ v, H.degree v ≤ 2)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {z z' : V} (hz : z ∈ w.support) (hadj : H.Adj z z') :
    oddCycleCount (toggled H {s(z, z')}) < oddCycleCount H := by
  -- By definition of toggled, we have that toggled H {s(z, z')} = H.deleteEdges {s(z, z')}.
  have h_toggled_eq_delete : toggled H {s(z, z')} = H.deleteEdges {s(z, z')} := by
    ext u v; simp [toggled, hadj];
    by_cases hu : u = v <;> simp +decide [ hu, hadj, symmDiff ];
  convert oddCycleCount_deleteEdges_lt H hdeg2 hw hodd hadj _;
  grind +suggestions

/-
Auxiliary: an odd cycle of `toggled K {s(z,z')}` that uses the new edge
`s(z,z')` yields, after removing that edge, an even-length `K`-path from `z` to
`z'` (the rest of the cycle, transferred back to `K`).
-/
private lemma even_path_of_cycle_through_edge
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {z z' : V} (hzz' : z ≠ z') (hnadj : ¬ K.Adj z z')
    {y : V} {c : (toggled K {s(z, z')}).Walk y y} (hc : c.IsCycle)
    (hodd : Odd c.length) (he : s(z, z') ∈ c.edges) :
    ∃ p : K.Walk z z', p.IsPath ∧ Even p.length := by
  have hz : z ∈ c.support := c.fst_mem_support_of_mem_edges he
  let d : (toggled K {s(z, z')}).Walk z z := c.rotate hz
  have hdc : d.IsCycle := by
    change (c.rotate hz).IsCycle
    exact hc.rotate hz
  have hde : s(z, z') ∈ d.edges := by
    change s(z, z') ∈ (c.rotate hz).edges
    exact (c.rotate_edges hz).mem_iff.mpr he
  have hdlen : d.length = c.length := by
    simpa only [d, SimpleGraph.Walk.length_edges] using
      (c.rotate_edges hz).perm.length_eq
  have hdodd : Odd d.length := by
    rw [hdlen]
    exact hodd
  have horient : d.snd = z' ∨ d.penultimate = z' := by
    have hadj : d.toSubgraph.Adj z z' :=
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hde
    have hmem : z' ∈ d.toSubgraph.neighborSet z := hadj
    rw [hdc.neighborSet_toSubgraph_endpoint] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hmem
  obtain ⟨e, hec, heodd, hesnd⟩ :
      ∃ e : (toggled K {s(z, z')}).Walk z z,
        e.IsCycle ∧ Odd e.length ∧ e.snd = z' := by
    rcases horient with hsnd | hpen
    · exact ⟨d, hdc, hdodd, hsnd⟩
    · exact ⟨d.reverse, hdc.reverse, by simpa using hdodd, by simpa using hpen⟩
  let t : (toggled K {s(z, z')}).Walk z' z := e.tail.copy hesnd rfl
  have htpath : t.IsPath := by
    simpa only [t, SimpleGraph.Walk.isPath_copy] using hec.isPath_tail
  have htlen : t.length + 1 = e.length := by
    simpa only [t, SimpleGraph.Walk.length_copy] using
      e.length_tail_add_one hec.not_nil
  have hefirst : s(z, e.snd) ∉ e.tail.edges := by
    have hcons :
        (SimpleGraph.Walk.cons (e.adj_snd hec.not_nil) e.tail).IsCycle := by
      rw [e.cons_tail_eq hec.not_nil]
      exact hec
    exact ((SimpleGraph.Walk.cons_isCycle_iff e.tail
      (e.adj_snd hec.not_nil)).mp hcons).2
  have htnew : s(z, z') ∉ t.edges := by
    simpa only [t, SimpleGraph.Walk.edges_copy, hesnd] using hefirst
  have htrans : ∀ f ∈ t.edges, f ∈ K.edgeSet := by
    intro f hf
    have hfT := t.edges_subset_edgeSet hf
    unfold toggled at hfT
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hfT
    have hfSymm : f ∈ symmDiff K.edgeFinset {s(z, z')} := hfT.1
    rcases Finset.mem_symmDiff.mp hfSymm with hK | hnew
    · exact SimpleGraph.mem_edgeFinset.mp hK.1
    · have hfeq : f = s(z, z') := Finset.mem_singleton.mp hnew.1
      exact (htnew (hfeq ▸ hf)).elim
  have hteven : Even t.length := by
    rcases heodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  let q : K.Walk z' z := t.transfer K htrans
  have hqpath : q.IsPath := by
    dsimp only [q]
    exact htpath.transfer htrans
  exact ⟨q.reverse, hqpath.reverse,
    by simpa only [q, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_transfer] using hteven⟩

/-
Auxiliary (K-side of the C1 one-edge toggle).  Adding the edge `s(z, z')`
between two non-adjacent vertices of a max-degree-≤2 graph `K` does not create a
new odd cycle unless `z, z'` are the ends of an even-length `K`-path; hence when
no such even path exists the odd-cycle count does not increase.
-/
private lemma oddCycleCount_toggle_K_le
    (K : SimpleGraph V) [DecidableRel K.Adj] (hdeg2 : ∀ v, K.degree v ≤ 2)
    {z z' : V} (hzz' : z ≠ z') (hnadj : ¬ K.Adj z z')
    (hno : ¬ ∃ p : K.Walk z z', p.IsPath ∧ Even p.length) :
    oddCycleCount (toggled K {s(z, z')}) ≤ oddCycleCount K := by
  refine' Finset.card_le_card _;
  intro D;
  simp +decide [ oddCycleSupports ];
  intro x w hw hw' hw'';
  by_cases h : s(z, z') ∈ w.edges;
  · contrapose! hno;
    apply even_path_of_cycle_through_edge K hzz' hnadj hw hw' h;
  · have h_edges : ∀ e ∈ w.edges, e ∈ K.edgeSet := by
      intro e he; have := w.edges_subset_edgeSet he; simp_all +decide [ toggled ] ;
      cases this.1 <;> aesop;
    have h_walk : ∃ w' : K.Walk x x, w'.IsCycle ∧ w'.length = w.length ∧ w'.support.toFinset = w.support.toFinset := by
      exact ⟨ w.transfer K h_edges, by
        convert hw.transfer _, by
        rw [SimpleGraph.Walk.length_transfer], by
        ext; simp [SimpleGraph.Walk.support_transfer] ⟩;
    grind

/-- Auxiliary: the degree of `toggled K {s(z,z')}` (adding a new edge `s(z,z')`
with `z ≠ z'` and `¬ K.Adj z z'`) is the `K`-degree, plus one at `z` and `z'`. -/
private lemma degree_toggle_add_edge
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {z z' : V} (hzz' : z ≠ z') (hnadj : ¬ K.Adj z z') (v : V) :
    (toggled K {s(z, z')}).degree v
      = K.degree v + (if v = z ∨ v = z' then 1 else 0) := by
  convert congr_arg Finset.card ( show (toggled K {s(z, z')}).neighborFinset v = if v = z then K.neighborFinset v ∪ {z'} else if v = z' then K.neighborFinset v ∪ {z} else K.neighborFinset v from ?_ ) using 1;
  · split_ifs <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    rw [ Finset.card_insert_of_notMem ] <;> simp_all +decide [ SimpleGraph.adj_comm ];
  · ext w;
    split_ifs <;> simp_all +decide [ toggled, SimpleGraph.fromEdgeSet_adj ];
    · by_cases hw : w = z' <;> simp_all +decide [ symmDiff ];
      exact fun h => by rintro rfl; exact h.ne rfl;
    · constructor <;> intro h <;> simp_all +decide [ symmDiff ];
      aesop;
    · by_cases hvw : K.Adj v w <;> simp_all +decide [ SimpleGraph.adj_comm, symmDiff ];
      exact hvw.ne

/-
Auxiliary (validity of the C1 one-edge move; direct proof of the relevant
special case of `toggle_valid_iff`).  Toggling the single `H`-edge `s(z, z')`
between two `(H‑degree 2, K‑degree 1)` vertices of a split yields a split again.
-/
private lemma single_edge_toggle_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {z z' : V} (hadj : H.Adj z z') (hKz : K.degree z = 1) (hKz' : K.degree z' = 1) :
    IsValidToggle G H K {s(z, z')} := by
  refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ IsEdgeSplit ];
  · intro u v; by_cases hu : u = v <;> simp +decide [ *, toggled ] ;
    grind +suggestions;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · intro u v hu hv; simp_all +decide [ toggled ] ;
      by_cases h : s(u, v) = s(z, z') <;> simp_all +decide [ symmDiff ];
    · intro u v; simp +decide [ toggled, SimpleGraph.fromEdgeSet_adj, hsplit.1 ] ;
      simp +decide [ symmDiff, hadj ];
      tauto;
    · intro u v huv; simp_all +decide [ toggled ] ;
      grind +suggestions;
    · intro v
      simp [toggled, SimpleGraph.degree, SimpleGraph.neighborFinset];
      refine' le_trans ( Finset.card_le_card _ ) ( hsplit.2.2.2.2.1 v );
      intro x hx; simp_all +decide [ SimpleGraph.neighborSet, symmDiff ] ;
    · refine' ⟨ _, _ ⟩;
      · intro v
        have h_deg : (toggled K {s(z, z')}).degree v = K.degree v + (if v = z ∨ v = z' then 1 else 0) := by
          apply degree_toggle_add_edge K hadj.ne (hsplit.2.1 z z' hadj) v;
        grind +splitIndPred;
      · intro v
        have h_deg_H : (toggled H {s(z, z')}).degree v = H.degree v - (if v = z ∨ v = z' then 1 else 0) := by
          convert degree_deleteEdges_single H z z' hadj v using 1;
          congr! 1;
          ext u v; simp [toggled, hadj]; by_cases hu : u = v <;> simp [hu, hadj, symmDiff]
        have h_deg_K : (toggled K {s(z, z')}).degree v = K.degree v + (if v = z ∨ v = z' then 1 else 0) := by
          convert degree_toggle_add_edge K hadj.ne ( hsplit.2.1 z z' hadj ) v using 1
        simp [h_deg_H, h_deg_K];
        split_ifs <;> simp_all +decide [ ← hsplit.2.2.2.2.2.2 ];
        rcases ‹_› with ( rfl | rfl ) <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
        · rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ z', by simpa using hadj ⟩ ) ];
        · rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ z, by simpa [ SimpleGraph.adj_comm ] using hadj ⟩ ) ]

/-- LADDER-PIN 3 (Lemma 2.1, "C1").  Two adjacent degree-3 vertices on an odd
`H`-cycle of a minimal split are the two ends of one common `K`-path of EVEN
length. -/
lemma C1_even_copath_of_minimal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {z z' : V} (hz : z ∈ w.support) (hz' : z' ∈ w.support)
    (hadj : H.Adj z z')
    (hz3 : G.degree z = 3) (hz'3 : G.degree z' = 3) :
    ∃ p : K.Walk z z', p.IsPath ∧ Even p.length := by
  by_contra! h_no_even_path;
  have hKz : K.degree z = 1 := by
    have h2 := degree_eq_two_of_mem_cycle_support H hmin.1.2.2.2.2.1 hw hz
    have := hmin.1.2.2.2.2.2.2 z; omega
  have hKz' : K.degree z' = 1 := by
    have h2 := degree_eq_two_of_mem_cycle_support H hmin.1.2.2.2.2.1 hw hz'
    have := hmin.1.2.2.2.2.2.2 z'; omega
  have h_valid : IsValidToggle G H K {s(z, z')} :=
    single_edge_toggle_valid G H K hmin.1 hadj hKz hKz'
  have h_strict : IsStrictToggle H K {s(z, z')} := by
    refine' lt_of_lt_of_le ( add_lt_add_of_lt_of_le ( oddCycleCount_toggle_H_lt H _ hw hodd hz hadj ) ( oddCycleCount_toggle_K_le K _ _ _ _ ) ) _;
    any_goals tauto;
    · exact hmin.1.2.2.2.2.1;
    · exact hmin.1.2.2.2.2.2.1;
    · exact hadj.ne;
    · exact hmin.1.2.1 _ _ hadj;
  have hge := hmin.2 (toggled H {s(z, z')}) (toggled K {s(z, z')})
    (instDecToggled H _) (instDecToggled K _) h_valid.2
  exact absurd h_strict (not_lt.mpr hge)

/-
Auxiliary handshake bound for `no_three_consecutive_deg3`.  In any finite
graph the sum of degrees over the connected component (reachable set) of a
vertex `z` is at least twice the size of that component minus two — because the
connected induced subgraph on that set has at least `card − 1` edges.
-/
private lemma deg_sum_reachable_component_ge
    (K : SimpleGraph V) [DecidableRel K.Adj] (z : V) :
    2 * (Finset.univ.filter (fun v => K.Reachable z v)).card
      ≤ (∑ v ∈ Finset.univ.filter (fun v => K.Reachable z v), K.degree v) + 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Finset V, C = Finset.univ.filter (fun v => K.Reachable z v) ∧ C.Nonempty := by
    exact ⟨ _, rfl, ⟨ z, by simp +decide [ SimpleGraph.Reachable.refl ] ⟩ ⟩;
  have h_induced_connected : (K.induce (↑C)).Connected := by
    rw [ SimpleGraph.connected_iff_exists_forall_reachable ];
    use ⟨ z, by aesop ⟩;
    rintro ⟨ w, hw ⟩;
    obtain ⟨ p ⟩ := ( show K.Reachable z w from by aesop );
    induction' p with u v p ih;
    · exact SimpleGraph.Reachable.refl _;
    · rename_i h₁ h₂ h₃;
      have h_induced_walk : (induce (↑C) K).Reachable ⟨v, by
        aesop⟩ ⟨p, by
        exact hC.1.symm ▸ by simpa using h₁.reachable⟩ := by
        exact ⟨ SimpleGraph.Walk.cons ( by aesop ) SimpleGraph.Walk.nil ⟩
      generalize_proofs at *;
      exact h_induced_walk.trans ( h₃ ⟨ by
        ext; simp [hC];
        exact ⟨ fun h => h₁.symm.reachable.trans h, fun h => h₁.reachable.trans h ⟩, hC.2 ⟩ hw );
  have h_induced_edges : (K.induce (↑C)).edgeFinset.card ≥ C.card - 1 := by
    have h_induced_card : (Nat.card (↑C)) ≤ (Nat.card (K.induce (↑C)).edgeSet) + 1 := by
      convert h_induced_connected.card_vert_le_card_edgeSet_add_one using 1;
    simp_all +decide [ Nat.card_eq_fintype_card ];
    convert h_induced_card using 1;
    · rw [ Fintype.subtype_card ];
    · simp +decide [ SimpleGraph.edgeFinset ];
  have h_induced_degrees : ∑ v ∈ C, K.degree v = ∑ v : C, (K.induce (↑C)).degree v := by
    refine' Finset.sum_bij ( fun v hv => ⟨ v, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    intro v hv; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr; ext; simp +decide [ hC.1 ] ;
    exact ⟨ fun h => ⟨ by exact SimpleGraph.Reachable.trans ( by aesop ) ( SimpleGraph.Adj.reachable h ), h ⟩, fun ⟨ _, h ⟩ => h ⟩;
  have := SimpleGraph.sum_degrees_eq_twice_card_edges ( K.induce ( ↑C ) ) ; simp_all +decide [ Finset.sum_add_distrib, two_mul ] ;
  linarith

/-- LADDER-PIN 3b (Corollary 2.2).  No three consecutive degree-3 vertices on
an odd `H`-cycle of a minimal split. -/
lemma no_three_consecutive_deg3
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {a z b : V} (ha : a ∈ w.support) (hz : z ∈ w.support) (hb : b ∈ w.support)
    (hab : a ≠ b) (haz : H.Adj a z) (hzb : H.Adj z b)
    (ha3 : G.degree a = 3) (hz3 : G.degree z = 3) (hb3 : G.degree b = 3) :
    False := by
  have h_deg : H.degree a = 2 ∧ K.degree a = 1 ∧ H.degree z = 2 ∧ K.degree z = 1 ∧ H.degree b = 2 ∧ K.degree b = 1 := by
    have h_deg : H.degree a = 2 ∧ H.degree z = 2 ∧ H.degree b = 2 := by
      exact ⟨ degree_eq_two_of_mem_cycle_support H hmin.1.2.2.2.2.1 hw ha, degree_eq_two_of_mem_cycle_support H hmin.1.2.2.2.2.1 hw hz, degree_eq_two_of_mem_cycle_support H hmin.1.2.2.2.2.1 hw hb ⟩;
    have := hmin.1.2.2.2.2.2.2 a; have := hmin.1.2.2.2.2.2.2 z; have := hmin.1.2.2.2.2.2.2 b; simp_all +decide ;
    grind;
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : K.Walk a z, p₁.IsPath ∧ Even p₁.length := by
    apply C1_even_copath_of_minimal G H K hdeg hmin hw hodd ha hz haz ha3 hz3
  obtain ⟨p₂, hp₂⟩ : ∃ p₂ : K.Walk z b, p₂.IsPath ∧ Even p₂.length := by
    apply C1_even_copath_of_minimal G H K hdeg hmin hw hodd hz hb hzb hz3 hb3;
  have h_card : 3 ≤ (Finset.univ.filter (fun v => K.Reachable z v)).card := by
    have h_card : {a, z, b} ⊆ Finset.univ.filter (fun v => K.Reachable z v) := by
      simp +decide [ Finset.insert_subset_iff, SimpleGraph.Reachable ];
      exact ⟨ ⟨ p₁.reverse ⟩, ⟨ SimpleGraph.Walk.nil ⟩, ⟨ p₂ ⟩ ⟩;
    refine' le_trans _ ( Finset.card_mono h_card );
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ * ];
    · rintro rfl; simp_all +decide;
    · rintro rfl; simp_all +decide [ SimpleGraph.adj_comm ];
  have h_sum : ∑ v ∈ Finset.univ.filter (fun v => K.Reachable z v), (2 - K.degree v) ≥ 3 := by
    have h_sum : ∑ v ∈ ({a, z, b} : Finset V), (2 - K.degree v) ≥ 3 := by
      rw [ Finset.sum_insert, Finset.sum_insert ] <;> simp +decide [ * ];
      · rintro rfl; simp_all +decide;
      · exact haz.ne;
    refine' le_trans h_sum ( Finset.sum_le_sum_of_subset _ );
    simp +decide [ Finset.insert_subset_iff, SimpleGraph.Reachable ];
    exact ⟨ ⟨ p₁.reverse ⟩, ⟨ SimpleGraph.Walk.nil ⟩, ⟨ p₂ ⟩ ⟩;
  have h_sum : ∑ v ∈ Finset.univ.filter (fun v => K.Reachable z v), K.degree v = 2 * (Finset.univ.filter (fun v => K.Reachable z v)).card - ∑ v ∈ Finset.univ.filter (fun v => K.Reachable z v), (2 - K.degree v) := by
    rw [ Nat.sub_eq_of_eq_add ];
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => add_tsub_cancel_of_le <| show K.degree x ≤ 2 from hmin.1.2.2.2.2.2.1 x ] ; simp +decide [ mul_comm ];
  have := deg_sum_reachable_component_ge K z; simp_all +decide ;
  omega

/-- Adjacency in the toggled graph: symmetric-difference of the edge relation. -/
lemma toggled_adj_split (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Sym2 V)) (a b : V) :
    (toggled H T).Adj a b ↔
      a ≠ b ∧ ((H.Adj a b ∧ s(a, b) ∉ T) ∨ (¬ H.Adj a b ∧ s(a, b) ∈ T)) := by
  unfold toggled; simp +decide [ *, SimpleGraph.fromEdgeSet_adj ] ;
  simp +decide [ symmDiff, and_comm ]

/-- A cycle edge, once deleted, still connects its endpoints via the rest of the
cycle. -/
lemma reachable_deleteEdges_of_cycle_edge
    (G : SimpleGraph V) {a b : V} (c : G.Walk a a) (hc : c.IsCycle)
    (he : s(a, b) ∈ c.edges) :
    (G.deleteEdges {s(a, b)}).Reachable a b := by
  obtain ⟨c₁, c₂, hc₁, hc₂⟩ : ∃ c₁ : G.Walk a b, ∃ c₂ : G.Walk b a, c = c₁.append c₂ := by
    obtain ⟨c₁, c₂, hc₁, hc₂⟩ : ∃ c₁ : G.Walk a b, ∃ c₂ : G.Walk b a, c = c₁.append c₂ := by
      have hb_in_support : b ∈ c.support := by
        grind +suggestions
      exact ⟨ c.takeUntil b hb_in_support, c.dropUntil b hb_in_support, by simp +decide [ SimpleGraph.Walk.take_spec ] ⟩;
    use c₁, c₂;
  by_cases h : s(a, b) ∈ c₁.edges <;> simp_all +decide [ SimpleGraph.Walk.isCycle_def ];
  · have h_c₂_reachable : (G.deleteEdges {s(a, b)}).Reachable b a := by
      have h_c₂_reachable : ∀ e ∈ c₂.edges, e ≠ s(a, b) := by
        intro e he; have := hc.1; simp_all +decide [ SimpleGraph.Walk.isTrail_def ] ;
        grind +splitIndPred;
      have h_c₂_reachable : ∃ c₂' : (G.deleteEdges {s(a, b)}).Walk b a, True := by
        have h_c₂_reachable : ∀ {u v : V} {p : G.Walk u v}, (∀ e ∈ p.edges, e ≠ s(a, b)) → ∃ p' : (G.deleteEdges {s(a, b)}).Walk u v, True := by
          intros u v p hp; induction' p with u v p ih <;> simp_all +decide [ SimpleGraph.Walk.cons ] ;
          exact ⟨ SimpleGraph.Walk.cons ( by aesop ) ( Classical.arbitrary _ ) ⟩;
        exact h_c₂_reachable ‹_›;
      exact ⟨ h_c₂_reachable.choose ⟩;
    exact h_c₂_reachable.symm;
  · have h_c1_edges : ∀ e ∈ c₁.edges, e ∈ (G.deleteEdges {s(a, b)}).edgeSet := by
      simp_all +decide [ SimpleGraph.deleteEdges ];
      exact fun e he => ⟨ by simpa using c₁.edges_subset_edgeSet he, by aesop ⟩;
    grind +suggestions

/-- K-side surgery: a two-edge toggle that deletes the unique `K`-edge `s(z,u)`
at a `K`-degree-1 vertex `z` and adds `s(z,z')` cannot create new odd cycles. -/
lemma oddCycleSupports_toggled_isolated
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {z u z' : V} (hzu : K.Adj z u) (hzz' : ¬ K.Adj z z')
    (hz'z : z' ≠ z) (hKz : K.degree z = 1) :
    oddCycleSupports (toggled K {s(z, z'), s(z, u)}) ⊆ oddCycleSupports K := by
  -- z has the single toggled-neighbour z', so it lies on no toggled odd cycle.
  have hKn : ∀ b, K.Adj z b ↔ b = u := by
    have hsingle : K.neighborFinset z = {u} := by
      have hc := SimpleGraph.card_neighborFinset_eq_degree K z
      rw [hKz] at hc
      rw [Finset.card_eq_one] at hc
      obtain ⟨a, ha⟩ := hc
      have : u ∈ K.neighborFinset z := by simpa [SimpleGraph.mem_neighborFinset] using hzu
      rw [ha] at this ⊢; rw [Finset.mem_singleton] at this; rw [this]
    intro b
    rw [← SimpleGraph.mem_neighborFinset, hsingle, Finset.mem_singleton]
  have hdegz : (toggled K {s(z, z'), s(z, u)}).degree z = 1 := by
    have hne : (toggled K {s(z, z'), s(z, u)}).neighborFinset z = {z'} := by
      ext b
      rw [SimpleGraph.mem_neighborFinset, toggled_adj_split, Finset.mem_singleton]
      constructor
      · rintro ⟨hzb, hcase | hcase⟩
        · obtain ⟨hK, hnT⟩ := hcase
          rw [hKn] at hK; subst hK; exact absurd (by simp) hnT
        · obtain ⟨hnK, hT⟩ := hcase
          simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
          rcases hT with (h | h) | (h | h) <;> aesop
      · rintro rfl
        exact ⟨Ne.symm hz'z, Or.inr ⟨hzz', by simp⟩⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hne, Finset.card_singleton]
  intro S hS
  simp only [oddCycleSupports, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  obtain ⟨y, w, hw₁, hw₂, rfl⟩ := hS
  have hznotin : z ∉ w.support := not_mem_cycle_of_degree_one _ hdegz w hw₁
  have h_edge : ∀ e ∈ w.edges, e ∈ K.edgeSet := by
    refine Sym2.ind (fun a b he => ?_)
    have hfst : a ∈ w.support := w.fst_mem_support_of_mem_edges he
    have hsnd : b ∈ w.support := w.snd_mem_support_of_mem_edges he
    have haz : a ≠ z := fun h => hznotin (h ▸ hfst)
    have hbz : b ≠ z := fun h => hznotin (h ▸ hsnd)
    have hmem := w.edges_subset_edgeSet he
    rw [SimpleGraph.mem_edgeSet, toggled_adj_split] at hmem
    rcases hmem.2 with ⟨hK, _⟩ | ⟨_, hT⟩
    · exact hK
    · simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
      rcases hT with (⟨rfl, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨_, rfl⟩)
      · exact absurd rfl haz
      · exact absurd rfl hbz
      · exact absurd rfl haz
      · exact absurd rfl hbz
  exact ⟨y, w.transfer K h_edge, hw₁.transfer h_edge,
    by rwa [SimpleGraph.Walk.length_transfer], by rw [SimpleGraph.Walk.support_transfer]⟩

set_option maxHeartbeats 1600000 in
/-- H-side surgery: a two-edge toggle deleting a cycle edge `s(z,z')` and adding
`s(z,u)` with `u` off the cycle produces no odd cycle through the new edge. -/
lemma oddCycleSupports_toggled_cross
    (H : SimpleGraph V) [DecidableRel H.Adj] (hHle : ∀ v, H.degree v ≤ 2)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle)
    {z z' u : V} (hz : z ∈ w.support) (hzz' : H.Adj z z')
    (hzu : ¬ H.Adj z u) (hu : u ∉ w.support) :
    oddCycleSupports (toggled H {s(z, z'), s(z, u)})
      ⊆ oddCycleSupports (H.deleteEdges {s(z, z')}) := by
  set M : SimpleGraph V := toggled H {s(z, z'), s(z, u)}
  set T : Finset (Sym2 V) := {s(z, z'), s(z, u)}
  have hMdel : M.deleteEdges {s(z, u)} = H.deleteEdges {s(z, z')} := by
    ext a b; simp [M, toggled_adj_split, SimpleGraph.deleteEdges_adj] ;
    by_cases ha : a = z <;> by_cases hb : b = z <;> by_cases ha' : a = z' <;> by_cases hb' : b = z' <;> by_cases ha'' : a = u <;> by_cases hb'' : b = u <;> simp_all +decide [ SimpleGraph.adj_comm ];
    · exact fun _ => Ne.symm hb;
    · exact fun _ => Ne.symm hb';
    · exact fun _ => Ne.symm hb'';
    · exact fun h => h.ne
  generalize_proofs at *; (
  intro S hS
  obtain ⟨y, cyc, hcyc, hodd, hsupp⟩ : ∃ y, ∃ cyc : M.Walk y y, cyc.IsCycle ∧ Odd cyc.length ∧ cyc.support.toFinset = S := by
    unfold oddCycleSupports at hS; aesop;
  generalize_proofs at *; (
  have h_not_in_edges : s(z, u) ∉ cyc.edges := by
    intro h
    have hz_in_support : z ∈ cyc.support := by
      exact Walk.fst_mem_support_of_mem_edges cyc h
    generalize_proofs at *; (
    obtain ⟨cyc', hcyc', hrot⟩ : ∃ cyc' : M.Walk z z, cyc'.IsCycle ∧ s(z, u) ∈ cyc'.edges ∧ cyc'.length = cyc.length := by
      use cyc.rotate hz_in_support
      generalize_proofs at *; (
      simp_all +decide [ SimpleGraph.Walk.rotate ];
      refine' ⟨ _, _, _ ⟩
      all_goals generalize_proofs at *;
      · convert hcyc.rotate hz_in_support using 1;
      · have h_edge_in_rotated : s(z, u) ∈ (cyc.takeUntil z hz_in_support).edges ++ (cyc.dropUntil z hz_in_support).edges := by
          rw [ ← SimpleGraph.Walk.edges_append ] ; aesop;
        generalize_proofs at *; (
        grind);
      · rw [ add_comm, ← SimpleGraph.Walk.length_append ] ; aesop;)
    generalize_proofs at *; (
    have h_reachable : (M.deleteEdges {s(z, u)}).Reachable z u := by
      apply reachable_deleteEdges_of_cycle_edge M cyc' hcyc' hrot.left
    generalize_proofs at *; (
    have h_reachable_H : H.Reachable z u := by
      exact h_reachable.mono ( by rw [ hMdel ] ; exact SimpleGraph.deleteEdges_le _ )
    generalize_proofs at *; (
    exact hu ( cycle_support_closed_reachable H hHle hw hz h_reachable_H )))))
  generalize_proofs at *; (
  have h_edges_subset : ∀ e ∈ cyc.edges, e ∈ (H.deleteEdges {s(z, z')}).edgeSet := by
    intro e he; rw [ ← hMdel ] ; simp +decide [ he, h_not_in_edges ] ;
    exact ⟨ by simpa using cyc.edges_subset_edgeSet he, by rintro rfl; exact h_not_in_edges he ⟩
  generalize_proofs at *; (
  obtain ⟨cyc', hcyc'⟩ : ∃ cyc' : (H.deleteEdges {s(z, z')}).Walk y y, cyc'.IsCycle ∧ cyc'.support.toFinset = S ∧ Odd cyc'.length := by
    exact ⟨ cyc.transfer ( H.deleteEdges { s(z, z') } ) h_edges_subset, hcyc.transfer _, by simp [ hsupp ], by simpa [ hsupp ] using hodd ⟩
  generalize_proofs at *; (
  unfold oddCycleSupports; aesop;)))))

/-- LADDER-PIN 4 (Lemma 2.3, "C2", flanked form).  A degree-3 vertex on an odd
`H`-cycle with a degree-3 cycle-neighbour has an `H`-full poison target. -/
lemma C2_poison_target_Hfull_of_minimal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {z z' u : V} (hz : z ∈ w.support) (hz' : z' ∈ w.support)
    (hadj : H.Adj z z') (hz3 : G.degree z = 3) (hz'3 : G.degree z' = 3)
    (hzu : K.Adj z u) :
    H.degree u = 2 := by
  by_contra h_contra;
  have h_deg_u : H.degree u = 1 := by
    have := half_degree_bounds G H K hdeg hmin.1 u; have := half_degree_bounds G K H hdeg ( hmin.1.swap ) u; omega;
  -- Build the strict valid toggle T = {s(z,z'), s(z,u)} and contradict minimality.
  set T : Finset (Sym2 V) := {s(z, z'), s(z, u)} with hT_def
  have hT_valid : IsValidToggle G H K T := by
    refine' toggle_valid_iff G H K hdeg hmin.1 T _ |>.2 _;
    · simp_all +decide [ Set.insert_subset_iff ];
      exact ⟨ hmin.1.2.2.1 hadj, hmin.1.2.2.2.1 hzu ⟩;
    · intro v; by_cases hv : v = z <;> by_cases hv' : v = z' <;> by_cases hv'' : v = u <;> simp +decide [ *, SimpleGraph.incidenceSet ] ;
      all_goals simp_all +decide [ Finset.filter_insert, Finset.filter_singleton, SimpleGraph.adj_comm ];
      · have := hmin.1.2.1; simp_all +decide [ SimpleGraph.adj_comm ] ;
        grind +splitImp;
      · grind +suggestions;
      · split_ifs <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
        cases hdeg u <;> simp_all +decide [ Finset.card_eq_one ];
        have := hmin.1.2.2.2.2.2; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
        obtain ⟨ a, ha ⟩ := h_deg_u; simp_all +decide [ Finset.ext_iff ] ;
        have := this.2 u; simp_all +decide [ Finset.filter_eq', Finset.filter_or ] ;
        linarith [ ‹ ( ∀ v, Finset.card ( Finset.filter ( fun x => K.Adj v x ) Finset.univ ) ≤ 2 ) ∧ ∀ v, Finset.card ( Finset.filter ( fun x => H.Adj v x ) Finset.univ ) + Finset.card ( Finset.filter ( fun x => K.Adj v x ) Finset.univ ) = Finset.card ( Finset.filter ( fun x => G.Adj v x ) Finset.univ ) ›.1 u ]
  have hT_strict : IsStrictToggle H K T := by
    have hT_strict_H : oddCycleCount (toggled H T) ≤ oddCycleCount (H.deleteEdges {s(z, z')}) := by
      apply Finset.card_le_card; exact oddCycleSupports_toggled_cross H (fun v => (half_degree_bounds G H K hdeg hmin.1 v).2) hw hz hadj (by
      intro h; have := hmin.1; simp_all +decide [ IsEdgeSplit ] ;) (by
      intro hu; have := degree_eq_two_of_mem_cycle_support H ( fun v => ( half_degree_bounds G H K hdeg hmin.1 v ).2 ) hw hu; simp_all +decide ;)
    have hT_strict_K : oddCycleCount (toggled K T) ≤ oddCycleCount K := by
      apply Finset.card_le_card;
      apply oddCycleSupports_toggled_isolated K hzu (by
      have := hmin.1.2.1 z z' ; simp_all +decide [ SimpleGraph.adj_comm ] ;) (by
      exact hadj.ne.symm) (by
      have := hmin.1.2.2.2.2.2.2 z; simp_all +decide ;
      linarith [ show H.degree z = 2 from degree_eq_two_of_mem_cycle_support H ( fun v => ( half_degree_bounds G H K hdeg hmin.1 v ).2 ) hw hz ])
    have hT_strict_H_lt : oddCycleCount (H.deleteEdges {s(z, z')}) < oddCycleCount H := by
      apply oddCycleCount_deleteEdges_lt H (fun v => (half_degree_bounds G H K hdeg hmin.1 v).2) hw hodd hadj (cycle_edge_mem_of_adj H (fun v => (half_degree_bounds G H K hdeg hmin.1 v).2) hw hz hadj)
    have hT_strict_K_le : oddCycleCount (toggled K T) ≤ oddCycleCount K := by
      exact hT_strict_K
    exact (by
    exact lt_of_le_of_lt ( add_le_add hT_strict_H hT_strict_K ) ( by linarith ))
  have h_contra : ¬IsOddCycleMinimalSplit G H K := by
    exact not_minimal_iff_exists_strict_toggle G H K hdeg hmin.1 |>.2 ⟨ T, hT_valid, hT_strict ⟩
  contradiction

/-- LADDER-PIN 5 (Lemma 2.4, "C3").  A degree-4 cycle vertex with an exposed
`K`-edge and a degree-3 cycle-neighbour has the rigid structure: the exposed
edge lies on no odd `K`-cycle, and the `K − zp` component of `z` is an even
path ending at the flank. -/
lemma C3_flank_structure_of_minimal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {z p c : V} (hz : z ∈ w.support) (hz4 : G.degree z = 4)
    (hzp : K.Adj z p) (hpH : H.degree p = 1)
    (hc : c ∈ w.support) (hzc : H.Adj z c) (hc3 : G.degree c = 3) :
    (∀ (y : V) (cyc : K.Walk y y), cyc.IsCycle → Odd cyc.length →
      s(z, p) ∉ cyc.edges) ∧
    (∃ q : (K.deleteEdges {s(z, p)}).Walk z c, q.IsPath ∧ Even q.length) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- LADDER-PIN 5b (Corollary 2.5).  A degree-4 cycle vertex with an exposed
`K`-edge cannot have two degree-3 cycle-neighbours. -/
lemma at_most_one_deg3_flank
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length)
    {z p c₁ c₂ : V} (hz : z ∈ w.support) (hz4 : G.degree z = 4)
    (hzp : K.Adj z p) (hpH : H.degree p = 1)
    (hc₁ : c₁ ∈ w.support) (hc₂ : c₂ ∈ w.support) (hne : c₁ ≠ c₂)
    (hzc₁ : H.Adj z c₁) (hzc₂ : H.Adj z c₂)
    (hc₁3 : G.degree c₁ = 3) (hc₂3 : G.degree c₂ = 3) :
    False := by
  -- Forced-continuation prefix law for max-degree-≤2 graphs.
  have forced_prefix : ∀ (M : SimpleGraph V) [DecidableRel M.Adj] (a b b' : V)
      (p : M.Walk a b) (p' : M.Walk a b'), p.IsPath → p'.IsPath →
      (∀ v, M.degree v ≤ 2) → M.degree a ≤ 1 →
      p.support <+: p'.support ∨ p'.support <+: p.support := by
    clear hmin hw hodd hz hz4 hzp hpH hc₁ hc₂ hne hzc₁ hzc₂ hc₁3 hc₂3 hdeg
    intro M _ a b b' p p' hp hp' hdeg2 ha
    induction' n : p.length using Nat.strong_induction_on with n ih generalizing a b b' p p' M
    rcases p with ( _ | ⟨ hax, p₀ ⟩ ) <;> rcases p' with ( _ | ⟨ hax', p₀' ⟩ ) <;>
      simp_all +decide [ SimpleGraph.Walk.support ]
    rename_i x y
    have hxy : x = y := by
      contrapose! ha
      exact Finset.one_lt_card.2 ⟨ x, by aesop, y, by aesop ⟩
    subst hxy
    have hp₀a : a ∉ p₀.support := hp.2
    have hp₀'a : a ∉ p₀'.support := hp'.2
    have hedges : ∀ {c : V} (r : M.Walk x c), a ∉ r.support →
        ∀ e ∈ r.edges, e ∈ (M.deleteEdges {s(a, x)}).edgeSet := by
      intro c r har e he
      rw [SimpleGraph.edgeSet_deleteEdges]
      refine ⟨r.edges_subset_edgeSet he, ?_⟩
      simp only [Set.mem_singleton_iff]
      rintro rfl
      exact har (r.fst_mem_support_of_mem_edges he)
    have key := ih (p₀.length) (by simp_all; omega) (M.deleteEdges {s(a, x)}) x b b'
      (p₀.transfer _ (hedges p₀ hp₀a)) (p₀'.transfer _ (hedges p₀' hp₀'a))
      ((SimpleGraph.Walk.isPath_def _).mpr (by
        rw [SimpleGraph.Walk.support_transfer]; exact (SimpleGraph.Walk.isPath_def _).mp hp.1))
      ((SimpleGraph.Walk.isPath_def _).mpr (by
        rw [SimpleGraph.Walk.support_transfer]; exact (SimpleGraph.Walk.isPath_def _).mp hp'.1))
      (fun v => le_trans (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)) (hdeg2 v))
      (by
        have := degree_deleteEdges_single M a x hax x
        simp only [or_true, if_true] at this
        have hle := hdeg2 x
        omega)
      (by rw [SimpleGraph.Walk.length_transfer])
    simp only [SimpleGraph.Walk.support_transfer] at key
    rcases key with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- The only degree-1 vertex reachable from a degree-1 vertex is unique.
  have tmp_unique : ∀ (M : SimpleGraph V) [DecidableRel M.Adj]
      (hdeg : ∀ v, M.degree v ≤ 2) {z c₁ c₂ : V},
      M.degree z = 1 → M.degree c₁ = 1 → M.degree c₂ = 1 → c₁ ≠ z → c₂ ≠ z →
      ∀ (q₁ : M.Walk z c₁), q₁.IsPath → ∀ (q₂ : M.Walk z c₂), q₂.IsPath →
      c₁ = c₂ := by
    clear hmin hw hodd hz hz4 hzp hpH hc₁ hc₂ hne hzc₁ hzc₂ hc₁3 hc₂3 hdeg
    intro M _ hdeg z c₁ c₂ hz1 hc₁1 hc₂1 hc₁z hc₂z q₁ hq₁ q₂ hq₂
    obtain h | h := forced_prefix M z c₁ c₂ q₁ q₂ hq₁ hq₂ hdeg hz1.le
    · by_contra h_ne
      obtain ⟨i, hi⟩ : ∃ i, i < q₂.support.length - 1 ∧ q₂.getVert i = c₁ := by
        grind +suggestions
      have h_adj : M.Adj (q₂.getVert i) (q₂.getVert (i + 1)) ∧ M.Adj (q₂.getVert i) (q₂.getVert (i - 1)) := by
        rcases i <;> simp_all +decide [ SimpleGraph.Walk.getVert ]
        exact ⟨ by rw [ ← hi.2 ] ; exact q₂.adj_getVert_succ ( by linarith ), by rw [ ← hi.2 ] ; exact q₂.adj_getVert_succ ( by linarith ) |> fun h => h.symm ⟩
      have h_deg : M.degree (q₂.getVert i) ≥ 2 := by
        refine' Finset.one_lt_card.mpr ⟨ q₂.getVert ( i + 1 ), _, q₂.getVert ( i - 1 ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ]
        have := hq₂.support_nodup; simp_all +decide [ List.nodup_iff_injective_get ]
        intro h; have := @this ⟨ i + 1, by
          grind +splitImp ⟩ ⟨ i - 1, by
          grind +qlia ⟩ ; simp_all +decide [ SimpleGraph.Walk.getVert ]
        grind +suggestions
      grind +splitImp
    · by_contra h_contra
      obtain ⟨i, hi⟩ : ∃ i, i < q₁.length ∧ q₁.getVert (i + 1) = c₂ := by
        have h_interior : c₂ ∈ q₁.support ∧ c₂ ≠ z := by
          exact ⟨ h.subset ( by simp +decide ), hc₂z ⟩
        have h_interior : ∃ i, i ≤ q₁.length ∧ q₁.getVert i = c₂ := by
          have h_interior : ∀ {v : V} {w : V} {p : M.Walk v w}, c₂ ∈ p.support → ∃ i, i ≤ p.length ∧ p.getVert i = c₂ := by
            intros v w p hp; induction' p with v w p ih <;> simp_all +decide [ SimpleGraph.Walk.support ]
            rcases hp with ( rfl | hp ) <;> [ exact ⟨ 0, by simp +decide ⟩ ; exact Exists.elim ( ‹c₂ ∈ _ → ∃ i ≤ _, _› hp ) fun i hi => ⟨ i + 1, by linarith, by simp +decide [ hi.2 ] ⟩ ]
          exact h_interior ( by tauto )
        obtain ⟨ i, hi, hi' ⟩ := h_interior; use i - 1; rcases i with ( _ | i ) <;> simp_all +decide
      have h_neigh : M.Adj (q₁.getVert i) c₂ ∧ M.Adj (q₁.getVert (i + 2)) c₂ := by
        have h_neigh : M.Adj (q₁.getVert i) (q₁.getVert (i + 1)) ∧ M.Adj (q₁.getVert (i + 1)) (q₁.getVert (i + 2)) := by
          grind +suggestions
        simp_all +decide [ SimpleGraph.adj_comm ]
      have h_neigh : Finset.card (M.neighborFinset c₂) ≥ 2 := by
        refine' Finset.one_lt_card.mpr ⟨ q₁.getVert i, _, q₁.getVert ( i + 2 ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ]
        intro h_eq
        have := hq₁.getVert_injOn; simp_all +decide [ SimpleGraph.Walk.isPath_def ]
        exact absurd ( this ( show i ≤ q₁.length from by linarith ) ( show i + 2 ≤ q₁.length from by linarith [ show q₁.length ≥ i + 2 from Nat.succ_le_of_lt ( Nat.lt_of_le_of_ne ( by linarith ) ( by aesop_cat ) ) ] ) h_eq ) ( by linarith )
      simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ]
  -- Assemble: derive the degree facts and apply `tmp_unique`.
  obtain ⟨-, hdisj, -, -, -, -, hsum⟩ := hmin.1
  have hHle : ∀ v, H.degree v ≤ 2 := fun v => (half_degree_bounds G H K hdeg hmin.1 v).2
  have hKle : ∀ v, K.degree v ≤ 2 := fun v => (half_degree_bounds G K H hdeg hmin.1.swap v).2
  have hHc₁ : H.degree c₁ = 2 := degree_eq_two_of_mem_cycle_support H hHle hw hc₁
  have hHc₂ : H.degree c₂ = 2 := degree_eq_two_of_mem_cycle_support H hHle hw hc₂
  have hHz : H.degree z = 2 := degree_eq_two_of_mem_cycle_support H hHle hw hz
  have hKc₁ : K.degree c₁ = 1 := by have := hsum c₁; omega
  have hKc₂ : K.degree c₂ = 1 := by have := hsum c₂; omega
  have hKz : K.degree z = 2 := by have := hsum z; omega
  have hc₁z : c₁ ≠ z := (hzc₁.ne).symm
  have hc₂z : c₂ ≠ z := (hzc₂.ne).symm
  have hc₁p : c₁ ≠ p := by rintro rfl; exact hdisj z c₁ hzc₁ hzp
  have hc₂p : c₂ ≠ p := by rintro rfl; exact hdisj z c₂ hzc₂ hzp
  have hMdeg : ∀ v, (K.deleteEdges {s(z, p)}).degree v ≤ 2 :=
    fun v => le_trans (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)) (hKle v)
  have hMz : (K.deleteEdges {s(z, p)}).degree z = 1 := by
    have h := degree_deleteEdges_single K z p hzp z
    rw [if_pos (Or.inl rfl)] at h; omega
  have hMc₁ : (K.deleteEdges {s(z, p)}).degree c₁ = 1 := by
    have h := degree_deleteEdges_single K z p hzp c₁
    rw [if_neg (by push_neg; exact ⟨hc₁z, hc₁p⟩)] at h; omega
  have hMc₂ : (K.deleteEdges {s(z, p)}).degree c₂ = 1 := by
    have h := degree_deleteEdges_single K z p hzp c₂
    rw [if_neg (by push_neg; exact ⟨hc₂z, hc₂p⟩)] at h; omega
  obtain ⟨q₁, hq₁, -⟩ :=
    (C3_flank_structure_of_minimal G H K hdeg hmin hw hodd hz hz4 hzp hpH hc₁ hzc₁ hc₁3).2
  obtain ⟨q₂, hq₂, -⟩ :=
    (C3_flank_structure_of_minimal G H K hdeg hmin hw hodd hz hz4 hzp hpH hc₂ hzc₂ hc₂3).2
  exact hne (tmp_unique (K.deleteEdges {s(z, p)}) hMdeg hMz hMc₁ hMc₂ hc₁z hc₂z q₁ hq₁ q₂ hq₂)

/-- LADDER-PIN 6 (validity half of Lemma 2.6; the Δω identity is deferred with
the debris-linkage formalism, see file header).  The canonical 3-edge move is a
valid toggle. -/
lemma three_edge_toggle_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {z z' p q : V} (hzz' : H.Adj z z') (hzp : K.Adj z p) (hz'q : K.Adj z' q)
    (hz4 : G.degree z = 4) (hz'4 : G.degree z' = 4)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hpq : p ≠ q) :
    IsValidToggle G H K {s(z, p), s(z, z'), s(z', q)} := by
  convert toggle_valid_iff G H K hdeg hsplit _ _ |>.2 _;
  · simp +decide [ Set.insert_subset_iff, hsplit.1 ];
    exact ⟨ Or.inr hzp, Or.inl hzz', Or.inr hz'q ⟩;
  · intro v
    by_cases hv : v = z ∨ v = z' ∨ v = p ∨ v = q;
    · rcases hv with ( rfl | rfl | rfl | rfl );
      · simp_all +decide [ Finset.filter_insert, Finset.filter_singleton, SimpleGraph.incidenceSet ];
        have := hsplit.2.1 v p; have := hsplit.2.1 v z'; have := hsplit.2.1 z' q; simp_all +decide [ SimpleGraph.adj_comm ] ;
        split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
        cases ‹v = z' ∨ v = q› <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · simp_all +decide [ Finset.filter_insert, Finset.filter_singleton, SimpleGraph.incidenceSet ];
        cases hsplit ; aesop;
      · simp +decide [ Finset.filter_insert, Finset.filter_singleton, SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff, hzp, hpH, hqH ];
        all_goals have := hsplit.2; simp_all +decide [ SimpleGraph.adj_comm ];
        grind;
      · simp +decide [ *, Finset.filter_insert, Finset.filter_singleton, SimpleGraph.incidenceSet ];
        all_goals have := hsplit.2; simp_all +decide [ SimpleGraph.adj_comm ]; all_goals grind;
    · simp_all +decide [ Finset.filter_insert, Finset.filter_singleton, SimpleGraph.incidenceSet ]

/-! ## Parity and separation (STRIKE-A §6.1, §7) -/

/-- PROVED (ladder item 7a).  The number of `H`-light vertices is even (they
are exactly the odd-`H`-degree vertices; handshake in `H`). -/
lemma deg3_lightness_parity
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) :
    Even #{v : V | H.degree v = 1} := by
  have hb : ∀ v : V, 1 ≤ H.degree v ∧ H.degree v ≤ 2 :=
    fun v => half_degree_bounds G H K hdeg hsplit v
  have h := SimpleGraph.even_card_odd_degree_vertices H
  have heq : Finset.univ.filter (fun v : V => Odd (H.degree v))
      = Finset.univ.filter (fun v : V => H.degree v = 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hbv := hb v
    rw [Nat.odd_iff]
    constructor <;> intro h' <;> omega
  rwa [heq] at h

/-
Adjacency in a toggled graph: `s(u,v)` is an edge of `toggled M T` iff
`u ≠ v` and membership in `M` is flipped by `T`.
-/
lemma toggled_adj (M : SimpleGraph V) [DecidableRel M.Adj]
    (T : Finset (Sym2 V)) (u v : V) :
    (toggled M T).Adj u v ↔ u ≠ v ∧ (M.Adj u v ↔ s(u, v) ∉ T) := by
  unfold toggled; by_cases h : u = v <;> simp +decide [ h ] ;
  simp +decide [ symmDiff, h ];
  grind

/-
Adding a single edge `s(u,w)` between two vertices that are NOT reachable in
`M` creates no new odd cycle, so the odd-cycle count does not increase.  Any odd
cycle of `M'` that used the new edge would exhibit a `u`–`w` walk in `M`.
-/
lemma oddCycleCount_addEdge_le
    (M M' : SimpleGraph V) [DecidableRel M.Adj] [DecidableRel M'.Adj]
    {u w : V} (hnr : ¬ M.Reachable u w)
    (hM' : ∀ x y, M'.Adj x y ↔ (M.Adj x y ∨ (s(x, y) = s(u, w) ∧ x ≠ y))) :
    oddCycleCount M' ≤ oddCycleCount M := by
  apply Finset.card_le_card;
  intro S hS;
  -- Let $c$ be an odd cycle in $M'$ with support $S$.
  obtain ⟨x, c, hc⟩ : ∃ x : V, ∃ c : M'.Walk x x, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S := by
    unfold oddCycleSupports at hS; aesop;
  -- Since $s(u,w)$ is not in $c.edges$, every edge of $c$ lies in $M$.
  have h_edges_M : ∀ e ∈ c.edges, e ∈ M.edgeSet := by
    intro e he; by_cases he' : e = s(u, w) <;> simp_all +decide [ SimpleGraph.edgeSet ] ;
    · have h_not_bridge : (M'.deleteEdges {s(u, w)}).Reachable u w := by
        have h_not_bridge : ¬M'.IsBridge s(u, w) := by
          grind +suggestions;
        contrapose! h_not_bridge; simp_all +decide [ SimpleGraph.isBridge_iff ] ;
        by_cases huw : u = w <;> simp_all +decide [ SimpleGraph.deleteEdges ];
      have h_delete_edges : M'.deleteEdges {s(u, w)} = M := by
        ext x y; simp +decide [ hM' ] ;
        by_cases hx : x = u <;> by_cases hy : y = w <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact fun h => hnr <| h.reachable;
        · grind;
        · by_cases hx' : x = w <;> by_cases hy' : y = u <;> simp_all +decide [ SimpleGraph.adj_comm ];
          exact fun h => hnr <| h.reachable;
      grind;
    · rcases e with ⟨ x, y ⟩ ; simp_all +decide [ edgeSetEmbedding ] ;
      have := c.edges_subset_edgeSet he; aesop;
  -- Let $c'$ be the walk in $M$ obtained by transferring $c$.
  obtain ⟨c', hc'⟩ : ∃ c' : M.Walk x x, c'.IsCycle ∧ c'.length = c.length ∧ c'.support.toFinset = S := by
    refine' ⟨ c.transfer M h_edges_M, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.transfer ];
    rw [ SimpleGraph.Walk.isCycle_def ] at *;
    simp_all +decide [ SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.transfer ];
    cases c <;> simp_all +decide [ SimpleGraph.Walk.transfer ];
  unfold oddCycleSupports; aesop;

/-
Deleting a single edge incident to a degree-≤1 vertex `q` never disconnects
two vertices `p, z` that are both different from `q`: any `p`–`z` path avoids the
degree-≤1 vertex `q`, hence uses no edge at `q`.
-/
lemma reach_avoid_low_deg
    (M : SimpleGraph V) [DecidableRel M.Adj] {p z q : V}
    (hq1 : M.degree q ≤ 1) (hpq : p ≠ q) (hzq : z ≠ q)
    (h : M.Reachable p z) {e : Sym2 V} (heq : q ∈ e) :
    (M.deleteEdges {e}).Reachable p z := by
  by_contra h_contra;
  obtain ⟨P, hP⟩ : ∃ P : M.Walk p z, P.IsPath := by
    obtain ⟨ P, hP ⟩ := h.exists_isPath; exact ⟨ P, hP ⟩ ;
  -- Since $q$ is not in the support of $P$, every edge of $P$ avoids $q$.
  have h_edges_avoid_q : ∀ s ∈ P.edges, q ∉ s := by
    intro s hs hqs
    have hq_in_support : q ∈ P.support := by
      have hq_in_support : ∀ {u v : V} {P : M.Walk u v}, s ∈ P.edges → q ∈ s → q ∈ P.support := by
        intros u v P hs hqs; induction P <;> aesop;
      exact hq_in_support hs hqs;
    obtain ⟨i, hi⟩ : ∃ i, P.getVert i = q ∧ 0 < i ∧ i < P.length := by
      obtain ⟨i, hi⟩ : ∃ i, P.getVert i = q := by
        rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hq_in_support ; tauto;
      grind +suggestions;
    have h_deg_q : 2 ≤ M.degree q := by
      have h_adj : M.Adj (P.getVert (i - 1)) q ∧ M.Adj q (P.getVert (i + 1)) := by
        rcases i <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        have := P.adj_getVert_succ ( show ‹_› < P.length from Nat.lt_of_succ_lt hi.2 ) ; have := P.adj_getVert_succ ( show ‹_› + 1 < P.length from hi.2 ) ; aesop;
      have h_distinct : P.getVert (i - 1) ≠ P.getVert (i + 1) := by
        have := hP.getVert_injOn;
        exact this.ne ( show i - 1 ≤ P.length from Nat.sub_le_of_le_add <| by linarith ) ( show i + 1 ≤ P.length from by linarith ) <| by omega;
      refine' Finset.one_lt_card.mpr ⟨ P.getVert ( i - 1 ), _, P.getVert ( i + 1 ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
    grind;
  refine' h_contra _;
  grind +suggestions

/-
In a max-degree-≤2 graph, three distinct degree-1 vertices cannot all lie in
one connected component (a path has only two ends).
-/
lemma three_deg_one_not_all_reachable
    (M : SimpleGraph V) [DecidableRel M.Adj] (hdeg : ∀ v, M.degree v ≤ 2)
    {a b c : V} (ha : M.degree a = 1) (hb : M.degree b = 1) (hc : M.degree c = 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (rab : M.Reachable a b) (rac : M.Reachable a c) : False := by
  -- Since `a` is reachable from `b` and `c`, and `b` and `c` are distinct, `a` must be connected to both `b` and `c`.
  have h_connected : M.Reachable b c := by
    exact rab.symm.trans rac;
  obtain ⟨ p, hp ⟩ := h_connected.exists_isPath;
  have h_support : ∀ x ∈ p.support, ∀ y, M.Adj x y → y ∈ p.support := by
    intro x hx y hy
    have h_neighbor_count : (p.toSubgraph.neighborSet x).ncard = M.degree x := by
      by_cases hx' : x = b ∨ x = c;
      · cases hx' <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
        · rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.toSubgraph ];
          simp_all +decide [ Set.eq_singleton_iff_unique_mem, SimpleGraph.subgraphOfAdj ];
          grind +suggestions;
        · have h_neighbor_c : p.getVert (p.length - 1) ∈ p.toSubgraph.neighborSet c := by
            have h_last : p.getVert (p.length - 1) ≠ c := by
              intro h_last_eq_c
              have h_contradiction : p.getVert (p.length - 1) = p.getVert p.length := by
                aesop;
              have := hp.getVert_injOn;
              exact absurd ( this ( show p.length - 1 ≤ p.length from Nat.sub_le _ _ ) ( show p.length ≤ p.length from le_rfl ) h_contradiction ) ( Nat.ne_of_lt ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < p.length from Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ) );
            grind +suggestions;
          use p.getVert (p.length - 1);
          have h_neighbor_c : (p.toSubgraph.neighborSet c).ncard ≤ 1 := by
            have h_neighbor_c : (p.toSubgraph.neighborSet c).ncard ≤ (M.neighborSet c).ncard := by
              apply Set.ncard_le_ncard;
              · grind +suggestions;
              · exact Set.toFinite _;
            simp_all +decide [ Set.ncard_eq_toFinset_card' ];
          rw [ Set.ncard_le_one_iff ] at h_neighbor_c;
          exact Set.eq_singleton_iff_unique_mem.mpr ⟨ by assumption, fun x hx => h_neighbor_c hx ‹_› ⟩;
      · have h_neighbor_count : (p.toSubgraph.neighborSet x).ncard = 2 := by
          obtain ⟨ i, hi ⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx;
          grind +suggestions;
        have h_neighbor_count : (p.toSubgraph.neighborSet x).ncard ≤ M.degree x := by
          rw [ Set.ncard_eq_toFinset_card _ ];
          refine' Finset.card_le_card _;
          simp +decide [ Finset.subset_iff, SimpleGraph.Walk.mem_support_iff_exists_getVert ];
          exact fun ⦃x_2⦄ a ↦ Subgraph.Adj.adj_sub a;
        linarith [ hdeg x ];
    have h_neighbor_count : (p.toSubgraph.neighborSet x) = M.neighborSet x := by
      apply Set.eq_of_subset_of_ncard_le;
      · exact fun z hz => by simpa using p.toSubgraph.adj_sub hz;
      · simp_all +decide [ Set.ncard_eq_toFinset_card' ];
        exact Finset.card_le_card fun y hy => by aesop;
      · exact Set.toFinite _;
    simp_all +decide [ Set.ext_iff ];
    grind +suggestions;
  have h_support_reachable : ∀ x ∈ p.support, ∀ y, M.Reachable x y → y ∈ p.support := by
    intro x hx y hy
    induction' hy with y hy ih;
    induction' y with y z hyz ih;
    · exact hx;
    · exact ‹hyz ∈ p.support → ih ∈ p.support› ( h_support _ hx _ ‹_› );
  have h_a_in_support : a ∈ p.support := by
    exact h_support_reachable _ ( by simp +decide ) _ ( rab.symm );
  -- Since `a` is in the support of `p`, and `p` is a path, `a` must have at least two neighbors in `p`.
  obtain ⟨i, hi⟩ : ∃ i, p.getVert i = a ∧ 0 < i ∧ i < p.length := by
    obtain ⟨i, hi⟩ : ∃ i, p.getVert i = a := by
      rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at h_a_in_support ; tauto;
    grind +suggestions;
  have h_two_neighbors : M.Adj (p.getVert (i - 1)) a ∧ M.Adj (p.getVert (i + 1)) a := by
    have h_two_neighbors : M.Adj (p.getVert (i - 1)) (p.getVert i) ∧ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
      have h_two_neighbors : ∀ i < p.length, M.Adj (p.getVert i) (p.getVert (i + 1)) := by
        exact fun i a ↦ Walk.adj_getVert_succ p a;
      exact ⟨ by simpa only [ Nat.sub_add_cancel hi.2.1 ] using h_two_neighbors ( i - 1 ) ( Nat.lt_of_le_of_lt ( Nat.pred_le _ ) hi.2.2 ), h_two_neighbors i hi.2.2 ⟩;
    simp_all +decide [ SimpleGraph.adj_comm ];
  have h_two_neighbors_distinct : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    have := hp.getVert_injOn;
    exact this.ne ( by norm_num; omega ) ( by norm_num; omega ) ( by omega );
  have h_two_neighbors_distinct : Finset.card (M.neighborFinset a) ≥ 2 := by
    exact Finset.one_lt_card.mpr ⟨ p.getVert ( i - 1 ), by simpa [ SimpleGraph.adj_comm ] using h_two_neighbors.1, p.getVert ( i + 1 ), by simpa [ SimpleGraph.adj_comm ] using h_two_neighbors.2, h_two_neighbors_distinct ⟩;
  simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ]

/-
The two-sided path separation of STRIKE-A §7.  In a max-degree-≤2 graph a
degree-2 vertex `q` with neighbours `z₂, z₃` separates them, so a degree-1
vertex `p` cannot reach BOTH `z₂` (in `K − q z₂`) and `z₃` (in `K − q z₃`).
-/
lemma double_poison_k_sep
    (K : SimpleGraph V) [DecidableRel K.Adj] (hdeg : ∀ v, K.degree v ≤ 2)
    {p q z₂ z₃ : V}
    (hKp : K.degree p = 1) (hKq : K.degree q = 2)
    (hKz₂ : K.degree z₂ = 2) (hKz₃ : K.degree z₃ = 2)
    (hqz₂ : K.Adj q z₂) (hqz₃ : K.Adj q z₃)
    (hpq : p ≠ q) (hpz₂ : p ≠ z₂) (hpz₃ : p ≠ z₃) (hz₂z₃ : z₂ ≠ z₃) :
    ¬ (K.deleteEdges {s(q, z₂)}).Reachable p z₂ ∨
      ¬ (K.deleteEdges {s(q, z₃)}).Reachable p z₃ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨R₂, R₃⟩ := hcon
  have hz₂q : z₂ ≠ q := hqz₂.ne'
  have hz₃q : z₃ ≠ q := hqz₃.ne'
  have hne : s(q, z₃) ≠ s(q, z₂) := by
    intro hh; rw [Sym2.eq_iff] at hh
    rcases hh with ⟨_, hh⟩ | ⟨hh, _⟩
    · exact hz₂z₃ hh.symm
    · exact hqz₂.ne hh
  -- `q` has degree ≤ 1 after deleting one of its two edges
  have hMq₂ : (K.deleteEdges {s(q, z₂)}).degree q ≤ 1 := by
    have h := degree_deleteEdges_single K q z₂ hqz₂ q
    rw [if_pos (Or.inl rfl)] at h; omega
  have hMq₃ : (K.deleteEdges {s(q, z₃)}).degree q ≤ 1 := by
    have h := degree_deleteEdges_single K q z₃ hqz₃ q
    rw [if_pos (Or.inl rfl)] at h; omega
  have hAdjInner : (K.deleteEdges {s(q, z₂)}).Adj q z₃ := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hqz₃, by simp only [Set.mem_singleton_iff]; exact hne⟩
  -- reach `z₂` and `z₃` from `p` in the doubly-deleted graph (both `q`-edges gone)
  have hR2 : ((K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)}).Reachable p z₂ :=
    reach_avoid_low_deg (K.deleteEdges {s(q, z₂)}) hMq₂ hpq hz₂q R₂ (by simp)
  have hR3 : ((K.deleteEdges {s(q, z₃)}).deleteEdges {s(q, z₂)}).Reachable p z₃ :=
    reach_avoid_low_deg (K.deleteEdges {s(q, z₃)}) hMq₃ hpq hz₃q R₃ (by simp)
  have hgeq : (K.deleteEdges {s(q, z₃)}).deleteEdges {s(q, z₂)}
            = (K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)} := by
    rw [SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_deleteEdges,
        Set.union_comm]
  rw [hgeq] at hR3
  -- degrees in the doubly-deleted graph: `p, z₂, z₃` are all degree 1
  have hdp : ((K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)}).degree p = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjInner p,
        degree_deleteEdges_single K q z₂ hqz₂ p,
        if_neg (by push_neg; exact ⟨hpq, hpz₂⟩),
        if_neg (by push_neg; exact ⟨hpq, hpz₃⟩)]
    omega
  have hdz₂ : ((K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)}).degree z₂ = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjInner z₂,
        degree_deleteEdges_single K q z₂ hqz₂ z₂,
        if_pos (Or.inr rfl),
        if_neg (by push_neg; exact ⟨hz₂q, hz₂z₃⟩)]
    omega
  have hdz₃ : ((K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)}).degree z₃ = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjInner z₃,
        degree_deleteEdges_single K q z₂ hqz₂ z₃,
        if_pos (Or.inr rfl),
        if_neg (by push_neg; exact ⟨hz₃q, fun hh => hz₂z₃ hh.symm⟩)]
    omega
  have hle : ∀ v, ((K.deleteEdges {s(q, z₂)}).deleteEdges {s(q, z₃)}).degree v ≤ 2 :=
    fun v => le_trans (SimpleGraph.degree_le_of_le
      (le_trans (SimpleGraph.deleteEdges_le _) (SimpleGraph.deleteEdges_le _))) (hdeg v)
  exact three_deg_one_not_all_reachable _ hle hdp hdz₂ hdz₃ hpz₂ hpz₃ hz₂z₃ hR2 hR3

/-
H-side of the §7 count: toggling the canonical 2-edge move destroys the
odd `H`-triangle `p–a–b` and creates no new odd `H`-cycle.
-/
lemma config_ii_H_count
    (H : SimpleGraph V) [DecidableRel H.Adj] (hHle : ∀ v, H.degree v ≤ 2)
    {p a b q : V}
    (hpa : H.Adj p a) (hab : H.Adj a b) (hbp : H.Adj b p)
    (hqp : q ≠ p) (hqa : q ≠ a) (hqb : q ≠ b) :
    oddCycleCount (toggled H {s(p, a), s(q, a)}) < oddCycleCount H := by
  have hM : ¬ H.Reachable q a := by
    intro hq_a_reachable
    have hq_in_cycle: q ∈ ({p, a, b} : Finset V) := by
      have hq_in_cycle : (SimpleGraph.Walk.cons hpa (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbp SimpleGraph.Walk.nil))).IsCycle := by
        simp +decide [ SimpleGraph.Walk.isCycle_def ];
        aesop;
      have := cycle_support_closed_reachable H hHle hq_in_cycle ( by simp +decide [ SimpleGraph.Walk.cons_isCycle_iff ] ) ( hq_a_reachable.symm ) ; simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ] ;
    aesop;
  have hM' : ∀ x y, (toggled H {s(p, a), s(q, a)}).Adj x y ↔ (H.deleteEdges {s(p, a)}).Adj x y ∨ (s(x, y) = s(q, a) ∧ x ≠ y) := by
    simp +decide [ toggled, SimpleGraph.deleteEdges_adj ];
    intro x y; by_cases hx : x = y <;> simp +decide [ *, symmDiff ] ;
    grind +suggestions;
  refine' lt_of_le_of_lt ( oddCycleCount_addEdge_le _ _ _ hM' ) _;
  · exact fun h => hM <| h.mono <| by simp +decide [ SimpleGraph.deleteEdges_le ] ;
  · apply oddCycleCount_deleteEdges_lt H hHle;
    any_goals exact SimpleGraph.Walk.cons hpa ( SimpleGraph.Walk.cons hab ( SimpleGraph.Walk.cons hbp SimpleGraph.Walk.nil ) );
    · simp +decide [ SimpleGraph.Walk.isCycle_def ];
      aesop;
    · simp +decide [ SimpleGraph.Walk.length ];
    · exact hpa;
    · simp +decide [ SimpleGraph.Walk.edges ]

/-
K-side of the §7 count: when `p` cannot reach `a` in `K − q a`, toggling the
canonical 2-edge move creates no new odd `K`-cycle.
-/
lemma config_ii_K_count
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {p a q : V} (hpq : p ≠ q) (hqa' : K.Adj q a) (hnKpa : ¬ K.Adj p a)
    (hnr : ¬ (K.deleteEdges {s(q, a)}).Reachable p a) :
    oddCycleCount (toggled K {s(p, a), s(q, a)}) ≤ oddCycleCount K := by
  refine' le_trans _ ( oddCycleCount_deleteEdges_le K ( s(q, a) ) );
  apply oddCycleCount_addEdge_le;
  exact hnr;
  intro x y; by_cases hx : x = y <;> simp +decide [ *, toggled_adj, SimpleGraph.deleteEdges_adj ] ;
  by_cases hx' : x = p <;> by_cases hy' : y = a <;> by_cases hx'' : x = a <;> by_cases hy'' : y = p <;> simp_all +decide [ SimpleGraph.adj_comm ];
  · by_cases hx''' : x = q <;> simp_all +decide [ SimpleGraph.adj_comm ];
  · by_cases hy''' : y = q <;> simp_all +decide [ SimpleGraph.adj_comm ]

/-
Validity of the canonical 2-edge move `{s(p,a), s(q,a)}` at a split, via the
vertex-local criterion `toggle_valid_iff`.
-/
lemma config_ii_toggle_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p a q : V}
    (hpa : H.Adj p a) (hqa' : K.Adj q a)
    (hHp : H.degree p = 2) (hKp : K.degree p = 1)
    (ha4 : G.degree a = 4)
    (hqH : H.degree q = 1) (hKq : K.degree q = 2)
    (hpq : p ≠ q) (hpa_ne : p ≠ a) (hqa_ne : q ≠ a)
    (hnHqa : ¬ H.Adj q a) (hnKpa : ¬ K.Adj p a) :
    IsValidToggle G H K {s(p, a), s(q, a)} := by
  apply (toggle_valid_iff G H K hdeg hsplit {s(p, a), s(q, a)} (by
  intro e he; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
  rcases he with ( rfl | rfl ) <;> [ exact hsplit.2.2.1 hpa; exact hsplit.2.2.2.1 hqa' ])).mpr;
  intro v;
  by_cases hv : v = p <;> by_cases hv' : v = q <;> by_cases hv'' : v = a <;> simp +decide [ *, Finset.filter_insert, Finset.filter_singleton ];
  all_goals simp_all +decide [ SimpleGraph.incidenceSet ];
  · have := hsplit.2.2.2.2.2.2 p; aesop;
  · have := hsplit.2.2.2.2.2.2 q; simp_all +decide ;
    grind

/-
Assembly of the §7 contradiction from the separation hypothesis: if `p`
cannot reach `a` in `K − q a`, the canonical move `{s(p,a), s(q,a)}` is a strict
valid toggle, contradicting minimality.
-/
lemma config_ii_strict_of_sep
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {p a b q : V}
    (hpa : H.Adj p a) (hab : H.Adj a b) (hbp : H.Adj b p)
    (hp3 : G.degree p = 3) (ha4 : G.degree a = 4) (hb4 : G.degree b = 4)
    (hq3 : G.degree q = 3) (hqp : q ≠ p) (hqa : q ≠ a) (hqb : q ≠ b)
    (hqa' : K.Adj q a) (hqb' : K.Adj q b) (hqH : H.degree q = 1)
    (hnr : ¬ (K.deleteEdges {s(q, a)}).Reachable p a) :
    False := by
  obtain ⟨hHp, hKp, hKq⟩ : H.degree p = 2 ∧ K.degree p = 1 ∧ K.degree q = 2 := by
    have hHp : H.degree p = 2 := by
      have hHle : ∀ v, H.degree v ≤ 2 := by
        exact fun v => half_degree_bounds G H K hdeg hmin.1 v |>.2;
      have hHp : H.degree p ≥ 2 := by
        refine' Finset.one_lt_card.2 ⟨ a, _, b, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
        exact Adj.ne' (id (adj_symm H hab));
      exact le_antisymm ( hHle p ) hHp
    have hKp : K.degree p = 1 := by
      have := hmin.1.2.2.2.2.2.2 p; omega;
    have hKq : K.degree q = 2 := by
      have := hmin.1.2.2.2.2.2.2 q; simp_all +decide ;
      linarith
    exact ⟨hHp, hKp, hKq⟩;
  have hHc := config_ii_H_count H ( fun v => by
    exact half_degree_bounds G H K hdeg hmin.1 v |>.2 ) hpa hab hbp hqp hqa hqb;
  have hKc := config_ii_K_count K hqp.symm hqa' (by
  exact fun h => hnr <| SimpleGraph.Adj.reachable <| by aesop;) hnr;
  have hval := config_ii_toggle_valid G H K hdeg hmin.1 hpa hqa' hHp hKp ha4 hqH hKq hqp.symm hpa.ne hqa (by
  intro hqa'';
  have := hmin.1.2.1 q a hqa''; simp_all +decide ;) (by
  contrapose! hnr;
  exact SimpleGraph.Adj.reachable ( by aesop ));
  exact not_le_of_gt ( add_lt_add_of_lt_of_le hHc hKc ) ( hmin.2 _ _ ( instDecToggled H _ ) ( instDecToggled K _ ) hval.2 )

/-- LADDER-PIN 7b (Theorem 7.1, ALL t; subsumes `config_ii_impossible_t2`).
The double-poisoner configuration — an `H`-triangle with a degree-3 vertex,
double-poisoned from one exposed degree-3 vertex — never survives minimality. -/
lemma double_poisoner_separation
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    {p z₂ z₃ q : V}
    (ht₁ : H.Adj p z₂) (ht₂ : H.Adj z₂ z₃) (ht₃ : H.Adj z₃ p)
    (hp3 : G.degree p = 3) (hz₂4 : G.degree z₂ = 4) (hz₃4 : G.degree z₃ = 4)
    (hq3 : G.degree q = 3) (hqp : q ≠ p) (hq₂ : q ≠ z₂) (hq₃ : q ≠ z₃)
    (hqz₂ : K.Adj q z₂) (hqz₃ : K.Adj q z₃)
    (hqH : H.degree q = 1) :
    False := by
  have hsplit := hmin.1
  have hHle : ∀ v, H.degree v ≤ 2 := fun v => (half_degree_bounds G H K hdeg hsplit v).2
  have hKle : ∀ v, K.degree v ≤ 2 :=
    fun v => (half_degree_bounds G K H hdeg hsplit.swap v).2
  have hsum := hsplit.2.2.2.2.2.2
  -- exact H-degrees at the triangle vertices
  have hHp : H.degree p = 2 := by
    refine le_antisymm (hHle p) ?_
    have h1 : z₂ ∈ H.neighborFinset p := (H.mem_neighborFinset p z₂).mpr ht₁
    have h2 : z₃ ∈ H.neighborFinset p := (H.mem_neighborFinset p z₃).mpr ht₃.symm
    have hcard : ({z₂, z₃} : Finset V).card ≤ (H.neighborFinset p).card :=
      Finset.card_le_card (by
        rw [Finset.insert_subset_iff]
        exact ⟨h1, Finset.singleton_subset_iff.mpr h2⟩)
    rw [Finset.card_pair ht₂.ne] at hcard
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hHz₂ : H.degree z₂ = 2 := by
    refine le_antisymm (hHle z₂) ?_
    have h1 : p ∈ H.neighborFinset z₂ := (H.mem_neighborFinset z₂ p).mpr ht₁.symm
    have h2 : z₃ ∈ H.neighborFinset z₂ := (H.mem_neighborFinset z₂ z₃).mpr ht₂
    have hcard : ({p, z₃} : Finset V).card ≤ (H.neighborFinset z₂).card :=
      Finset.card_le_card (by
        rw [Finset.insert_subset_iff]
        exact ⟨h1, Finset.singleton_subset_iff.mpr h2⟩)
    rw [Finset.card_pair ht₃.symm.ne] at hcard
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hHz₃ : H.degree z₃ = 2 := by
    refine le_antisymm (hHle z₃) ?_
    have h1 : z₂ ∈ H.neighborFinset z₃ := (H.mem_neighborFinset z₃ z₂).mpr ht₂.symm
    have h2 : p ∈ H.neighborFinset z₃ := (H.mem_neighborFinset z₃ p).mpr ht₃
    have hcard : ({z₂, p} : Finset V).card ≤ (H.neighborFinset z₃).card :=
      Finset.card_le_card (by
        rw [Finset.insert_subset_iff]
        exact ⟨h1, Finset.singleton_subset_iff.mpr h2⟩)
    rw [Finset.card_pair ht₁.ne.symm] at hcard
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  -- K-degrees
  have hKp : K.degree p = 1 := by have := hsum p; omega
  have hKz₂ : K.degree z₂ = 2 := by have := hsum z₂; omega
  have hKz₃ : K.degree z₃ = 2 := by have := hsum z₃; omega
  have hKq : K.degree q = 2 := by have := hsum q; omega
  -- distinctness of the triangle vertices
  have hpz₂ : p ≠ z₂ := ht₁.ne
  have hpz₃ : p ≠ z₃ := ht₃.symm.ne
  have hz₂z₃ : z₂ ≠ z₃ := ht₂.ne
  -- the two-sided separation
  rcases double_poison_k_sep K hKle hKp hKq hKz₂ hKz₃ hqz₂ hqz₃
      hqp.symm hpz₂ hpz₃ hz₂z₃ with h2 | h3
  · exact config_ii_strict_of_sep G H K hdeg hmin ht₁ ht₂ ht₃
      hp3 hz₂4 hz₃4 hq3 hqp hq₂ hq₃ hqz₂ hqz₃ hqH h2
  · exact config_ii_strict_of_sep G H K hdeg hmin ht₃.symm ht₂.symm ht₁.symm
      hp3 hz₃4 hz₂4 hq3 hqp hq₃ hq₂ hqz₃ hqz₂ hqH h3

/-! ## The t ≤ 2 blocked world (STRIKE-A §6) -/

section PoisonedShapeHelpers

/-- In a `{3,4}`-split, a degree-4 vertex has both halves of degree exactly 2. -/
private lemma split_deg4_halves
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) {v : V} (h4 : G.degree v = 4) :
    H.degree v = 2 ∧ K.degree v = 2 := by
  obtain ⟨_, _, _, _, hH, hK, hsum⟩ := hsplit
  have := hH v; have := hK v; have := hsum v
  omega

/-- Split-degree sum. -/
private lemma split_deg_sum
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K) (v : V) :
    H.degree v + K.degree v = G.degree v :=
  hsplit.2.2.2.2.2.2 v

/-- An `H`-light vertex has `G`-degree 3. -/
private lemma H_light_imp_deg3
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) {v : V} (h1 : H.degree v = 1) :
    G.degree v = 3 := by
  rcases hdeg v with h | h
  · exact h
  · have := (split_deg4_halves G H K hdeg hsplit h).1; omega

/-
Every two distinct vertices of a 3-element odd-cycle support are `H`-adjacent.
-/
private lemma cycle3_all_adj
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg2 : ∀ v, H.degree v ≤ 2)
    {S : Finset V} (hS : S ∈ oddCycleSupports H) (hcard : S.card = 3)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    H.Adj u v := by
  -- By definition of `oddCycleSupports`, there exists an odd cycle `c` in `H` such that `S = c.support.toFinset`.
  obtain ⟨x, w, hc⟩ : ∃ x : V, ∃ w : H.Walk x x, w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = S := by
    unfold oddCycleSupports at hS; aesop;
  have hu_cycle : u ∈ w.support := by
    aesop
  have hv_cycle : v ∈ w.support := by
    exact List.mem_toFinset.mp ( hc.2.2.symm ▸ hv );
  have h_neighbor : H.neighborFinset u ⊆ S := by
    intro y hy; simp_all +decide [ Finset.subset_iff ] ;
    exact hc.2.2 ▸ by simpa using cycle_support_closed_adj H hdeg2 hc.1 hu_cycle hy;
  have h_neighbor_card : (H.neighborFinset u).card = 2 := by
    have := degree_eq_two_of_mem_cycle_support H hdeg2 hc.1 hu_cycle; aesop;
  have h_neighbor_eq : H.neighborFinset u = S.erase u := by
    exact Finset.eq_of_subset_of_card_le ( fun x hx => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( h_neighbor hx ) ) ( by aesop );
  replace h_neighbor_eq := Finset.ext_iff.mp h_neighbor_eq v; aesop;

/-
The support of an odd `H`-cycle has odd cardinality.
-/
private lemma oddCycleSupport_card_odd
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {S : Finset V} (hS : S ∈ oddCycleSupports H) :
    Odd S.card := by
  unfold oddCycleSupports at hS; simp_all +decide [ SimpleGraph.Walk.isCycle_def ] ;
  obtain ⟨ x, w, hw, hw', rfl ⟩ := hS;
  have h_card : w.support.toFinset.card = w.support.tail.toFinset.card := by
    rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide [ List.nodup_cons ];
  rw [ h_card, List.toFinset_card_of_nodup hw.2.2 ] ; simp_all +decide [ SimpleGraph.Walk.length_support ] ;

/-
Charging bound (STRIKE-B Lemma B0): a fully-poisoned odd `H`-cycle support has
at most `2 · numDeg3 G` vertices.  Each poisoned vertex is charged to a degree-3
witness (itself, or a degree-3 `K`-neighbour); every degree-3 vertex receives at
most two charges.
-/
private lemma poisoned_support_card_le
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {S : Finset V} (hHdeg2 : ∀ u ∈ S, H.degree u = 2)
    (hpois : cleanSet G K S = ∅) :
    S.card ≤ 2 * numDeg3 G := by
  -- For each $u \in S$, there exists $w$ such that $G.degree w = 3$ and $(w = u ∨ K.Adj u w)$.
  have h_witness : ∀ u ∈ S, ∃ w, G.degree w = 3 ∧ (w = u ∨ K.Adj u w) := by
    intro u hu
    have h_not_clean : ¬CleanVertex G K u := by
      exact fun h => Finset.notMem_empty u ( hpois ▸ Finset.mem_filter.mpr ⟨ hu, h ⟩ );
    unfold CleanVertex at h_not_clean; simp_all +decide [ cap_eq_three_iff ];
    grind;
  choose! f hf using h_witness;
  -- By the choice function `f`, each vertex `u ∈ S` is charged to a degree-3 witness `w` such that `w = u` or `K.Adj u w`.
  have h_charge_bound : ∀ b ∈ Finset.univ.filter (fun v => G.degree v = 3), (Finset.filter (fun u => f u = b) S).card ≤ 2 := by
    intro b hb
    have hT : (Finset.filter (fun u => f u = b) S) ⊆ {u ∈ S | u = b ∨ K.Adj u b} := by
      grind;
    by_cases hbS : b ∈ S;
    · have hKdeg_b : K.degree b = 1 := by
        have := split_deg_sum G H K hsplit b; simp_all +decide ;
        linarith;
      have hT_card : (Finset.filter (fun u => u = b ∨ K.Adj u b) S).card ≤ 2 := by
        have hT_card : (Finset.filter (fun u => u = b ∨ K.Adj u b) S).card ≤ (insert b (K.neighborFinset b)).card := by
          refine Finset.card_le_card ?_;
          simp +decide [ Finset.subset_iff, SimpleGraph.adj_comm ];
        exact hT_card.trans ( Finset.card_insert_le _ _ |> le_trans <| by simp +decide [ hKdeg_b ] );
      exact le_trans ( Finset.card_le_card hT ) hT_card;
    · have hT_subset : {u ∈ S | f u = b} ⊆ K.neighborFinset b := by
        simp_all +decide [ Finset.subset_iff ];
        exact fun x hx hx' => by cases hT hx hx' <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
      exact le_trans ( Finset.card_le_card hT_subset ) ( by simpa using hsplit.2.2.2.2.2.1 b );
  convert Finset.card_le_mul_card_image_of_maps_to _ _ _ using 1;
  exacts [ inferInstance, f, fun u hu => by simpa using hf u hu |>.1, fun b hb => h_charge_bound b hb ]

/-
If `p` has odd `H`-degree and the only odd-`H`-degree vertices are `p` and
`q`, then `q` is `H`-reachable from `p` (component parity).
-/
private lemma reachable_of_two_odd
    (H : SimpleGraph V) [DecidableRel H.Adj] {p q : V}
    (hp : Odd (H.degree p))
    (hall : ∀ v, Odd (H.degree v) → v = p ∨ v = q) :
    H.Reachable p q := by
  grind +suggestions

end PoisonedShapeHelpers

section PoisonedShapeCore

/-
Poison witness: a poisoned support vertex is charged to a degree-3 vertex
(itself, or a degree-3 `K`-neighbour).
-/
private lemma poison_deg3_witness
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    {S : Finset V} {z : V} (hz : z ∈ S) (hpois : cleanSet G K S = ∅) :
    ∃ w, G.degree w = 3 ∧ (w = z ∨ K.Adj z w) := by
  contrapose! hpois;
  refine' ⟨ z, _ ⟩;
  refine' Finset.mem_filter.mpr ⟨ hz, fun v hv => _ ⟩;
  cases hdeg z <;> cases hdeg v <;> simp_all +decide [ cap_eq_three_iff ];
  exact hpois z ‹_› |>.1 rfl

/-
Two-element degree-3 vertex set from `numDeg3 = 2`.
-/
private lemma deg3_pair_of_numdeg3_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : numDeg3 G = 2) :
    ∃ a b : V, a ≠ b ∧ G.degree a = 3 ∧ G.degree b = 3 ∧
      (∀ v, G.degree v = 3 → v = a ∨ v = b) := by
  have := Finset.card_eq_two.mp h; obtain ⟨ a, b, hab ⟩ := this; use a, b; simp_all +decide [ Finset.ext_iff ] ;

/-
Every vertex of an odd-cycle support has `H`-degree 2.
-/
private lemma oddCycleSupport_Hdeg2
    (H : SimpleGraph V) [DecidableRel H.Adj] (hHle2 : ∀ v, H.degree v ≤ 2)
    {S : Finset V} (hS : S ∈ oddCycleSupports H) :
    ∀ u ∈ S, H.degree u = 2 := by
  intro u hu;
  -- By definition of `oddCycleSupports`, there exists an odd cycle `c` in `H` such that `S = c.support.toFinset`.
  obtain ⟨x, c, hc⟩ : ∃ x : V, ∃ c : H.Walk x x, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S := by
    contrapose! hS; simp_all +decide [ oddCycleSupports ] ;
  convert degree_eq_two_of_mem_cycle_support H hHle2 hc.1 ( List.mem_toFinset.mp ( hc.2.2.symm ▸ hu ) )

/-
STEP B: a poisoned odd support at `t ≤ 2` is a triangle and `t = 2`.
-/
private lemma poisoned_t2_card
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) (ht2 : numDeg3 G ≤ 2)
    {S : Finset V} (hS : S ∈ oddCycleSupports H)
    (hHdeg2 : ∀ u ∈ S, H.degree u = 2) (hpois : cleanSet G K S = ∅) :
    S.card = 3 ∧ numDeg3 G = 2 := by
  have hS_card : S.card ≤ 2 * numDeg3 G := by
    apply poisoned_support_card_le G H K hdeg hsplit hHdeg2 hpois;
  interval_cases _ : numDeg3 G <;> simp_all +decide;
  · exact absurd ( nonempty_of_mem_oddCycleSupports _ hS ) ( by simp +decide );
  · have := oddCycleSupports_three_le_card H S hS; interval_cases _ : #S;
  · have := oddCycleSupport_card_odd H hS; interval_cases _ : #S <;> simp_all +decide ;
    exact absurd ( oddCycleSupports_three_le_card H S hS ) ( by linarith )

/-
STEP F: no degree-3 vertex lies on the fully-poisoned triangle support.
-/
private lemma poison_pair_notin_S
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {S : Finset V} (hS : S ∈ oddCycleSupports H) (hScard : S.card = 3)
    (hHdeg2 : ∀ u ∈ S, H.degree u = 2) (hpois : cleanSet G K S = ∅)
    {a b : V} (hab : a ≠ b) (ha3 : G.degree a = 3) (hb3 : G.degree b = 3)
    (hpair : ∀ v, G.degree v = 3 → v = a ∨ v = b) :
    a ∉ S ∧ b ∉ S := by
  have h_key : ∀ c d : V, c ≠ d → G.degree c = 3 → G.degree d = 3 → (∀ v, G.degree v = 3 → v = c ∨ v = d) → c ∉ S := by
    intros c d hcd hc hd hpair
    by_contra hcS
    have hdc : d ∉ S := by
      intro hdS
      obtain ⟨e, heS, he_ne_c, he_ne_d⟩ : ∃ e ∈ S, e ≠ c ∧ e ≠ d := by
        exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( S.erase c ) from by rw [ Finset.card_erase_of_mem hcS, hScard ] ; decide ) d )
      have he_deg4 : G.degree e = 4 := by
        grind +splitImp
      have he_poison : ∃ w, G.degree w = 3 ∧ (w = e ∨ K.Adj e w) := by
        apply poison_deg3_witness G H K hdeg heS hpois
      obtain ⟨w, hw_deg3, hw⟩ := he_poison
      have hw_in_S : w ∈ S := by
        grind
      have hw_ne_e : w ≠ e := by
        grind +ring
      have hw_adj_H : H.Adj e w := by
        apply cycle3_all_adj H (fun v => hsplit.2.2.2.2.1 v) hS hScard heS hw_in_S (by
        exact Ne.symm hw_ne_e)
      have hw_adj_K : ¬K.Adj e w := by
        exact hsplit.2.1 e w hw_adj_H
      exact hw_adj_K (by
      grind)
    have h_other_two : ∃ e e' : V, e ≠ e' ∧ e ∈ S ∧ e' ∈ S ∧ e ≠ c ∧ e' ≠ c ∧ e ≠ d ∧ e' ≠ d := by
      obtain ⟨ e, he, e', he', hee' ⟩ := Finset.two_lt_card.1 ( by linarith : 2 < Finset.card S );
      grind;
    obtain ⟨ e, e', hee', heS, he'S, hec, he'c, hed, he'd ⟩ := h_other_two
    have he_deg : G.degree e = 4 := by
      grind
    have he'_deg : G.degree e' = 4 := by
      grind
    have he_poison : ∃ w, G.degree w = 3 ∧ (w = e ∨ K.Adj e w) := by
      apply poison_deg3_witness G H K hdeg heS hpois
    have he'_poison : ∃ w, G.degree w = 3 ∧ (w = e' ∨ K.Adj e' w) := by
      apply poison_deg3_witness G H K hdeg he'S hpois
    generalize_proofs at *; (
    obtain ⟨ w, hw₁, hw₂ ⟩ := he_poison
    obtain ⟨ w', hw₁', hw₂' ⟩ := he'_poison
    have hw : w = d := by
      cases hpair w hw₁ <;> simp_all +decide only [cleanSet];
      cases hw₂ <;> simp_all +decide [ SimpleGraph.adj_comm ];
      have := hsplit.2.1 c e; simp_all +decide [ SimpleGraph.adj_comm ] ;
      exact this ( cycle3_all_adj H ( fun v => hsplit.2.2.2.2.1 v ) hS hScard hcS heS ( by tauto ) )
    have hw' : w' = d := by
      cases hpair w' hw₁' <;> simp_all +decide only [cleanSet] ;
      have := hsplit.2.1 e' c; simp_all +decide ;
      have := cycle3_all_adj H ( fun v => hsplit.2.2.2.2.1 v ) hS hScard he'S hcS; simp_all +decide ;
    generalize_proofs at *; (
    have hK_deg_d : K.degree d ≥ 2 := by
      have hK_deg_d : K.degree d ≥ Finset.card ({e, e'} : Finset V) := by
        refine' Finset.card_le_card _;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.adj_comm ];
        grind +splitImp
      generalize_proofs at *; (
      exact le_trans ( by simp +decide [ hee' ] ) hK_deg_d)
    generalize_proofs at *; (
    have hH_deg_d : H.degree d = 1 := by
      have := hsplit.2.2.2.2.2.1 d; ( have := hsplit.2.2.2.2.2.2 d; ( have := split_deg_sum G H K hsplit d; ( norm_num at *; omega; ) ) )
    generalize_proofs at *; (
    have hT_card : (Finset.univ.filter (fun v => H.degree v = 1)).card = 1 := by
      have hT_card : ∀ v, H.degree v = 1 → v = d := by
        intros v hv
        have hv_deg : G.degree v = 3 := by
          exact H_light_imp_deg3 G H K hdeg hsplit hv
        generalize_proofs at *; (
        cases hpair v hv_deg <;> simp_all +decide only [ne_eq])
      generalize_proofs at *; (
      exact Finset.card_eq_one.mpr ⟨ d, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hH_deg_d ⟩, fun v hv => hT_card v <| Finset.mem_filter.mp hv |>.2 ⟩ ⟩)
    generalize_proofs at *; (
    exact absurd ( deg3_lightness_parity G H K hdeg hsplit ) ( by simp +decide [ hT_card ] ))))));
  grind

/-
Every triangle vertex is `K`-adjacent to one of the two off-support
degree-3 vertices.
-/
private lemma poison_covered
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    {S : Finset V} (hpois : cleanSet G K S = ∅)
    {a b : V} (hanS : a ∉ S) (hbnS : b ∉ S)
    (hpair : ∀ v, G.degree v = 3 → v = a ∨ v = b) :
    ∀ z ∈ S, K.Adj z a ∨ K.Adj z b := by
  intro z hzS
  have hz_deg : G.degree z = 3 ∨ ∃ w, G.degree w = 3 ∧ K.Adj z w := by
    have := poison_deg3_witness G H K hdeg hzS hpois; aesop;
  grind +locals

/-
STEP H: both degree-3 vertices are `H`-light.
-/
private lemma poison_pair_Hlight
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {S : Finset V} (hScard : S.card = 3)
    {a b : V} (hab : a ≠ b) (ha3 : G.degree a = 3) (hb3 : G.degree b = 3)
    (hpair : ∀ v, G.degree v = 3 → v = a ∨ v = b)
    (hcov : ∀ z ∈ S, K.Adj z a ∨ K.Adj z b) :
    H.degree a = 1 ∧ H.degree b = 1 := by
  -- Consider `T := Finset.univ.filter (fun v => H.degree v = 1)`. `deg3_lightness_parity G H K hdeg hsplit : Even T.card`. `T ⊆ {a, b}`: any `v ∈ T` has `H.degree v = 1`, so `G.degree v = 3` (`H_light_imp_deg3`), so `v = a ∨ v = b` (`hpair`). Hence `T.card ≤ ({a,b}).card = 2` (`hab`). Since `Even T.card` and `T.card ≤ 2`, `T.card = 0` or `T.card = 2`.
  set T := Finset.univ.filter (fun v => H.degree v = 1)
  have hT_card : T.card ≤ 2 := by
    have hT_subset : T ⊆ {a, b} := by
      intro v hv; specialize hpair v; have := H_light_imp_deg3 G H K hdeg hsplit ( Finset.mem_filter.mp hv |>.2 ) ; aesop;
    exact le_trans ( Finset.card_le_card hT_subset ) ( Finset.card_insert_le _ _ )
  have hT_even : Even T.card := by
    convert deg3_lightness_parity G H K hdeg hsplit using 1
  have hT_cases : T.card = 0 ∨ T.card = 2 := by
    grind;
  cases' hT_cases with hT_zero hT_two;
  · -- If `T.card = 0`, then `a ∉ T` and `b ∉ T`, i.e. `H.degree a ≠ 1` and `H.degree b ≠ 1`; since `deg a = deg b = 3`, `H.degree a = 2` and `H.degree b = 2`, so `K.degree a = 1` and `K.degree b = 1`.
    have hK_deg_a : K.degree a = 1 := by
      have hH_deg_a : H.degree a = 2 := by
        have := hsplit.2.2.2.2.2.1 a; have := hsplit.2.2.2.2.1 a; have := split_deg_sum G H K hsplit a; simp_all +decide ;
        interval_cases _ : H.degree a <;> simp_all +decide;
        exact Finset.notMem_empty a ( hT_zero ▸ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by assumption ⟩ );
      linarith [ split_deg_sum G H K hsplit a ]
    have hK_deg_b : K.degree b = 1 := by
      have := hsplit.2.2.2.2.2.1 b; ( have := hsplit.2.2.2.2.1 b; ( have := split_deg_sum G H K hsplit b; ( simp_all +decide [ parity_simps ] ; ) ) );
      simp +zetaDelta at *;
      grind +splitIndPred;
    -- Since $S$ is covered by the neighbors of $a$ and $b$ in $K$, we have $S \subseteq K.neighborFinset a \cup K.neighborFinset b$.
    have hS_subset : S ⊆ K.neighborFinset a ∪ K.neighborFinset b := by
      intro z hz; specialize hcov z hz; simp_all +decide [ SimpleGraph.adj_comm ] ;
    have := Finset.card_le_card hS_subset; simp_all +decide ;
    exact absurd this ( by exact not_le_of_gt ( lt_of_le_of_lt ( Finset.card_union_le _ _ ) ( by simp +decide [ *, SimpleGraph.card_neighborFinset_eq_degree ] ) ) );
  · have hT_eq : T = {a, b} := by
      refine' Finset.eq_of_subset_of_card_le ( fun v hv => _ ) _;
      · have := H_light_imp_deg3 G H K hdeg hsplit ( Finset.mem_filter.mp hv |>.2 ) ; aesop;
      · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
    simp_all +decide [ Finset.ext_iff ];
    exact ⟨ Finset.mem_filter.mp ( hT_eq a |>.2 ( Or.inl rfl ) ) |>.2, Finset.mem_filter.mp ( hT_eq b |>.2 ( Or.inr rfl ) ) |>.2 ⟩

/-
STEPS I–J: the poison edges attach in configuration (i).
-/
private lemma poison_attach
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {S : Finset V} (hScard : S.card = 3)
    {a b : V} (hab : a ≠ b) (hKa : K.degree a = 2) (hKb : K.degree b = 2)
    (hcov : ∀ z ∈ S, K.Adj z a ∨ K.Adj z b) :
    ∃ p q z₁ z₂ z₃ : V,
      (p = a ∨ p = b) ∧ (q = a ∨ q = b) ∧ p ≠ q ∧
      S = {z₁, z₂, z₃} ∧
      K.Adj p z₁ ∧ K.Adj p z₂ ∧ K.Adj q z₃ ∧
      ((∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂) := by
  -- Let's assume without loss of generality that $a$ has two neighbors in $S$.
  wlog h_wlog : (Finset.filter (fun z => K.Adj z a) S).card = 2 generalizing a b;
  · by_cases h_card_b : (Finset.filter (fun z => K.Adj z b) S).card = 2;
    · convert this hab.symm hKb hKa ( fun z hz => Or.symm ( hcov z hz ) ) h_card_b using 1;
      simp +decide only [or_comm];
    · have h_card_a : (Finset.filter (fun z => K.Adj z a) S).card ≤ 2 := by
        have h_card_a : (Finset.filter (fun z => K.Adj z a) S).card ≤ (K.neighborFinset a).card := by
          exact Finset.card_le_card fun x hx => by simpa [ SimpleGraph.adj_comm ] using Finset.mem_filter.mp hx |>.2;
        exact h_card_a.trans ( by simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] at *; linarith )
      have h_card_b : (Finset.filter (fun z => K.Adj z b) S).card ≤ 2 := by
        have h_card_b : (Finset.filter (fun z => K.Adj z b) S).card ≤ (K.neighborFinset b).card := by
          exact Finset.card_le_card fun x hx => by simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact h_card_b.trans ( by simp +decide [ hKb ] );
      have h_card_union : (Finset.filter (fun z => K.Adj z a) S).card + (Finset.filter (fun z => K.Adj z b) S).card ≥ S.card := by
        rw [ ← Finset.card_union_add_card_inter ];
        exact le_add_right ( Finset.card_le_card fun x hx => by specialize hcov x hx; aesop );
      omega;
  · obtain ⟨z₁, z₂, hz₁, hz₂, hz⟩ : ∃ z₁ z₂ : V, z₁ ∈ S ∧ z₂ ∈ S ∧ z₁ ≠ z₂ ∧ K.Adj z₁ a ∧ K.Adj z₂ a ∧ ∀ z ∈ S, K.Adj z a → z = z₁ ∨ z = z₂ := by
      rcases Finset.card_eq_two.mp h_wlog with ⟨ z₁, z₂, hz₁, hz₂ ⟩;
      exact ⟨ z₁, z₂, by rw [ Finset.ext_iff ] at hz₂; specialize hz₂ z₁; aesop, by rw [ Finset.ext_iff ] at hz₂; specialize hz₂ z₂; aesop, hz₁, by rw [ Finset.ext_iff ] at hz₂; specialize hz₂ z₁; aesop, by rw [ Finset.ext_iff ] at hz₂; specialize hz₂ z₂; aesop, fun z hz hz' => by rw [ Finset.ext_iff ] at hz₂; specialize hz₂ z; aesop ⟩;
    -- Let's choose the third element $z₃$ from $S$.
    obtain ⟨z₃, hz₃⟩ : ∃ z₃ : V, z₃ ∈ S ∧ z₃ ≠ z₁ ∧ z₃ ≠ z₂ := by
      exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase S z₁ ) from by rw [ Finset.card_erase_of_mem hz₁, hScard ] ; decide ) z₂ );
    by_cases hz₃b : K.Adj z₃ b;
    · obtain ⟨y, hy⟩ : ∃ y : V, y ∈ K.neighborFinset b ∧ y ≠ z₃ := by
        exact Finset.exists_mem_ne ( by simp +decide [ hKb ] ) _;
      by_cases hyS : y ∈ S;
      · use b, a, z₃, y, if y = z₁ then z₂ else z₁;
        split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hz₃.1 ( Finset.insert_subset hz₁ ( Finset.singleton_subset_iff.mpr hz₂ ) ) ) ; aesop;
        · have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hz₃.1 ( Finset.insert_subset hyS ( Finset.singleton_subset_iff.mpr hz₁ ) ) ) ; simp_all +decide ;
          grind;
      · use a, b, z₁, z₂, z₃;
        simp_all +decide [ SimpleGraph.adj_comm ];
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hz₁, Finset.insert_subset_iff.mpr ⟨ hz₂, Finset.singleton_subset_iff.mpr hz₃.1 ⟩ ⟩ ) ] ; aesop;
        grind;
    · grind

end PoisonedShapeCore

/-- LADDER-PIN 8 (§6.1 + Strike-B B1; `poisoned_t2_shape`).  At a minimal split
of a t ≤ 2 graph, a poisoned odd `H`-cycle forces configuration (i): the cycle
is a triangle of degree-4 vertices, both degree-3 vertices are `H`-light path
ends, `K` is 2-regular, and (variant i-a or i-b) the poison edges attach as
`p → {z₁, z₂}`, `q → {z₃}` with `q`'s other `K`-edge off the triangle, or
`q → {z₂, z₃}`. -/
lemma poisoned_t2_shape
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    (S : Finset V) (hS : S ∈ oddCycleSupports H)
    (hpois : cleanSet G K S = ∅) :
    ∃ p q z₁ z₂ z₃ : V,
      p ≠ q ∧ G.degree p = 3 ∧ G.degree q = 3 ∧
      H.degree p = 1 ∧ H.degree q = 1 ∧
      S = {z₁, z₂, z₃} ∧ (∀ z ∈ S, G.degree z = 4) ∧
      K.Adj p z₁ ∧ K.Adj p z₂ ∧ K.Adj q z₃ ∧
      ((∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂) ∧
      (∀ v, K.degree v = 2) ∧
      (∃ w : H.Walk p q, w.IsPath) := by
  have := hmin.1; simp_all +decide [ IsEdgeSplit ] ;
  obtain ⟨a, b, hab, ha3, hb3, hpair⟩ : ∃ a b : V, a ≠ b ∧ G.degree a = 3 ∧ G.degree b = 3 ∧ (∀ v, G.degree v = 3 → v = a ∨ v = b) := by
    apply deg3_pair_of_numdeg3_two G (by
    have := poisoned_t2_card G H K hdeg hmin.1 ht2 hS ( fun u hu => oddCycleSupport_Hdeg2 H this.2.2.2.2.1 hS u hu ) hpois; aesop;);
  have hHdeg2 : ∀ u ∈ S, H.degree u = 2 := by
    exact oddCycleSupport_Hdeg2 H this.2.2.2.2.1 hS
  have hScard : S.card = 3 := by
    have := poisoned_t2_card G H K hdeg hmin.1 ht2 hS hHdeg2 hpois; aesop;
  have hanS : a ∉ S := by
    apply (poison_pair_notin_S G H K hdeg hmin.1 hS hScard hHdeg2 hpois hab ha3 hb3 hpair).left
  have hbnS : b ∉ S := by
    exact poison_pair_notin_S G H K hdeg hmin.1 hS hScard hHdeg2 hpois hab ha3 hb3 hpair |>.2
  have hcov : ∀ z ∈ S, K.Adj z a ∨ K.Adj z b := by
    apply poison_covered G H K hdeg hpois hanS hbnS hpair
  have hHa : H.degree a = 1 := by
    apply poison_pair_Hlight G H K hdeg hmin.1 hScard hab ha3 hb3 hpair hcov |>.1
  have hHb : H.degree b = 1 := by
    apply (poison_pair_Hlight G H K hdeg hmin.1 hScard hab ha3 hb3 hpair hcov).right
  have hKa : K.degree a = 2 := by
    linarith [ this.2.2.2.2.2.2 a ]
  have hKb : K.degree b = 2 := by
    linarith [ this.2.2.2.2.2.2 b ]
  obtain ⟨p, q, z₁, z₂, z₃, hp_ab, hq_ab, hpq, hSeq, hpz₁, hpz₂, hqz₃, hvar⟩ := poison_attach K hScard hab hKa hKb hcov;
  refine' ⟨ p, q, hpq, _, _, _, _, z₁, z₂, z₃, hSeq, _, hpz₁, hpz₂, hqz₃, hvar, _, _ ⟩;
  any_goals rcases hp_ab with ( rfl | rfl ) <;> simp +decide [ * ];
  any_goals rcases hq_ab with ( rfl | rfl ) <;> simp +decide [ * ];
  · grind +splitImp;
  · grind;
  · grind;
  · have h_reachable : H.Reachable p q := by
      apply reachable_of_two_odd;
      · rcases hp_ab with ( rfl | rfl ) <;> simp +decide [ * ];
      · grind +revert;
    exact ⟨ h_reachable.some.toPath.1, h_reachable.some.toPath.2 ⟩

/-
Helper: unfolded adjacency of a toggle.
-/
lemma toggled_adj_iff (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Sym2 V)) (u v : V) :
    (toggled H T).Adj u v ↔
      u ≠ v ∧ ((H.Adj u v ∧ s(u, v) ∉ T) ∨ (¬ H.Adj u v ∧ s(u, v) ∈ T)) := by
  unfold toggled; simp +decide [ SimpleGraph.fromEdgeSet ] ;
  simp +decide [ symmDiff, and_comm ]

/-
Helper (reusable): if a path `p` from `x` to `a` uses the edge `s(a,b)`
(necessarily its last edge, incident to the endpoint `a`), then peeling that
edge off yields a path from `x` to `b` avoiding `a` and `s(a,b)`, one shorter.
-/
lemma exists_isPath_peel_end {G : SimpleGraph V} {x a b : V}
    (p : G.Walk x a) (hp : p.IsPath) (he : s(a, b) ∈ p.edges) :
    ∃ q : G.Walk x b, q.IsPath ∧ s(a, b) ∉ q.edges ∧ q.length + 1 = p.length ∧
      a ∉ q.support ∧ (∀ v ∈ q.support, v ∈ p.support) := by
  induction' p with x y p ih generalizing b;
  · cases he;
  · by_cases h : s(ih, b) = s(y, p) <;> simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ];
    · aesop;
    · grind +suggestions

/-
Helper (reusable): a cycle through the edge `s(a,b)` (incident to its base
point `a`) minus that edge is a path from `a` to `b` of length one less.
-/
lemma exists_isPath_of_cycle_edge {G : SimpleGraph V} {a b : V}
    {c : G.Walk a a} (hc : c.IsCycle) (he : s(a, b) ∈ c.edges) :
    ∃ w : G.Walk a b, w.IsPath ∧ s(a, b) ∉ w.edges ∧ w.length + 1 = c.length := by
  obtain ⟨p, hp⟩ : ∃ p : G.Walk a a, c = p ∧ p.IsCycle := by
    use c;
  rcases p with ( _ | ⟨ h, p ⟩ ) <;> simp_all +decide;
  rcases he with ( ( rfl | ⟨ rfl, rfl ⟩ ) | he );
  · use p.reverse;
    simp_all +decide [ SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.cons_isCycle_iff ];
  · exact False.elim ( h.ne rfl );
  · obtain ⟨ q, hq ⟩ := exists_isPath_peel_end p ( by
      grind +suggestions ) he;
    refine' ⟨ Walk.cons h q, _, _, _ ⟩ <;> simp_all +decide [ Walk.cons_isPath_iff ];
    constructor <;> rintro rfl <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ]

/-
Helper (reusable): adjoining one edge `s(a,b)` whose every simple closing
path in `M` has odd length leaves the odd-cycle count unchanged.  This subsumes
the *bridge* case (no `a`–`b` path exists, so the hypothesis is vacuous) and the
*even-closure* case (the unique new cycle through `s(a,b)` has even length).
-/
lemma oddCycleCount_sup_edge_of_all_paths_odd
    (M : SimpleGraph V) [DecidableRel M.Adj] {a b : V} (hab : a ≠ b)
    (hpaths : ∀ w : M.Walk a b, w.IsPath → Odd w.length) :
    oddCycleCount (M ⊔ SimpleGraph.fromEdgeSet {s(a, b)}) = oddCycleCount M := by
  refine' congr_arg Finset.card _;
  -- By definition of `oddCycleSupports`, we are done if we show a set equality on the supports of odd cycles.
  ext S
  simp [oddCycleSupports];
  constructor <;> rintro ⟨ x, w, hw₁, hw₂, rfl ⟩;
  · by_cases he : s(a, b) ∈ w.edges;
    · -- Rotate `w` to base it at `a`: `w₀ := w.rotate (ha : a ∈ w.support)`, still a cycle (`hw₁.rotate`), same edges set and same length, and `s(a, b) ∈ w₀.edges`.
      obtain ⟨w₀, hw₀⟩ : ∃ w₀ : (M ⊔ fromEdgeSet {s(a, b)}).Walk a a, w₀.IsCycle ∧ s(a, b) ∈ w₀.edges ∧ w₀.length = w.length ∧ w₀.support.toFinset = w.support.toFinset := by
        obtain ⟨ha, hb⟩ : a ∈ w.support ∧ b ∈ w.support := by
          exact ⟨ by exact? , by exact? ⟩;
        refine' ⟨ w.rotate ha, _, _, _, _ ⟩;
        · exact hw₁.rotate ha;
        · rw [ SimpleGraph.Walk.rotate ];
          simp +decide [ SimpleGraph.Walk.edges_append, he ];
          have h_split : w.edges = (w.takeUntil a ha).edges ++ (w.dropUntil a ha).edges := by
            rw [ ← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec ];
          grind;
        · simp +decide [ SimpleGraph.Walk.rotate ];
          rw [ add_comm, ← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec ];
        · simp +decide [ Finset.ext_iff, List.mem_append, List.mem_reverse ];
      obtain ⟨w₁, hw₁⟩ : ∃ w₁ : (M ⊔ fromEdgeSet {s(a, b)}).Walk a b, w₁.IsPath ∧ s(a, b) ∉ w₁.edges ∧ w₁.length + 1 = w₀.length := by
        have := exists_isPath_of_cycle_edge hw₀.1 hw₀.2.1; aesop;
      -- Since every edge of `w₁` is in `M'.edgeSet = M.edgeSet ∪ {s(a, b)}` and is `≠ s(a, b)`, and `M'.edgeSet = M.edgeSet ∪ {s(a, b)}`, every edge of `w₁` lies in `M.edgeSet`; so `w' := w₁.transfer M (by …) : M.Walk a b` with `w'.IsPath` and `w'.length = w₁.length`.
      obtain ⟨w', hw'⟩ : ∃ w' : M.Walk a b, w'.IsPath ∧ w'.length = w₁.length := by
        have h_transfer : ∀ e ∈ w₁.edges, e ∈ M.edgeSet := by
          intro e he; have := w₁.edges_subset_edgeSet he; simp_all +decide [ SimpleGraph.edgeSet_sup ] ;
          grind;
        use w₁.transfer M h_transfer;
        simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      grind +splitIndPred;
    · use x, w.transfer M (by
      intro e he; have := w.edges_subset_edgeSet he; simp_all +decide [ SimpleGraph.edgeSet_sup ] ;
      grind);
      simp_all +decide [ SimpleGraph.Walk.transfer ];
      convert hw₁.transfer _;
  · refine' ⟨ x, w.map ( SimpleGraph.Hom.ofLE le_sup_left ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.map ]

/-- Helper (reusable): the odd-cycle count is monotone under the subgraph order. -/
lemma oddCycleCount_mono {M N : SimpleGraph V} (h : M ≤ N) :
    oddCycleCount M ≤ oddCycleCount N := by
  apply Finset.card_le_card
  intro S hS
  simp_all +decide [Finset.mem_filter, oddCycleSupports]
  obtain ⟨x, w, hw, hodd, hsupp⟩ := hS
  refine ⟨x, w.map (SimpleGraph.Hom.ofLE h), ?_, ?_, ?_⟩
  · exact hw.map (fun u v huv => by simpa using huv)
  · simpa using hodd
  · simpa [SimpleGraph.Walk.support_map, List.map_id''] using hsupp

/-- Count side, `H`-half of a canonical 3-move.  Given the toggle rewrites as a
deletion of the triangle edge `s(a,z₃)` followed by adjoining the two exposed
edges `s(a,p)`, `s(z₃,q)`, and the two adjoined edges only ever close odd
paths (bridge / even-closure), the `H`-count strictly drops (the deleted edge
lies on an odd cycle of the max-degree-2 graph `H`). -/
lemma canonical_H_count_lt (H : SimpleGraph V) [DecidableRel H.Adj]
    {a z₃ p q : V} (T : Finset (Sym2 V))
    (hrepr : toggled H T =
      (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)})
        ⊔ SimpleGraph.fromEdgeSet {s(z₃, q)})
    (hHmax : ∀ v, H.degree v ≤ 2)
    (haz₃ : H.Adj a z₃)
    {x0 : V} {tc : H.Walk x0 x0} (htc : tc.IsCycle) (htodd : Odd tc.length)
    (hte : s(a, z₃) ∈ tc.edges)
    (hsep1 : ∀ w : (H.deleteEdges {s(a, z₃)}).Walk a p, w.IsPath → Odd w.length)
    (hsep2 : ∀ w : (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).Walk z₃ q,
      w.IsPath → Odd w.length)
    (hap : a ≠ p) (hz₃q : z₃ ≠ q) :
    oddCycleCount (toggled H T) < oddCycleCount H := by
  classical
  rw [hrepr]
  rw [oddCycleCount_sup_edge_of_all_paths_odd _ hz₃q hsep2]
  rw [oddCycleCount_sup_edge_of_all_paths_odd _ hap hsep1]
  exact oddCycleCount_deleteEdges_lt H hHmax htc htodd haz₃ hte

/-- Count side, `K`-half of a canonical 3-move.  The toggle deletes the two
exposed `K`-edges `s(a,p)`, `s(z₃,q)` and adjoins the triangle edge `s(a,z₃)`;
when the two endpoints `a`, `z₃` are separated (no even connecting path), the
adjoined edge does not raise the odd-cycle count, so the `K`-count does not
increase. -/
lemma canonical_K_count_le (K : SimpleGraph V) [DecidableRel K.Adj]
    {a z₃ p q : V} (T : Finset (Sym2 V))
    (hrepr : toggled K T =
      K.deleteEdges {s(a, p), s(z₃, q)} ⊔ SimpleGraph.fromEdgeSet {s(a, z₃)})
    (hsep : ∀ w : (K.deleteEdges {s(a, p), s(z₃, q)}).Walk a z₃,
      w.IsPath → Odd w.length)
    (haz₃ : a ≠ z₃) :
    oddCycleCount (toggled K T) ≤ oddCycleCount K := by
  classical
  rw [hrepr, oddCycleCount_sup_edge_of_all_paths_odd _ haz₃ hsep]
  exact oddCycleCount_mono (SimpleGraph.deleteEdges_le _)

/-
Helper (reusable): a 3-vertex odd-cycle support is a triangle.
-/
lemma triangle_of_oddSupport (H : SimpleGraph V) [DecidableRel H.Adj]
    {z₁ z₂ z₃ : V} (hS : ({z₁, z₂, z₃} : Finset V) ∈ oddCycleSupports H) :
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧
      H.Adj z₁ z₂ ∧ H.Adj z₂ z₃ ∧ H.Adj z₁ z₃ := by
  obtain ⟨x, w, hw, hodd, hsupp⟩ : ∃ x : V,
    ∃ w : H.Walk x x, w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = {z₁, z₂, z₃} := by
      unfold oddCycleSupports at hS; aesop;
  have h_card : w.length = 3 := by
    have h_card : w.support.toFinset.card = w.length := by
      have := hw.support_nodup;
      have h_card : w.support.toFinset = w.support.tail.toFinset := by
        cases w <;> simp +decide [ SimpleGraph.Walk.support ] at *;
      rw [ h_card, List.toFinset_card_of_nodup this ] ; aesop;
    grind +suggestions;
  rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | w ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
  rcases hsupp with ⟨ ⟨ rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl ⟩, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
  all_goals simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ];
  all_goals tauto

/-
Helper (reusable): reachability cannot leave a set closed under adjacency.
-/
lemma not_reachable_of_closed {M : SimpleGraph V} {A : Finset V} {a b : V}
    (hclosed : ∀ u ∈ A, ∀ w, M.Adj u w → w ∈ A) (haA : a ∈ A) (hbA : b ∉ A) :
    ¬ M.Reachable a b := by
  contrapose! hbA; rcases hbA with ⟨ p ⟩ ; induction p ; aesop;
  grind

/-- Helper (reusable): an odd closed walk based at `a` contains an odd cycle
whose base vertex is reachable from `a`. -/
lemma exists_odd_cycle_reachable {M : SimpleGraph V} {a : V}
    (W : M.Walk a a) (hodd : Odd W.length) :
    ∃ (v : V) (c : M.Walk v v), c.IsCycle ∧ Odd c.length ∧ M.Reachable a v := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, W.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing a W with
  | _ n ih =>
  by_cases hcycle : W.IsCycle
  · exact ⟨a, W, hcycle, hodd, SimpleGraph.Reachable.refl a⟩
  · have hne1 : W.length ≠ 1 := by
      intro h1
      rcases W with _ | ⟨h₀, p⟩
      · simp at h1
      · have hp0 : p.length = 0 := by simpa [SimpleGraph.Walk.length_cons] using h1
        cases p with
        | nil => exact h₀.ne rfl
        | cons => simp [SimpleGraph.Walk.length_cons] at hp0
    have h3 : 3 ≤ W.length := by
      rcases hodd with ⟨k, hk⟩; omega
    have hnd : ¬ W.support.tail.Nodup := by
      intro hnd
      apply hcycle
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      refine ⟨?_, h3⟩
      have hnn : ¬ W.Nil := by rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnn]
      exact hnd
    obtain ⟨x, hxdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hnd
    rw [List.duplicate_iff_two_le_count] at hxdup
    have hxtail : x ∈ W.support.tail := List.count_pos_iff.mp (by omega)
    have hx : x ∈ W.support := List.mem_of_mem_tail hxtail
    have hreach_ax : M.Reachable a x := ⟨W.takeUntil x hx⟩
    set W' := W.rotate hx with hW'
    have hlen : W'.length = W.length := by
      have := (W.rotate_darts hx).perm.length_eq
      simpa [SimpleGraph.Walk.length_darts] using this
    have hcount' : 2 ≤ W'.support.tail.count x := by
      have hp := (W.support_rotate hx).perm
      rw [hp.count_eq]; exact hxdup
    have hnn' : ¬ W'.Nil := by rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
    obtain ⟨y, h₀, p, hpeq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnn'
    have hps : p.support = W'.support.tail := by rw [hpeq]; simp
    have hpcount : 2 ≤ p.support.count x := by rw [hps]; exact hcount'
    have hxp : x ∈ p.support := List.count_pos_iff.mp (by omega)
    set r := p.takeUntil x hxp with hr
    set q := p.dropUntil x hxp with hq
    have hsum : r.length + q.length = p.length := by
      have h1 := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec p hxp)
      rwa [SimpleGraph.Walk.length_append] at h1
    have hpsupp : p.support = r.support ++ q.support.tail := by
      rw [hr, hq, ← SimpleGraph.Walk.support_append, SimpleGraph.Walk.take_spec]
    have hrcount : r.support.count x = 1 := SimpleGraph.Walk.count_support_takeUntil_eq_one p hxp
    have hqpos : 0 < q.length := by
      by_contra hcon
      push_neg at hcon
      have hq0 : q.length = 0 := by omega
      have htail : q.support.tail = [] := by
        have hl : q.support.length = 1 := by rw [SimpleGraph.Walk.length_support, hq0]
        have h0 : q.support.tail.length = 0 := by simp [List.length_tail, hl]
        exact List.length_eq_zero_iff.mp h0
      have : p.support.count x = 1 := by
        rw [hpsupp, List.count_append, htail, hrcount]; simp
      omega
    have hwlen : W.length = r.length + 1 + q.length := by
      rw [← hlen, hpeq, SimpleGraph.Walk.length_cons, ← hsum]; ring
    rcases Nat.even_or_odd r.length with hre | hro
    · have hodd1 : Odd (SimpleGraph.Walk.cons h₀ r).length := by
        rw [SimpleGraph.Walk.length_cons]; exact hre.add_one
      have hlt1 : (SimpleGraph.Walk.cons h₀ r).length < n := by
        rw [SimpleGraph.Walk.length_cons]; omega
      obtain ⟨v, c, hc, hoddc, hvr⟩ := ih _ hlt1 (SimpleGraph.Walk.cons h₀ r) hodd1 rfl
      exact ⟨v, c, hc, hoddc, hreach_ax.trans hvr⟩
    · have hqodd : Odd q.length := by
        rw [Nat.odd_iff] at hodd hro ⊢; omega
      have hlt2 : q.length < n := by omega
      obtain ⟨v, c, hc, hoddc, hvr⟩ := ih _ hlt2 q hqodd rfl
      exact ⟨v, c, hc, hoddc, hreach_ax.trans hvr⟩

/-
Helper (reusable): if there is an odd `a`–`b` walk and no odd cycle is
reachable from `a`, then every `a`–`b` path is odd.
-/
lemma all_paths_odd_of_witness {M : SimpleGraph V} {a b : V}
    (w0 : M.Walk a b) (hw0 : Odd w0.length)
    (hbip : ∀ (v : V) (c : M.Walk v v), c.IsCycle → M.Reachable a v → ¬ Odd c.length) :
    ∀ w : M.Walk a b, w.IsPath → Odd w.length := by
  intro w hw;
  by_contra h_even_length;
  -- Consider $W := w.append w0.reverse : M.Walk a a$. Its length is $w.length + w0.reverse.length = w.length + w0.length$, which is $Even + Odd$, hence odd.
  set W : M.Walk a a := w.append w0.reverse
  have hW_odd : Odd W.length := by
    rw [ SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse ] ; simp_all +decide [ parity_simps ];
    exact iff_of_false ( by simpa using h_even_length ) ( by simpa using hw0 );
  obtain ⟨ v, c, hc, hodd, hv ⟩ := exists_odd_cycle_reachable W hW_odd; exact hbip v c hc hv hodd;

/-
Helper (reusable): a degree-2 vertex has exactly the two known neighbours.
-/
lemma adj_eq_of_deg2 (H : SimpleGraph V) [DecidableRel H.Adj] {v x y w : V}
    (hd : H.degree v = 2) (hx : H.Adj v x) (hy : H.Adj v y) (hxy : x ≠ y)
    (hw : H.Adj v w) : w = x ∨ w = y := by
  have h_neighborFinset : H.neighborFinset v = {x, y} := by
    rw [ Finset.eq_of_subset_of_card_le ( show { x, y } ⊆ H.neighborFinset v from by aesop_cat ) ( by aesop_cat ) ];
  replace h_neighborFinset := Finset.ext_iff.mp h_neighborFinset w; aesop;

/-
Helper (reusable): in a max-degree-2 graph, the vertex set of a path
carries no cycle (a path's support is acyclic).
-/
lemma no_cycle_of_path_support (H : SimpleGraph V) [DecidableRel H.Adj]
    (hHmax : ∀ v, H.degree v ≤ 2)
    {p q : V} {w0 : H.Walk p q} (hw0 : w0.IsPath)
    (hdp : H.degree p = 1) (hdq : H.degree q = 1)
    {v : V} {c : H.Walk v v} (hc : c.IsCycle)
    (hsub : ∀ u ∈ c.support, u ∈ w0.support) : False := by
  -- By `hsub`, every vertex `u` in `c.support` has `H.degree u = 2`.
  have h_deg2 : ∀ u ∈ c.support, H.degree u = 2 := fun u hu =>
    degree_eq_two_of_mem_cycle_support H hHmax hc hu
  -- Path neighbors are strong hf of cycle neighbors and graph degree: $H.neighborSet u = c.toSubgraph.neighborSet u \subseteq c.support$.
  have h_neighbor_subset : ∀ u ∈ c.support, ∀ x, H.Adj u x → x ∈ c.support := fun u hu x hx =>
    cycle_support_closed_adj H hHmax hc hu hx
  -- Index vertices by their unique position along `w0`: since `w0.IsPath`, `getVert` is injective on `{0,…,w0.length}`, and `u ∈ w0.support ↔ ∃ i ≤ w0.length, w0.getVert i = u`.
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i ≤ w0.length ∧ w0.getVert i ∈ c.support ∧ ∀ j : ℕ, j ≤ w0.length → w0.getVert j ∈ c.support → i ≤ j := by
    obtain ⟨i, hi⟩ : ∃ i : ℕ, i ≤ w0.length ∧ w0.getVert i ∈ c.support := by
      have := hsub _ ( c.start_mem_support );
      rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at this; aesop;
    exact ⟨ Nat.find ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w0.length, w0.getVert i ∈ c.support ), Nat.find_spec ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w0.length, w0.getVert i ∈ c.support ) |>.1, Nat.find_spec ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w0.length, w0.getVert i ∈ c.support ) |>.2, fun j hj hj' => Nat.find_min' _ ⟨ hj, hj' ⟩ ⟩;
  rcases i with ( _ | i ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
  have := h_neighbor_subset _ hi.2.1 _ ( show H.Adj ( w0.getVert ( i + 1 ) ) ( w0.getVert i ) from ?_ );
  · linarith [ hi.2.2 i ( Nat.le_of_lt hi.1 ) this ];
  · convert w0.adj_getVert_succ ( show i < w0.length from hi.1 ) |> SimpleGraph.Adj.symm using 1

/-
Helper (reusable): in a max-degree-2 graph, all neighbours of vertices on a
path (with degree-1 endpoints) stay on the path — the path's support is closed
under adjacency.
-/
lemma path_support_closed (H : SimpleGraph V) [DecidableRel H.Adj]
    (hHmax : ∀ v, H.degree v ≤ 2)
    {p q : V} {w0 : H.Walk p q} (hw0 : w0.IsPath) (hpq : p ≠ q)
    (hdp : H.degree p = 1) (hdq : H.degree q = 1) :
    ∀ u ∈ w0.support, ∀ w, H.Adj u w → w ∈ w0.support := by
  intro u hu w hw
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i ≤ w0.length ∧ u = w0.getVert i := by
    have := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu;
    tauto;
  by_cases hi0 : i = 0 <;> by_cases hil : i = w0.length <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
  · cases w0 <;> aesop;
  · rcases w0 with ( _ | ⟨ _, _, w0 ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.support ];
    · have := Finset.card_eq_one.mp hdp; obtain ⟨ x, hx ⟩ := this; have := Finset.card_eq_one.mp hdq; obtain ⟨ y, hy ⟩ := this; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    · have := Finset.card_eq_one.mp hdp; obtain ⟨ x, hx ⟩ := this; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
  · have h_unique_neighbor : H.neighborFinset q = {w} := by
      have := Finset.card_eq_one.mp hdq;
      obtain ⟨ a, ha ⟩ := this; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
    replace h_unique_neighbor := Finset.ext_iff.mp h_unique_neighbor ( w0.getVert ( w0.length - 1 ) ) ; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
    exact h_unique_neighbor.mp ( by
      convert w0.adj_getVert_succ ( show w0.length - 1 < w0.length from Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ) |> SimpleGraph.Adj.symm using 1;
      rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hi0 ), SimpleGraph.Walk.getVert_length ] ) ▸ w0.getVert_mem_support _;
  · have h_deg : H.degree (w0.getVert i) = 2 := by
      have h_deg : H.Adj (w0.getVert i) (w0.getVert (i - 1)) ∧ H.Adj (w0.getVert i) (w0.getVert (i + 1)) := by
        have h_neigh : ∀ j : ℕ, j < w0.length → H.Adj (w0.getVert j) (w0.getVert (j + 1)) := by
          grind +suggestions;
        exact ⟨ by simpa [ SimpleGraph.adj_comm ] using h_neigh ( i - 1 ) ( by omega ) |> SimpleGraph.Adj.symm |> fun h => by cases i <;> tauto, h_neigh i ( by omega ) ⟩;
      have h_distinct : w0.getVert (i - 1) ≠ w0.getVert (i + 1) := by
        have := hw0.getVert_injOn ( show i - 1 ≤ w0.length from Nat.sub_le_of_le_add <| by linarith ) ( show i + 1 ≤ w0.length from by omega ) ; aesop;
      exact le_antisymm ( hHmax _ ) ( Finset.one_lt_card.2 ⟨ w0.getVert ( i - 1 ), by aesop, w0.getVert ( i + 1 ), by aesop ⟩ );
    have h_adj : H.Adj (w0.getVert i) (w0.getVert (i - 1)) ∧ H.Adj (w0.getVert i) (w0.getVert (i + 1)) := by
      have h_adj : ∀ j : ℕ, j < w0.length → H.Adj (w0.getVert j) (w0.getVert (j + 1)) := by
        grind +suggestions;
      exact ⟨ by simpa [ SimpleGraph.adj_comm ] using h_adj ( i - 1 ) ( Nat.lt_of_le_of_lt ( Nat.pred_le _ ) ( lt_of_le_of_ne hi.1 hil ) ) |> fun h => by cases i <;> tauto, h_adj i ( lt_of_le_of_ne hi.1 hil ) ⟩;
    have h_adj : w = w0.getVert (i - 1) ∨ w = w0.getVert (i + 1) := by
      apply adj_eq_of_deg2 H h_deg h_adj.left h_adj.right;
      · have := hw0.getVert_injOn ( show i - 1 ≤ w0.length from Nat.sub_le_of_le_add <| by linarith ) ( show i + 1 ≤ w0.length from Nat.succ_le_of_lt <| lt_of_le_of_ne hi.1 hil ) ; simp_all +decide ;
      · exact hw;
    rcases h_adj with ( rfl | rfl ) <;> simp +decide [ SimpleGraph.Walk.getVert_mem_support ]

/-
Representation of the `H`-side canonical toggle as delete-one-edge then
adjoin-two-edges.
-/
lemma toggled_H_repr (H : SimpleGraph V) [DecidableRel H.Adj]
    {a z₃ p q : V}
    (haz : H.Adj a z₃) (hap : ¬ H.Adj a p) (hzq : ¬ H.Adj z₃ q)
    (hapne : a ≠ p) (hzqne : z₃ ≠ q)
    (h1 : s(a, p) ≠ s(a, z₃)) (h2 : s(a, p) ≠ s(z₃, q)) (h3 : s(a, z₃) ≠ s(z₃, q)) :
    toggled H {s(a, p), s(a, z₃), s(z₃, q)}
      = (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)})
        ⊔ SimpleGraph.fromEdgeSet {s(z₃, q)} := by
  have hazne : a ≠ z₃ := haz.ne
  have haqne : a ≠ q := fun h => hzq ((h ▸ haz).symm)
  have hzpne : z₃ ≠ p := fun h => h1 (by rw [h])
  ext u v
  rw [toggled_adj_iff]
  simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
    Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hE1 : s(u, v) = s(a, p)
  · have huv : u ≠ v := by
      rw [Sym2.eq_iff] at hE1; rcases hE1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hapne
      · exact fun h => hapne h.symm
    have hnadj : ¬ H.Adj u v := by
      rw [Sym2.eq_iff] at hE1; rcases hE1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hap
      · exact fun h => hap h.symm
    have n2 : ¬ s(u, v) = s(a, z₃) := by rw [hE1]; exact h1
    have n3 : ¬ s(u, v) = s(z₃, q) := by rw [hE1]; exact h2
    simp [hE1, n2, n3, huv, hnadj]
  · by_cases hE2 : s(u, v) = s(a, z₃)
    · have huv : u ≠ v := by
        rw [Sym2.eq_iff] at hE2; rcases hE2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hazne
        · exact fun h => hazne h.symm
      have hadj : H.Adj u v := by
        rw [Sym2.eq_iff] at hE2; rcases hE2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact haz
        · exact haz.symm
      have n3 : ¬ s(u, v) = s(z₃, q) := by rw [hE2]; exact h3
      simp [hE1, hE2, n3, huv, hadj, hapne, hazne, haqne, hzpne]
    · by_cases hE3 : s(u, v) = s(z₃, q)
      · have huv : u ≠ v := by
          rw [Sym2.eq_iff] at hE3; rcases hE3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hzqne
          · exact fun h => hzqne h.symm
        have hnadj : ¬ H.Adj u v := by
          rw [Sym2.eq_iff] at hE3; rcases hE3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hzq
          · exact fun h => hzq h.symm
        simp [hE1, hE2, hE3, huv, hnadj]
      · have hne_adj : H.Adj u v → u ≠ v := fun h => h.ne
        simp only [hE1, hE2, hE3, or_self, or_false, false_or, false_and, and_false,
          not_false_eq_true, and_true, ne_eq]
        tauto

/-
Representation of the `K`-side canonical toggle as delete-two-edges then
adjoin-one-edge.
-/
lemma toggled_K_repr (K : SimpleGraph V) [DecidableRel K.Adj]
    {a z₃ p q : V}
    (hap : K.Adj a p) (hzq : K.Adj z₃ q) (haz : ¬ K.Adj a z₃)
    (hazne : a ≠ z₃)
    (h1 : s(a, p) ≠ s(a, z₃)) (h2 : s(a, p) ≠ s(z₃, q)) (h3 : s(a, z₃) ≠ s(z₃, q)) :
    toggled K {s(a, p), s(a, z₃), s(z₃, q)}
      = K.deleteEdges {s(a, p), s(z₃, q)} ⊔ SimpleGraph.fromEdgeSet {s(a, z₃)} := by
  ext u v; simp +decide [ toggled_adj_iff, SimpleGraph.fromEdgeSet_adj, SimpleGraph.deleteEdges_adj ] ;
  by_cases hu : u = a <;> by_cases hv : v = a <;> simp_all +decide [ SimpleGraph.adj_comm ];
  · by_cases hv : v = p <;> by_cases hv' : v = z₃ <;> simp_all +decide [ SimpleGraph.adj_comm ];
    exact fun _ => Ne.symm ‹_›;
  · by_cases hu' : u = p <;> by_cases hu'' : u = z₃ <;> simp_all +decide [ SimpleGraph.adj_comm ];
  · by_cases huv : u = v <;> simp_all +decide [ SimpleGraph.adj_comm ];
    exact fun h => ⟨ fun hu hv => h <| by have := hzq.symm; aesop, fun hu hv => h <| by have := hzq.symm; aesop ⟩

/-
The `H`-side bridge separation: after deleting the triangle edge `s(a,z₃)`,
the triangle vertex `a` cannot reach the off-triangle vertex `p`.
-/
lemma hsep1_H (H : SimpleGraph V) [DecidableRel H.Adj]
    {a cm z₃ p : V} (hac : H.Adj a cm) (haz : H.Adj a z₃) (hcz : H.Adj cm z₃)
    (hda : H.degree a = 2) (hdcm : H.degree cm = 2) (hdz : H.degree z₃ = 2)
    (hacne : a ≠ cm) (hazne : a ≠ z₃) (hcmz : cm ≠ z₃)
    (hpa : p ≠ a) (hpcm : p ≠ cm) (hpz : p ≠ z₃) :
    ¬ (H.deleteEdges {s(a, z₃)}).Reachable a p := by
  apply not_reachable_of_closed (A := ({a, cm, z₃} : Finset V));
  · intro u hu w hadj
    have hadjH : H.Adj u w := SimpleGraph.deleteEdges_le _ hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl
    · rcases adj_eq_of_deg2 H hda hac haz hcmz hadjH with h | h <;> tauto
    · rcases adj_eq_of_deg2 H hdcm hac.symm hcz hazne hadjH with h | h <;> tauto
    · rcases adj_eq_of_deg2 H hdz haz.symm hcz.symm hacne hadjH with h | h <;> tauto
  · simp +decide;
  · aesop

/-- Helper (reusable): degree after adjoining one fresh edge `s(x,y)`. -/
lemma degree_sup_edge (M : SimpleGraph V) [DecidableRel M.Adj] {x y : V}
    (hxy : x ≠ y) (hnadj : ¬ M.Adj x y) (v : V) :
    (M ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).degree v
      = M.degree v + (if v = x ∨ v = y then 1 else 0) := by
  classical
  have hchar : ∀ w, (M ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).Adj v w ↔
      (M.Adj v w ∨ (s(v,w) = s(x,y) ∧ v ≠ w)) := by
    intro w; simp [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : v = x ∨ v = y
  · rcases hv with rfl | rfl
    · have hset : (M ⊔ SimpleGraph.fromEdgeSet {s(v, y)}).neighborFinset v
          = insert y (M.neighborFinset v) := by
        ext w; simp only [SimpleGraph.mem_neighborFinset, hchar, Finset.mem_insert]
        constructor
        · rintro (h | ⟨he, hne⟩)
          · exact Or.inr h
          · left; rw [Sym2.eq_iff] at he; aesop
        · rintro (rfl | h)
          · exact Or.inr ⟨rfl, hxy⟩
          · exact Or.inl h
      rw [hset, Finset.card_insert_of_notMem (by simp [SimpleGraph.mem_neighborFinset, hnadj])]
      simp
    · have hset : (M ⊔ SimpleGraph.fromEdgeSet {s(x, v)}).neighborFinset v
          = insert x (M.neighborFinset v) := by
        ext w; simp only [SimpleGraph.mem_neighborFinset, hchar, Finset.mem_insert]
        constructor
        · rintro (h | ⟨he, hne⟩)
          · exact Or.inr h
          · left; rw [Sym2.eq_iff] at he; aesop
        · rintro (rfl | h)
          · exact Or.inr ⟨by rw [Sym2.eq_iff]; tauto, fun h => hxy (by rw[h])⟩
          · exact Or.inl h
      rw [hset, Finset.card_insert_of_notMem (by simp only [SimpleGraph.mem_neighborFinset]; intro h; exact hnadj h.symm)]
      simp
  · push_neg at hv
    have hset : (M ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).neighborFinset v = M.neighborFinset v := by
      ext w; simp only [SimpleGraph.mem_neighborFinset, hchar]
      constructor
      · rintro (h | ⟨he, hne⟩)
        · exact h
        · exfalso; rw [Sym2.eq_iff] at he; rcases he with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp_all
      · exact Or.inl
    rw [hset]; simp [hv.1, hv.2]

/-- The `H`-side even-closure parity: every `z₃`–`q` path in the graph obtained
by deleting `s(a,z₃)` and adjoining `s(a,p)` has odd length. -/
lemma hsep2_H (H : SimpleGraph V) [DecidableRel H.Adj]
    (hHmax : ∀ v, H.degree v ≤ 2)
    {a cm z₃ p q : V}
    (hac : H.Adj a cm) (haz : H.Adj a z₃) (hcz : H.Adj cm z₃)
    (hda : H.degree a = 2) (hdz : H.degree z₃ = 2)
    (hacne : a ≠ cm) (hazne : a ≠ z₃) (hcmz : cm ≠ z₃)
    {w0 : H.Walk p q} (hw0 : w0.IsPath) (hw0even : Even w0.length) (hpq : p ≠ q)
    (hdp : H.degree p = 1) (hdq : H.degree q = 1)
    (hap : ¬ H.Adj a p)
    (hane : a ∉ w0.support) (hcmne : cm ∉ w0.support) (hzne : z₃ ∉ w0.support)
    (hsep1 : ¬ (H.deleteEdges {s(a, z₃)}).Reachable a p) :
    ∀ w : (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).Walk z₃ q,
      w.IsPath → Odd w.length := by
  classical
  have hpmem : p ∈ w0.support := w0.start_mem_support
  have hqmem : q ∈ w0.support := w0.end_mem_support
  have hpa : p ≠ a := fun h => hane (h ▸ hpmem)
  have hpz : p ≠ z₃ := fun h => hzne (h ▸ hpmem)
  have hqa : q ≠ a := fun h => hane (h ▸ hqmem)
  have hqz : q ≠ z₃ := fun h => hzne (h ▸ hqmem)
  have hap_ne : a ≠ p := fun h => hpa h.symm
  have hDap : ¬ (H.deleteEdges {s(a, z₃)}).Adj a p := fun h => hap (SimpleGraph.deleteEdges_le _ h)
  have key : ∀ v, (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).degree v
      = (H.degree v - (if v = a ∨ v = z₃ then 1 else 0)) + (if v = a ∨ v = p then 1 else 0) := by
    intro v
    rw [degree_sup_edge (H.deleteEdges {s(a, z₃)}) hap_ne hDap v,
      degree_deleteEdges_single H a z₃ haz v]
  have hNz3 : (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).degree z₃ = 1 := by
    rw [key z₃, hdz]
    rw [if_pos (Or.inr rfl), if_neg (by rintro (h|h); exacts [hazne h.symm, hpz h.symm])]
  have hNq : (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).degree q = 1 := by
    rw [key q, hdq]
    rw [if_neg (by rintro (h|h); exacts [hqa h, hqz h]),
      if_neg (by rintro (h|h); exacts [hqa h, hpq h.symm])]
  have hNmax : ∀ v, (H.deleteEdges {s(a, z₃)} ⊔ SimpleGraph.fromEdgeSet {s(a, p)}).degree v ≤ 2 := by
    intro v; rw [key v]
    by_cases hva : v = a
    · subst hva; rw [if_pos (Or.inl rfl), if_pos (Or.inl rfl)]; omega
    · by_cases hvp : v = p
      · subst hvp; rw [if_neg (by rintro (h|h); exacts [hva h, hpz h]), if_pos (Or.inr rfl)]; omega
      · by_cases hvz : v = z₃
        · subst hvz; rw [if_pos (Or.inr rfl), if_neg (by rintro (h|h); exacts [hva h, hvp h])]; omega
        · rw [if_neg (by rintro (h|h); exacts [hva h, hvz h]),
            if_neg (by rintro (h|h); exacts [hva h, hvp h])]
          have := hHmax v; omega
  set D := H.deleteEdges {s(a, z₃)} with hD
  set N := D ⊔ SimpleGraph.fromEdgeSet {s(a, p)} with hN
  have e1 : s(z₃, cm) ≠ s(a, z₃) := by
    rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hazne h.1.symm, fun h => hacne h.2.symm⟩
  have e2 : s(cm, a) ≠ s(a, z₃) := by
    rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hacne h.1.symm, fun h => hcmz h.1⟩
  have hz₃cm : N.Adj z₃ cm := by
    rw [hN, SimpleGraph.sup_adj]; left
    rw [hD, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]; exact ⟨hcz.symm, e1⟩
  have hcma : N.Adj cm a := by
    rw [hN, SimpleGraph.sup_adj]; left
    rw [hD, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]; exact ⟨hac.symm, e2⟩
  have hap_N : N.Adj a p := by
    rw [hN, SimpleGraph.sup_adj]; right
    rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]; exact ⟨rfl, hap_ne⟩
  have hnotedge : s(a, z₃) ∉ w0.edges := fun he => hane (w0.fst_mem_support_of_mem_edges he)
  have hw0edges : ∀ e ∈ w0.edges, e ∈ D.edgeSet := by
    intro e he
    rw [hD, SimpleGraph.edgeSet_deleteEdges]
    exact ⟨w0.edges_subset_edgeSet he, fun hc => hnotedge ((Set.mem_singleton_iff.mp hc) ▸ he)⟩
  set w0N : N.Walk p q := (w0.transfer D hw0edges).map (SimpleGraph.Hom.ofLE le_sup_left) with hw0N
  have hw0Nsupp : ∀ x, x ∈ w0N.support ↔ x ∈ w0.support := by
    intro x; rw [hw0N, SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_transfer]; simp
  have hw0Nlen : w0N.length = w0.length := by
    rw [hw0N, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_transfer]
  have hw0NPath : w0N.IsPath := by
    rw [hw0N]; exact (SimpleGraph.Walk.mapLe_isPath le_sup_left).mpr (hw0.transfer hw0edges)
  set w0' : N.Walk z₃ q :=
    SimpleGraph.Walk.cons hz₃cm (SimpleGraph.Walk.cons hcma (SimpleGraph.Walk.cons hap_N w0N)) with hw0'
  have hw0'len : w0'.length = w0.length + 3 := by
    rw [hw0', SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_cons, hw0Nlen]
  have hw0'odd : Odd w0'.length := by
    rw [hw0'len]; rcases hw0even with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have hw0'Path : w0'.IsPath := by
    rw [hw0', SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff,
      SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨⟨⟨hw0NPath, ?_⟩, ?_⟩, ?_⟩
    · rw [hw0Nsupp]; exact hane
    · rw [SimpleGraph.Walk.support_cons]; simp only [List.mem_cons]
      rintro (h | h)
      · exact hacne h.symm
      · exact hcmne ((hw0Nsupp cm).mp h)
    · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
      simp only [List.mem_cons]
      rintro (h | h | h)
      · exact hcmz h.symm
      · exact hazne h.symm
      · exact hzne ((hw0Nsupp z₃).mp h)
  have hbip : ∀ (v : V) (c : N.Walk v v), c.IsCycle → N.Reachable z₃ v → ¬ Odd c.length := by
    intro v c hc hreach hodd
    have hclosed : ∀ u ∈ w0'.support.toFinset, ∀ w, N.Adj u w → w ∈ w0'.support.toFinset := by
      intro u hu w hadj
      rw [List.mem_toFinset] at hu ⊢
      exact path_support_closed N hNmax hw0'Path hqz.symm hNz3 hNq u hu w hadj
    have hcsub : ∀ u ∈ c.support, u ∈ w0'.support := by
      intro u hu
      by_contra hunot
      have hru : N.Reachable z₃ u := hreach.trans (c.takeUntil u hu).reachable
      exact not_reachable_of_closed hclosed
        (List.mem_toFinset.mpr w0'.start_mem_support)
        (fun h => hunot (List.mem_toFinset.mp h)) hru
    exact no_cycle_of_path_support N hNmax hw0'Path hNz3 hNq hc hcsub
  exact all_paths_odd_of_witness w0' hw0'odd hbip

/-- Helper (reusable): a vertex of degree ≤ 1 lying on a path is one of the two
endpoints of the path. -/
lemma endpoint_of_deg_le_one {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    {P : G.Walk x y} (hP : P.IsPath) {v : V} (hv : v ∈ P.support) (hdeg : G.degree v ≤ 1) :
    v = x ∨ v = y := by
  obtain ⟨i, hget, hile⟩ := (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hv
  by_contra hcon
  push_neg at hcon
  obtain ⟨hcx, hcy⟩ := hcon
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact absurd (by rw [← hget, h, SimpleGraph.Walk.getVert_zero]) hcx
    · exact h
  have hilt : i < P.length := by
    rcases lt_or_eq_of_le hile with h | h
    · exact h
    · exact absurd (by rw [← hget, h, SimpleGraph.Walk.getVert_length]) hcy
  have hadj1 : G.Adj v (P.getVert (i - 1)) := by
    have := P.adj_getVert_succ (show i - 1 < P.length by omega)
    rw [Nat.sub_add_cancel hi0] at this
    rw [← hget]; exact this.symm
  have hadj2 : G.Adj v (P.getVert (i + 1)) := by
    have := P.adj_getVert_succ hilt
    rw [← hget]; exact this
  have hne : P.getVert (i - 1) ≠ P.getVert (i + 1) := by
    have hinj := hP.getVert_injOn
    intro h
    exact absurd (hinj (by simp; omega) (by simp; omega) h) (by omega)
  have h2 : 2 ≤ G.degree v := by
    have hsub : ({P.getVert (i - 1), P.getVert (i + 1)} : Finset V) ⊆ G.neighborFinset v := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [SimpleGraph.mem_neighborFinset, hadj1, hadj2]
    calc 2 = ({P.getVert (i - 1), P.getVert (i + 1)} : Finset V).card := by rw [Finset.card_pair hne]
      _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
      _ = G.degree v := rfl
  omega

/-- The `K`-side arc separation (2-regular `K`): for one of the two canonical
moves, after deleting the two exposed `K`-edges the vertex `a ∈ {z₁,z₂}` cannot
reach `z₃`. -/
lemma k_arc_separation (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK2 : ∀ v, K.degree v = 2)
    {p q z₁ z₂ z₃ : V}
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hz₁z₂ : z₁ ≠ z₂) (hpq : p ≠ q)
    (hz₁z₃ : z₁ ≠ z₃) (hz₂z₃ : z₂ ≠ z₃) (hpz₃ : p ≠ z₃) (hqz₁ : q ≠ z₁) (hqz₂ : q ≠ z₂) :
    ¬ (K.deleteEdges {s(z₁, p), s(z₃, q)}).Reachable z₁ z₃ ∨
    ¬ (K.deleteEdges {s(z₂, p), s(z₃, q)}).Reachable z₂ z₃ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hR1, hR2⟩ := hcon
  have hpnz1 : p ≠ z₁ := hpz₁.ne
  have hpnz2 : p ≠ z₂ := hpz₂.ne
  have hqnz3 : q ≠ z₃ := hqz₃.ne
  have hchar : (∀ w, s(z₁, w) ∈ ({s(z₁,p),s(z₂,p),s(z₃,q)} : Set (Sym2 V)) ↔ w = p) ∧
      (∀ w, s(z₂, w) ∈ ({s(z₁,p),s(z₂,p),s(z₃,q)} : Set (Sym2 V)) ↔ w = p) ∧
      (∀ w, s(z₃, w) ∈ ({s(z₁,p),s(z₂,p),s(z₃,q)} : Set (Sym2 V)) ↔ w = q) := by
    refine ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩ <;>
      (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
       constructor <;> intro h <;> simp_all <;> tauto)
  have degG' : ∀ (v nb : V), K.Adj v nb →
      (∀ w, s(v, w) ∈ ({s(z₁,p),s(z₂,p),s(z₃,q)} : Set (Sym2 V)) ↔ w = nb) →
      (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).degree v = 1 := by
    intro v nb hvnb hc
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hset : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).neighborFinset v
        = (K.neighborFinset v).erase nb := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hadj, hnin⟩; exact ⟨fun hh => hnin ((hc w).mpr hh), hadj⟩
      · rintro ⟨hwnb, hadj⟩; exact ⟨hadj, fun hmem => hwnb ((hc w).mp hmem)⟩
    rw [hset, Finset.card_erase_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hvnb),
      SimpleGraph.card_neighborFinset_eq_degree, hK2]
  have hdz1 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).degree z₁ = 1 := degG' z₁ p hpz₁.symm hchar.1
  have hdz2 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).degree z₂ = 1 := degG' z₂ p hpz₂.symm hchar.2.1
  have hdz3 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).degree z₃ = 1 := degG' z₃ q hqz₃.symm hchar.2.2
  have hG'max : ∀ v, (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).degree v ≤ 2 := fun v =>
    (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)).trans (le_of_eq (hK2 v))
  have degp : ∀ (za : V), K.Adj p za →
      (K.deleteEdges {s(za, p), s(z₃, q)}).degree p = 1 := by
    intro za hpza
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hset : (K.deleteEdges {s(za, p), s(z₃, q)}).neighborFinset p = (K.neighborFinset p).erase za := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj, Finset.mem_erase,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hadj, hnin⟩; refine ⟨?_, hadj⟩; rintro rfl
        exact hnin (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; left; rw [Sym2.eq_iff]; tauto)
      · rintro ⟨hwza, hadj⟩; refine ⟨hadj, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨?_, ?_⟩
        · rw [Sym2.eq_iff, not_or]; exact ⟨fun h => hpza.ne h.1, fun h => hwza h.2⟩
        · rw [Sym2.eq_iff, not_or]; exact ⟨fun h => hpz₃ h.1, fun h => hpq h.1⟩
    rw [hset, Finset.card_erase_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hpza),
      SimpleGraph.card_neighborFinset_eq_degree, hK2]
  have hGR1 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).Reachable z₁ z₃ := by
    obtain ⟨W0⟩ := hR1
    have hP1path := W0.bypass_isPath
    have hpnotin : p ∉ W0.bypass.support := by
      intro hp
      rcases endpoint_of_deg_le_one hP1path hp (degp z₁ hpz₁).le with h | h
      · exact hpnz1 h
      · exact hpz₃ h
    refine ⟨W0.bypass.transfer _ ?_⟩
    intro e he
    have h1 := W0.bypass.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h1
    have hene : e ≠ s(z₂, p) := by rintro rfl; exact hpnotin (W0.bypass.snd_mem_support_of_mem_edges he)
    rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff]
    refine ⟨h1.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1.2.1, hene, h1.2.2⟩
  have hGR2 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).Reachable z₂ z₃ := by
    obtain ⟨W0⟩ := hR2
    have hP2path := W0.bypass_isPath
    have hpnotin : p ∉ W0.bypass.support := by
      intro hp
      rcases endpoint_of_deg_le_one hP2path hp (degp z₂ hpz₂).le with h | h
      · exact hpnz2 h
      · exact hpz₃ h
    refine ⟨W0.bypass.transfer _ ?_⟩
    intro e he
    have h1 := W0.bypass.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h1
    have hene : e ≠ s(z₁, p) := by rintro rfl; exact hpnotin (W0.bypass.snd_mem_support_of_mem_edges he)
    rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff]
    refine ⟨h1.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hene, h1.2.1, h1.2.2⟩
  have hR12 : (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).Reachable z₁ z₂ := hGR1.trans hGR2.symm
  obtain ⟨W⟩ := hGR1
  have hPpath := W.bypass_isPath
  have hclosed : ∀ u ∈ W.bypass.support.toFinset, ∀ w,
      (K.deleteEdges {s(z₁,p),s(z₂,p),s(z₃,q)}).Adj u w → w ∈ W.bypass.support.toFinset := by
    intro u hu w hadj
    rw [List.mem_toFinset] at hu ⊢
    exact path_support_closed _ hG'max hPpath hz₁z₃ hdz1 hdz3 u hu w hadj
  have hz2mem : z₂ ∈ W.bypass.support := by
    by_contra h
    exact (not_reachable_of_closed hclosed (List.mem_toFinset.mpr W.bypass.start_mem_support)
      (fun hh => h (List.mem_toFinset.mp hh))) hR12
  rcases endpoint_of_deg_le_one hPpath hz2mem hdz2.le with h | h
  · exact hz₁z₂ h.symm
  · exact hz₂z₃ h

/-- LADDER-PIN 9 (Proposition 6.2).  If the `p`–`q` `H`-path has EVEN length,
some canonical 3-move is strict (the arc case analysis). -/
lemma canonical_strict_of_ellP_even
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPeven : ∃ w : H.Walk p q, w.IsPath ∧ Even w.length) :
    ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
  classical
  have hsplit : IsEdgeSplit G H K := hmin.1
  have hHmax : ∀ v, H.degree v ≤ 2 := fun v => (half_degree_bounds G H K hdeg hsplit v).2
  subst hSeq
  obtain ⟨hz12, hz13, hz23, hHz12, hHz23, hHz13⟩ := triangle_of_oddSupport H hS
  have hsum := hsplit.2.2.2.2.2.2
  have hGz₁ : G.degree z₁ = 4 := hz4 z₁ (by simp)
  have hGz₂ : G.degree z₂ = 4 := hz4 z₂ (by simp)
  have hGz₃ : G.degree z₃ = 4 := hz4 z₃ (by simp)
  have hHz₁ : H.degree z₁ = 2 := by have := hsum z₁; rw [hGz₁, hK2 z₁] at this; omega
  have hHz₂ : H.degree z₂ = 2 := by have := hsum z₂; rw [hGz₂, hK2 z₂] at this; omega
  have hHz₃ : H.degree z₃ = 2 := by have := hsum z₃; rw [hGz₃, hK2 z₃] at this; omega
  have hpz₃' : p ≠ z₃ := fun h => by rw [h, hHz₃] at hpH; omega
  have hqz₁' : q ≠ z₁ := fun h => by rw [h, hHz₁] at hqH; omega
  have hqz₂' : q ≠ z₂ := fun h => by rw [h, hHz₂] at hqH; omega
  have hqz₃' : q ≠ z₃ := fun h => by rw [h, hHz₃] at hqH; omega
  obtain ⟨w0, hw0path, hw0even⟩ := hPeven
  have tri_contra : z₁ ∈ w0.support → z₂ ∈ w0.support → z₃ ∈ w0.support → False := by
    intro h1 h2 h3
    have hcyc : (SimpleGraph.Walk.cons hHz13 (SimpleGraph.Walk.cons hHz23.symm
        (SimpleGraph.Walk.cons hHz12.symm SimpleGraph.Walk.nil))).IsCycle := by
      have n1 : s(z₁, z₃) ≠ s(z₃, z₂) := by
        rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hz13 h.1, fun h => hz12 h.1⟩
      have n2 : s(z₁, z₃) ≠ s(z₂, z₁) := by
        rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hz12 h.1, fun h => hz23 h.2.symm⟩
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.Walk.cons_isPath_iff]
          exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [Ne.symm hz12]⟩
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false]
          push_neg; exact ⟨Ne.symm hz23, Ne.symm hz13⟩
      · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false]
        push_neg; exact ⟨n1, n2⟩
    refine no_cycle_of_path_support H hHmax hw0path hpH hqH hcyc ?_
    intro u hu
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h2
    · exact h1
  have hcl := path_support_closed H hHmax hw0path hpq hpH hqH
  have hz_notin : z₁ ∉ w0.support ∧ z₂ ∉ w0.support ∧ z₃ ∉ w0.support := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact tri_contra h (hcl z₁ h z₂ hHz12) (hcl z₁ h z₃ hHz13)
    · exact tri_contra (hcl z₂ h z₁ hHz12.symm) h (hcl z₂ h z₃ hHz23)
    · exact tri_contra (hcl z₃ h z₁ hHz13.symm) (hcl z₃ h z₂ hHz23.symm) h
  have harc := k_arc_separation K hK2 hpz₁ hpz₂ hqz₃ hz12 hpq hz13 hz23 hpz₃' hqz₁' hqz₂'
  have main_move : ∀ a cm : V, H.Adj a cm → H.Adj cm z₃ → H.Adj a z₃ →
      H.degree a = 2 → H.degree cm = 2 → a ≠ cm → a ≠ z₃ → cm ≠ z₃ →
      G.degree a = 4 → a ∉ w0.support → cm ∉ w0.support → K.Adj a p →
      ¬ (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃ →
      ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
    intro a cm hac hcz haz hda hdcm hacne hazne hcmz hGa hane hcmne hKap hR
    have hpa : p ≠ a := fun h => hane (h ▸ w0.start_mem_support)
    have hpcm : p ≠ cm := fun h => hcmne (h ▸ w0.start_mem_support)
    have hqa : q ≠ a := fun h => hane (h ▸ w0.end_mem_support)
    have hap_ne : a ≠ p := fun h => hpa h.symm
    have hzq_ne : z₃ ≠ q := fun h => hqz₃' h.symm
    have hnHap : ¬ H.Adj a p := fun hH => (hsplit.2.1 a p hH) hKap
    have hnHzq : ¬ H.Adj z₃ q := fun hH => (hsplit.2.1 z₃ q hH) hqz₃.symm
    have hnKaz : ¬ K.Adj a z₃ := hsplit.2.1 a z₃ haz
    have e1 : s(a, p) ≠ s(a, z₃) := by
      rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hpz₃' h.2, fun h => hazne h.1⟩
    have e2 : s(a, p) ≠ s(z₃, q) := by
      rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hazne h.1, fun h => hqa h.1.symm⟩
    have e3 : s(a, z₃) ≠ s(z₃, q) := by
      rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hazne h.1, fun h => hqa h.1.symm⟩
    refine ⟨{s(a, p), s(a, z₃), s(z₃, q)},
      three_edge_toggle_valid G H K hdeg hsplit haz hKap hqz₃.symm hGa hGz₃ hpH hqH hpq, ?_⟩
    have htccyc : (SimpleGraph.Walk.cons haz (SimpleGraph.Walk.cons hcz.symm
        (SimpleGraph.Walk.cons hac.symm SimpleGraph.Walk.nil))).IsCycle := by
      have n1 : s(a, z₃) ≠ s(z₃, cm) := by
        rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hazne h.1, fun h => hacne h.1⟩
      have n2 : s(a, z₃) ≠ s(cm, a) := by
        rw [Ne, Sym2.eq_iff, not_or]; exact ⟨fun h => hacne h.1, fun h => hcmz h.2.symm⟩
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.Walk.cons_isPath_iff]
          exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [Ne.symm hacne]⟩
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false]
          push_neg; exact ⟨Ne.symm hcmz, Ne.symm hazne⟩
      · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false]
        push_neg; exact ⟨n1, n2⟩
    have htcodd : Odd (SimpleGraph.Walk.cons haz (SimpleGraph.Walk.cons hcz.symm
        (SimpleGraph.Walk.cons hac.symm SimpleGraph.Walk.nil))).length := by
      simp [SimpleGraph.Walk.length_cons]; decide
    have htcedge : s(a, z₃) ∈ (SimpleGraph.Walk.cons haz (SimpleGraph.Walk.cons hcz.symm
        (SimpleGraph.Walk.cons hac.symm SimpleGraph.Walk.nil))).edges := by
      simp [SimpleGraph.Walk.edges_cons]
    have hHlt := canonical_H_count_lt H {s(a, p), s(a, z₃), s(z₃, q)}
      (toggled_H_repr H haz hnHap hnHzq hap_ne hzq_ne e1 e2 e3) hHmax haz htccyc htcodd htcedge
      (fun w _ => absurd (⟨w⟩ : (H.deleteEdges {s(a, z₃)}).Reachable a p)
        (hsep1_H H hac haz hcz hda hdcm hHz₃ hacne hazne hcmz hpa hpcm hpz₃'))
      (hsep2_H H hHmax hac haz hcz hda hHz₃ hacne hazne hcmz hw0path hw0even hpq hpH hqH hnHap
        hane hcmne hz_notin.2.2
        (hsep1_H H hac haz hcz hda hdcm hHz₃ hacne hazne hcmz hpa hpcm hpz₃'))
      hap_ne hzq_ne
    have hKle := canonical_K_count_le K {s(a, p), s(a, z₃), s(z₃, q)}
      (toggled_K_repr K hKap hqz₃.symm hnKaz hazne e1 e2 e3)
      (fun w _ => absurd (⟨w⟩ : (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃) hR) hazne
    exact add_lt_add_of_lt_of_le hHlt hKle
  rcases harc with hR1 | hR2
  · exact main_move z₁ z₂ hHz12 hHz23 hHz13 hHz₁ hHz₂ hz12 hz13 hz23 hGz₁
      hz_notin.1 hz_notin.2.1 hpz₁.symm hR1
  · exact main_move z₂ z₁ hHz12.symm hHz13 hHz23 hHz₂ hHz₁ (Ne.symm hz12) hz23 hz13 hGz₂
      hz_notin.2.1 hz_notin.1 hpz₂.symm hR2

/-- Supply, the `K`-side (STRIKE-A §6.3, `n` odd case).  A `2`-regular spanning
half on an odd number of vertices carries an odd cycle: were it odd-cycle-free
it would be `2`-colorable, forcing an even vertex count
(`even_card_of_two_regular_no_odd_cycle`). -/
lemma supply_oddCount_K_of_odd_card
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK2 : ∀ v, K.degree v = 2) (hn : Odd (Fintype.card V)) :
    1 ≤ oddCycleCount K := by
  by_contra h
  push_neg at h
  have h0 : oddCycleCount K = 0 := by omega
  have hno := noOddCycle_of_oddCycleCount_eq_zero K h0
  have heven := even_card_of_two_regular_no_odd_cycle K hK2 hno
  exact (Nat.not_even_iff_odd.mpr hn) heven

/-
Supply, the `H`-side (STRIKE-A §6.3, `n` even case).  `H` is the light half:
two degree-`1` ends `p, q` and every other vertex of degree `2`, so it is one
`p`–`q` path (odd length `ℓ_P`) together with disjoint cycles.  The number of
odd `H`-cycles has the parity of `n − (ℓ_P + 1) ≡ n (mod 2)` (handshake over the
components, `ℓ_P` odd); for `n` even this is even, and since `H` already carries
an odd cycle `Z` (`hHodd`; in STRIKE-A the poisoned triangle of config (i)) the
count is `≥ 1`, hence `≥ 2`.

NOTE.  The bare `(Even n → 2 ≤ oc(H))` conclusion of the original LADDER-PIN 10
is FALSE without `hHodd`: take `H` a Hamiltonian `p`–`q` path (odd length) and
`K` a single even spanning cycle — a zero-odd (hence minimal) split of a
connected degree-`{3,4}` graph with `n` even and `oc(H) = 0`.  STRIKE-A §6.3
silently uses the odd cycle `Z ∈ H` supplied by config (i); `hHodd` restores it.

Bridge (STRIKE-A §6.3 handshake, structural half).  For the light half `H`
(degrees `1` at `p, q`, `2` elsewhere, one `p`–`q` path of odd length `ℓ_P` and
all other components cycles), the odd-cycle supports are exactly the
odd-cardinality connected components: an odd `H`-cycle occupies a whole
degree-`2` component, and every odd-cardinality component is such a cycle (the
only non-cycle component is the `p`–`q` path, whose `ℓ_P + 1` vertices are even
in number).

Direction 1 of the bridge.  In a graph of maximum degree `≤ 2`, the support
of an odd cycle fills a whole odd-cardinality connected component: each cycle
vertex already spends both its (≤ 2) edges on the cycle, so nothing else attaches
and the component equals the cycle's vertex set.
-/
lemma oddCycleSupport_fills_oddComponent
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg2 : ∀ v, H.degree v ≤ 2)
    {S : Finset V} (hS : S ∈ oddCycleSupports H) :
    ∃ c : H.ConnectedComponent, Odd c.supp.ncard ∧ (↑S : Set V) = c.supp := by
  obtain ⟨x, w, hw_cycle, hw_odd, hw_support⟩ : ∃ x : V, ∃ w : H.Walk x x, w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = S := by
    unfold oddCycleSupports at hS; aesop;
  refine' ⟨ H.connectedComponentMk x, _, _ ⟩;
  · have h_card : (H.connectedComponentMk x).supp.ncard = w.support.toFinset.card := by
      rw [ ← Set.ncard_coe_finset ];
      congr with y ; simp +decide [ SimpleGraph.connectedComponentMk ];
      constructor <;> intro hy;
      · have h_support : ∀ u ∈ w.support, ∀ v, H.Reachable u v → v ∈ w.support := by
          exact fun u a v a_1 ↦ cycle_support_closed_reachable H hdeg2 hw_cycle a a_1;
        exact h_support x ( by simp +decide ) y ( by exact ConnectedComponent.exact (id (Eq.symm hy)) );
      · exact Quot.sound ( by
          exact ⟨ w.takeUntil y hy |> SimpleGraph.Walk.reverse ⟩ );
    have := hw_cycle.support_nodup;
    cases w <;> simp_all +decide [ List.nodup_iff_injective_get ];
    have := List.toFinset_card_of_nodup ( show List.Nodup ( ‹H.Walk _ _›.support ) from List.nodup_iff_injective_get.mpr this ) ; aesop;
  · ext y;
    constructor;
    · intro hy;
      simp +zetaDelta at *;
      exact ⟨ w.takeUntil y ( by aesop ) |> SimpleGraph.Walk.reverse ⟩;
    · intro hy
      have h_reachable : SimpleGraph.Reachable H x y := by
        exact Reachable.symm (ConnectedComponent.exact hy);
      grind +suggestions

/-- Closure step for `path_support_eq_component`.  Every `H`-neighbour of a
support vertex of the path `w` is again on `w`: the path already realises all of
that vertex's `H`-degree (`1` at the ends `p, q`, `2` in the interior), so its
`w`-subgraph neighbour set exhausts its `H`-neighbour set. -/
lemma path_closure (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    {w : H.Walk p q} (hw : w.IsPath) :
    ∀ u ∈ w.support, ∀ v, H.Adj u v → v ∈ w.support := by
  have h_neighbor_set_eq : ∀ u ∈ w.support, (w.toSubgraph.neighborSet u).ncard = H.degree u := by
    intro u hu
    by_cases hu_p : u = p
    by_cases hu_q : u = q;
    · cases w <;> simp_all +decide [ SimpleGraph.Walk.IsPath ];
      · contrapose! hqH;
        have := SimpleGraph.sum_degrees_eq_twice_card_edges H; simp_all +decide [ Finset.sum_add_distrib ] ;
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ p ) ] at this;
        rw [ Finset.sum_congr rfl fun x hx => hHfull x <| by aesop ] at this ; simp_all +decide [ Finset.card_sdiff ];
        omega;
      · aesop;
    · have h_neighbor_set_eq : w.toSubgraph.neighborSet p = {w.snd} := by
        apply SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_startpoint hw;
        cases w <;> aesop;
      aesop;
    · by_cases hu_q : u = q <;> simp_all +decide [ SimpleGraph.Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two ];
      · rw [ hu_q, SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_endpoint hw ];
        · rw [ Set.ncard_singleton, hqH ];
        · cases w <;> aesop;
      · obtain ⟨i, hi⟩ : ∃ i : ℕ, 0 < i ∧ i < w.length ∧ u = w.getVert i := by
          grind +suggestions;
        grind +suggestions;
  intro u hu v hv
  have h_subset : w.toSubgraph.neighborSet u ⊆ H.neighborSet u := by
    exact Subgraph.neighborSet_subset w.toSubgraph u
  have h_eq : (w.toSubgraph.neighborSet u).ncard = (H.neighborSet u).ncard := by
    convert h_neighbor_set_eq u hu using 1;
    rw [ Set.ncard_eq_toFinset_card' ] ; simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
  have h_eq_set : w.toSubgraph.neighborSet u = H.neighborSet u := by
    exact Set.eq_of_subset_of_ncard_le h_subset h_eq.ge;
  replace h_eq_set := Set.ext_iff.mp h_eq_set v; simp_all +decide [ SimpleGraph.Walk.mem_verts_toSubgraph ] ;
  exact Walk.mem_support_of_adj_toSubgraph (id (Subgraph.adj_symm w.toSubgraph h_eq_set))

/-- The `p`–`q` path fills its whole connected component.  A walk from the
degree-`1` vertex `p` is forced along `w`: at every support vertex `u` of `w`,
`u`'s `w`-neighbours (one at an end, two in the interior) already account for all
of `u`'s `H`-degree (`1` at `p, q`, `2` elsewhere), so every `H`-neighbour of `u`
lies on `w`; hence nothing reachable from `p` escapes `w.support`. -/
lemma path_support_eq_component (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    {w : H.Walk p q} (hw : w.IsPath) :
    (↑(w.support.toFinset) : Set V) = (H.connectedComponentMk p).supp := by
  refine' Set.Subset.antisymm _ _;
  · intro v hv;
    simp_all +decide [ SimpleGraph.ConnectedComponent.mem_supp_iff ];
    exact ⟨ w.takeUntil v hv |> SimpleGraph.Walk.reverse ⟩;
  · intro v hv;
    obtain ⟨pw, hpw⟩ : ∃ pw : H.Walk p v, True := by
      simp_all +decide [ SimpleGraph.ConnectedComponent.mem_supp_iff ];
      exact hv.symm;
    have h_ind : ∀ a b : V, H.Reachable a b → a ∈ w.support → b ∈ w.support := by
      intro a b hab ha
      induction' hab with a b hab ih;
      induction' a with a b hab ih;
      · exact ha;
      · have := path_closure H hpH hqH hHfull hw b ha hab ‹_›; aesop;
    simpa using h_ind p v ( by exact ⟨ pw ⟩ ) ( by simp )

/-
A connected component all of whose vertices have degree `2` (a `2`-regular
component) is a single cycle; if its cardinality is odd, its support is the
support of an odd cycle.
-/
lemma allDeg2_component_oddCycleSupport (H : SimpleGraph V) [DecidableRel H.Adj]
    {c : H.ConnectedComponent} (hdeg2c : ∀ v ∈ c.supp, H.degree v = 2)
    (hc : Odd c.supp.ncard) :
    ∃ S : Finset V, S ∈ oddCycleSupports H ∧ (↑S : Set V) = c.supp := by
  have h_cycle : ∃ p : H.Walk (Classical.choose c.nonempty_supp) (Classical.choose c.nonempty_supp), p.IsCycle ∧ (p.support.toFinset : Set V) = c.supp := by
    obtain ⟨p, hp_cycle⟩ : ∃ p : (H.induce c.supp).Walk (⟨Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp⟩) (⟨Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp⟩), p.IsCycle ∧ p.support.toFinset = Finset.univ := by
      have h_cycle : (H.induce c.supp).IsCycles := by
        intro v hv_nonempty
        have hv_card : (H.induce c.supp).degree v = 2 := by
          convert hdeg2c v v.2 using 1;
          convert induce_supp_degree H c v using 1;
        simp_all +decide [ Set.ncard_eq_toFinset_card' ];
        convert hv_card using 1;
        refine' Finset.card_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ <;> aesop;
      have h_connected : (H.induce c.supp).Connected := by
        rw [ SimpleGraph.connected_iff_exists_forall_reachable ];
        obtain ⟨ v, hv ⟩ := c.nonempty_supp;
        use ⟨v, hv⟩;
        rintro ⟨ w, hw ⟩;
        have h_path : H.Reachable v w := by
          exact ConnectedComponent.reachable_of_mem_supp c hv hw;
        obtain ⟨ p ⟩ := h_path;
        induction' p with u v p ih;
        · exact SimpleGraph.Reachable.refl _;
        · rename_i h₁ h₂ h₃;
          have h_path : p ∈ c.supp := by
            exact (ConnectedComponent.mem_supp_congr_adj c h₁).mp hv;
          exact SimpleGraph.Reachable.trans ( SimpleGraph.Adj.reachable ( by aesop ) ) ( h₃ h_path hw );
      have := @SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp;
      specialize this h_cycle ( show ( ⟨ Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp ⟩ : c.supp ) ∈ ( ( induce c.supp H ).connectedComponentMk ⟨ Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp ⟩ ).supp from ?_ );
      · grind +suggestions;
      · obtain ⟨ p, hp ⟩ := this ( by
          have := hdeg2c ( Classical.choose c.nonempty_supp ) ( Classical.choose_spec c.nonempty_supp );
          rw [ SimpleGraph.degree ] at this;
          rw [ Finset.card_eq_two ] at this;
          obtain ⟨ x, y, hxy, h ⟩ := this; simp_all +decide [ Finset.ext_iff, SimpleGraph.neighborSet ] ;
          have := h x; have := h y; simp_all +decide [ SimpleGraph.adj_comm ] ;
          exact ⟨ ⟨ x, by have := h x; have := h y; exact (by
          have := Classical.choose_spec c.nonempty_supp; simp_all +decide [ SimpleGraph.connectedComponentMk ] ;
          exact this ▸ Quot.sound ( SimpleGraph.Adj.reachable ( h x |>.2 ( Or.inl rfl ) ) )) ⟩, by simp +decide ⟩ );
        refine' ⟨ p, hp.1, _ ⟩;
        simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        exact fun v hv => h_connected ⟨ v, by aesop ⟩ ⟨ Classical.choose c.nonempty_supp, Classical.choose_spec c.nonempty_supp ⟩;
    refine' ⟨ p.map ( SimpleGraph.Embedding.toHom ( SimpleGraph.Embedding.induce c.supp ) ), _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    convert hp_cycle.1.map _;
    exact Subtype.coe_injective;
  obtain ⟨ p, hp_cycle, hp_support ⟩ := h_cycle; use p.support.toFinset; simp_all +decide [ oddCycleSupports ] ;
  refine' ⟨ _, p, hp_cycle, _, rfl ⟩;
  have h_card_odd : p.support.length - 1 = c.supp.ncard := by
    have h_card_odd : p.support.length - 1 = (p.support.toFinset : Finset V).card := by
      have := hp_cycle.support_nodup; simp_all +decide [ List.nodup_iff_injective_get ] ;
      have h_card_odd : (p.support.tail.toFinset : Finset V).card = p.support.tail.length := by
        rw [ List.toFinset_card_of_nodup ] ; exact List.nodup_iff_injective_get.mpr this;
      cases p <;> simp_all +decide [ List.toFinset_cons ];
    rw [ h_card_odd, ← Set.ncard_coe_finset ] ; congr ; aesop;
  cases p <;> simp_all +decide [ parity_simps ]

/-- Direction 2 of the bridge.  For the light half `H` (degrees `1` at `p, q`,
`2` elsewhere, an odd `p`–`q` path), every odd-cardinality connected component is
the support of an odd cycle.  Such a component avoids `p, q` (their component is
the `p`–`q` path, of even cardinality `ℓ_P + 1`), so all its vertices have degree
`2`, and a finite connected all-degree-`2` component is a single cycle. -/
lemma oddComponent_has_oddCycleSupport
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    {c : H.ConnectedComponent} (hc : Odd c.supp.ncard) :
    ∃ S : Finset V, S ∈ oddCycleSupports H ∧ (↑S : Set V) = c.supp := by
  classical
  obtain ⟨w0, hw0path, hw0odd⟩ := hPodd
  have hspan := path_support_eq_component H hpH hqH hHfull hw0path
  have hpeven : Even (H.connectedComponentMk p).supp.ncard := by
    have hcard : (H.connectedComponentMk p).supp.ncard = w0.support.toFinset.card := by
      rw [← hspan, Set.ncard_coe_finset]
    rw [hcard, List.toFinset_card_of_nodup hw0path.support_nodup, SimpleGraph.Walk.length_support]
    rcases hw0odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have hpqsame : H.connectedComponentMk q = H.connectedComponentMk p :=
    (SimpleGraph.ConnectedComponent.sound ⟨w0⟩).symm
  have hcp : p ∉ c.supp := by
    intro hp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hp
    rw [← hp] at hc
    exact (Nat.not_even_iff_odd.mpr hc) hpeven
  have hcq : q ∉ c.supp := by
    intro hq
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hq
    rw [← hq, hpqsame] at hc
    exact (Nat.not_even_iff_odd.mpr hc) hpeven
  have hdeg2c : ∀ v ∈ c.supp, H.degree v = 2 := fun v hv =>
    hHfull v (by rintro rfl; exact hcp hv) (by rintro rfl; exact hcq hv)
  exact allDeg2_component_oddCycleSupport H hdeg2c hc

lemma oddCycleCount_eq_oddComponents_ncard
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    oddCycleCount H = H.oddComponents.ncard := by
  classical
  have hdeg2 : ∀ v, H.degree v ≤ 2 := by
    intro v
    by_cases hvp : v = p
    · subst hvp; omega
    · by_cases hvq : v = q
      · subst hvq; omega
      · rw [hHfull v hvp hvq]
  have hncard : H.oddComponents.ncard
      = (Finset.univ.filter (fun c : H.ConnectedComponent => Odd c.supp.ncard)).card := by
    rw [SimpleGraph.oddComponents, Set.ncard_eq_toFinset_card']
    congr 1; ext c; simp
  rw [oddCycleCount, hncard]
  apply Finset.card_bij (fun S hS => (oddCycleSupport_fills_oddComponent H hdeg2 hS).choose)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (oddCycleSupport_fills_oddComponent H hdeg2 hS).choose_spec.1
  · intro S₁ h₁ S₂ h₂ heq
    have e1 := (oddCycleSupport_fills_oddComponent H hdeg2 h₁).choose_spec.2
    have e2 := (oddCycleSupport_fills_oddComponent H hdeg2 h₂).choose_spec.2
    rw [heq] at e1
    have : (↑S₁ : Set V) = ↑S₂ := by rw [e1, ← e2]
    exact_mod_cast this
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨S, hS, hSc⟩ := oddComponent_has_oddCycleSupport H hpq hpH hqH hHfull hPodd hc
    refine ⟨S, hS, ?_⟩
    have e1 := (oddCycleSupport_fills_oddComponent H hdeg2 hS).choose_spec.2
    apply SimpleGraph.ConnectedComponent.supp_injective
    rw [← e1, hSc]

/-- Bridge for a `2`-regular half.  Every connected component of a `2`-regular
graph is a single cycle, so its odd-cycle supports are exactly its
odd-cardinality components: `oddCycleCount K = |oddComponents K|`. -/
lemma twoReg_oddCycleCount_eq_oddComponents
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK2 : ∀ v, K.degree v = 2) :
    oddCycleCount K = K.oddComponents.ncard := by
  classical
  have hdeg2 : ∀ v, K.degree v ≤ 2 := fun v => (hK2 v).le
  have hncard : K.oddComponents.ncard
      = (Finset.univ.filter (fun c : K.ConnectedComponent => Odd c.supp.ncard)).card := by
    rw [SimpleGraph.oddComponents, Set.ncard_eq_toFinset_card']
    congr 1; ext c; simp
  rw [oddCycleCount, hncard]
  apply Finset.card_bij (fun S hS => (oddCycleSupport_fills_oddComponent K hdeg2 hS).choose)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (oddCycleSupport_fills_oddComponent K hdeg2 hS).choose_spec.1
  · intro S₁ h₁ S₂ h₂ heq
    have e1 := (oddCycleSupport_fills_oddComponent K hdeg2 h₁).choose_spec.2
    have e2 := (oddCycleSupport_fills_oddComponent K hdeg2 h₂).choose_spec.2
    rw [heq] at e1
    have : (↑S₁ : Set V) = ↑S₂ := by rw [e1, ← e2]
    exact_mod_cast this
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hdeg2c : ∀ v ∈ c.supp, K.degree v = 2 := fun v _ => hK2 v
    obtain ⟨S, hS, hSc⟩ := allDeg2_component_oddCycleSupport K hdeg2c hc
    refine ⟨S, hS, ?_⟩
    have e1 := (oddCycleSupport_fills_oddComponent K hdeg2 hS).choose_spec.2
    apply SimpleGraph.ConnectedComponent.supp_injective
    rw [← e1, hSc]

/-
General bridge for a max-degree-`≤ 2` half `M`.  Its odd-cycle supports are
exactly the connected components that are cycles (all vertices of degree `2`)
of odd cardinality; path components (which carry degree-`1` vertices) never
count.  This unifies `twoReg_oddCycleCount_eq_oddComponents` (no path
components) and `oddCycleCount_eq_oddComponents_ncard` (one even path).
-/
lemma maxDeg2_oddCycleCount_eq_cycleComponents
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg2 : ∀ v, M.degree v ≤ 2) :
    oddCycleCount M =
      (Finset.univ.filter (fun c : M.ConnectedComponent =>
        (∀ v ∈ c.supp, M.degree v = 2) ∧ Odd c.supp.ncard)).card := by
  classical
  rw [oddCycleCount]
  apply Finset.card_bij (fun S hS => (oddCycleSupport_fills_oddComponent M hdeg2 hS).choose)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hspec := (oddCycleSupport_fills_oddComponent M hdeg2 hS).choose_spec
    refine ⟨?_, hspec.1⟩
    -- every vertex of the cycle-support component has degree exactly `2`
    intro v hv
    have hvS : v ∈ (↑S : Set V) := by rw [hspec.2]; exact hv
    -- unpack the odd cycle `w` whose support is `S`
    obtain ⟨x, w, hw_cycle, hw_odd, hw_support⟩ :
        ∃ x : V, ∃ w : M.Walk x x, w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = S := by
      unfold oddCycleSupports at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact hS
    have hvw : v ∈ w.support := by
      have : v ∈ S := by exact_mod_cast hvS
      rw [← hw_support] at this
      exact List.mem_toFinset.mp this
    -- a vertex on a cycle has at least two neighbours, and ≤ 2 by hypothesis
    have h2 : 2 ≤ M.degree v := cycle_support_deg_ge_two M w hw_cycle v hvw
    have := hdeg2 v
    omega
  · intro S₁ h₁ S₂ h₂ heq
    have e1 := (oddCycleSupport_fills_oddComponent M hdeg2 h₁).choose_spec.2
    have e2 := (oddCycleSupport_fills_oddComponent M hdeg2 h₂).choose_spec.2
    rw [heq] at e1
    have : (↑S₁ : Set V) = ↑S₂ := by rw [e1, ← e2]
    exact_mod_cast this
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨S, hS, hSc⟩ := allDeg2_component_oddCycleSupport M hc.1 hc.2
    refine ⟨S, hS, ?_⟩
    have e1 := (oddCycleSupport_fills_oddComponent M hdeg2 hS).choose_spec.2
    apply SimpleGraph.ConnectedComponent.supp_injective
    rw [← e1, hSc]

/-- Adding a single edge `s(u, w)` to a max-degree-`≤ 2` graph in which `u` and
`w` already have degree `≤ 1` increases the odd-cycle count by at most one: the
result is again max-degree-`≤ 2`, so every new odd cycle fills the connected
component of the new edge — there is at most one such component, hence at most
one new odd-cycle support. -/
lemma oddCycleCount_addEdge_le_succ
    (M M' : SimpleGraph V) [DecidableRel M.Adj] [DecidableRel M'.Adj]
    (hMdeg2 : ∀ v, M.degree v ≤ 2)
    {u w : V} (hu : M.degree u ≤ 1) (hw : M.degree w ≤ 1) (huw : u ≠ w)
    (hM' : ∀ x y, M'.Adj x y ↔ (M.Adj x y ∨ (s(x, y) = s(u, w) ∧ x ≠ y))) :
    oddCycleCount M' ≤ oddCycleCount M + 1 := by
  classical
  have hMle : ∀ x y, M.Adj x y → M'.Adj x y := fun x y h => (hM' x y).2 (Or.inl h)
  have hM'deg2 : ∀ v, M'.degree v ≤ 2 := by
    intro v
    by_cases hvu : v = u
    · subst hvu
      have hsub : M'.neighborFinset v ⊆ insert w (M.neighborFinset v) := by
        intro z hz
        simp only [mem_neighborFinset] at hz
        rw [hM'] at hz
        rcases hz with h | ⟨he, hne⟩
        · exact Finset.mem_insert_of_mem (by simpa [mem_neighborFinset])
        · have hz : z = w := Sym2.congr_right.mp he
          subst hz; exact Finset.mem_insert_self _ _
      have hcard : M'.degree v = (M'.neighborFinset v).card := (M'.card_neighborFinset_eq_degree v).symm
      rw [hcard]
      calc (M'.neighborFinset v).card ≤ (insert w (M.neighborFinset v)).card := Finset.card_le_card hsub
        _ ≤ (M.neighborFinset v).card + 1 := Finset.card_insert_le _ _
        _ ≤ 2 := by rw [M.card_neighborFinset_eq_degree]; omega
    · by_cases hvw : v = w
      · subst hvw
        have hsub : M'.neighborFinset v ⊆ insert u (M.neighborFinset v) := by
          intro z hz
          simp only [mem_neighborFinset] at hz
          rw [hM'] at hz
          rcases hz with h | ⟨he, hne⟩
          · exact Finset.mem_insert_of_mem (by simpa [mem_neighborFinset])
          · have hz : z = u := Sym2.congr_right.mp (he.trans (Sym2.eq_swap))
            subst hz; exact Finset.mem_insert_self _ _
        have hcard : M'.degree v = (M'.neighborFinset v).card := (M'.card_neighborFinset_eq_degree v).symm
        rw [hcard]
        calc (M'.neighborFinset v).card ≤ (insert u (M.neighborFinset v)).card := Finset.card_le_card hsub
          _ ≤ (M.neighborFinset v).card + 1 := Finset.card_insert_le _ _
          _ ≤ 2 := by rw [M.card_neighborFinset_eq_degree]; omega
      · have hset : M'.neighborFinset v = M.neighborFinset v := by
          ext z; simp only [mem_neighborFinset, hM']
          constructor
          · rintro (h | ⟨he, hne⟩)
            · exact h
            · exfalso
              rcases Sym2.eq_iff.mp he with ⟨h1,_⟩ | ⟨h1,_⟩
              · exact hvu h1
              · exact hvw h1
          · intro h; exact Or.inl h
        rw [SimpleGraph.degree, hset, ← SimpleGraph.degree]; exact hMdeg2 v
  have hsub : oddCycleSupports M ⊆ oddCycleSupports M' := by
    intro S hS
    simp only [oddCycleSupports, mem_filter, mem_univ, true_and] at hS ⊢
    obtain ⟨x, c, hc, hodd, hsupp⟩ := hS
    have hedges : ∀ e ∈ c.edges, e ∈ M'.edgeSet := by
      intro e he
      rcases e with ⟨a,b⟩
      have hab : M.Adj a b := by simpa using c.edges_subset_edgeSet he
      simpa using hMle a b hab
    exact ⟨x, c.transfer M' hedges, hc.transfer hedges, by rwa [SimpleGraph.Walk.length_transfer],
      by rw [SimpleGraph.Walk.support_transfer]; exact hsupp⟩
  have hnew : ∀ S ∈ oddCycleSupports M', S ∉ oddCycleSupports M →
      (↑S : Set V) = (M'.connectedComponentMk u).supp := by
    intro S hS hSnot
    obtain ⟨x, c, hc, hodd, hsupp⟩ : ∃ (x:V) (c : M'.Walk x x), c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S := by
      simpa only [oddCycleSupports, mem_filter, mem_univ, true_and] using hS
    have hedge : s(u,w) ∈ c.edges := by
      by_contra hne
      apply hSnot
      have hedges : ∀ e ∈ c.edges, e ∈ M.edgeSet := by
        intro e he
        rcases e with ⟨a,b⟩
        have hadj : M'.Adj a b := by simpa using c.edges_subset_edgeSet he
        rw [hM'] at hadj
        rcases hadj with h | ⟨heq, hnee⟩
        · simpa using h
        · exact absurd (by rw [← heq]; exact he) hne
      simp only [oddCycleSupports, mem_filter, mem_univ, true_and]
      exact ⟨x, c.transfer M hedges, hc.transfer hedges, by rwa [SimpleGraph.Walk.length_transfer],
        by rw [SimpleGraph.Walk.support_transfer]; exact hsupp⟩
    have huin : u ∈ S := by
      rw [← hsupp]; exact List.mem_toFinset.mpr (c.fst_mem_support_of_mem_edges hedge)
    obtain ⟨comp, hcodd, hcsupp⟩ := oddCycleSupport_fills_oddComponent M' hM'deg2 hS
    have hcompeq : comp = M'.connectedComponentMk u := by
      have hu' : u ∈ comp.supp := by rw [← hcsupp]; exact_mod_cast huin
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu'; exact hu'.symm
    rw [hcsupp, hcompeq]
  have hcard1 : (oddCycleSupports M' \ oddCycleSupports M).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_sdiff] at ha hb
    have h1 := hnew a ha.1 ha.2
    have h2 := hnew b hb.1 hb.2
    have hab : (↑a : Set V) = ↑b := by rw [h1, h2]
    exact_mod_cast hab
  have hunion : oddCycleSupports M' ⊆ oddCycleSupports M ∪ (oddCycleSupports M' \ oddCycleSupports M) := by
    intro x hx
    by_cases h : x ∈ oddCycleSupports M
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (mem_sdiff.mpr ⟨hx, h⟩)
  calc oddCycleCount M' = (oddCycleSupports M').card := rfl
    _ ≤ (oddCycleSupports M).card + (oddCycleSupports M' \ oddCycleSupports M).card := by
        rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff]
        exact Finset.card_le_card hunion
    _ ≤ oddCycleCount M + 1 := by rw [oddCycleCount]; omega

lemma supply_oddCount_H_of_even_card
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    (hHodd : (oddCycleSupports H).Nonempty)
    (hn : Even (Fintype.card V)) :
    2 ≤ oddCycleCount H := by
  have hbridge := oddCycleCount_eq_oddComponents_ncard H hpq hpH hqH hHfull hPodd
  have hpar := H.odd_ncard_oddComponents
  have hcardeven : ¬ Odd (Nat.card V) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff_even.mpr hn
  have heven : Even H.oddComponents.ncard :=
    Nat.not_odd_iff_even.mp (fun h => hcardeven (hpar.mp h))
  have hge1 : 1 ≤ oddCycleCount H := Finset.Nonempty.card_pos hHodd
  rw [hbridge] at hge1 ⊢
  rcases heven with ⟨k, hk⟩
  omega

/-- LADDER-PIN 10 (Lemma 6.4, the parity supply).  In the blocked world
(`ℓ_P` odd), the blocking parity manufactures a second odd component: an odd
`K`-cycle when `|V|` is odd, a second odd `H`-cycle when `|V|` is even.

CORRECTED STATEMENT.  The original conclusion's second conjunct
(`Even n → 2 ≤ oc(H)`) is FALSE as literally stated — see the NOTE on
`supply_oddCount_H_of_even_card` for the Hamiltonian-path counterexample.
STRIKE-A §6.3's proof uses the odd `H`-cycle `Z` supplied by config (i) (§6.1);
the corrected statement restores that as the hypothesis
`hHodd : (oddCycleSupports H).Nonempty`.  The original (unprovable) statement is
retained, commented out, immediately below. -/
lemma supply_of_blocked
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    (hHodd : (oddCycleSupports H).Nonempty) :
    (Odd (Fintype.card V) → 1 ≤ oddCycleCount K) ∧
    (Even (Fintype.card V) → 2 ≤ oddCycleCount H) :=
  ⟨fun hn => supply_oddCount_K_of_odd_card K hK2 hn,
   fun hn => supply_oddCount_H_of_even_card H hpq hpH hqH hHfull hPodd hHodd hn⟩

/- ORIGINAL LADDER-PIN 10 STATEMENT — FALSE as literally stated (see the NOTE on
`supply_oddCount_H_of_even_card`); retained verbatim, commented out, rather than
deleted.

lemma supply_of_blocked_ORIGINAL
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    (Odd (Fintype.card V) → 1 ≤ oddCycleCount K) ∧
    (Even (Fintype.card V) → 2 ≤ oddCycleCount H) := by
  sorry
-/

/-! ## The routing core (STRIKE-A §6.10, pass 3; round 15)

Walk vocabulary: an alternating walk is a `G.Walk` that is a trail (distinct
edges, mathlib `IsTrail`), whose step `i` lies in `K` for even `i` and in `H`
for odd `i` (so it starts at `p` with a `K`-edge); it is maximal when no unused
edge of the demanded half remains at its final vertex. -/

/-- Step-half alternation: even steps in `K`, odd steps in `H`. -/
def AlternatesKH (H K : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    {G : SimpleGraph V} {p x : V} (w : G.Walk p x) : Prop :=
  ∀ i, i < w.length →
    (i % 2 = 0 → K.Adj (w.getVert i) (w.getVert (i + 1))) ∧
    (i % 2 = 1 → H.Adj (w.getVert i) (w.getVert (i + 1)))

/-- A maximal alternating walk (STRIKE-A §6.10.1): trail, alternating from `K`,
and no unused demanded-half edge at the final vertex. -/
def IsMaximalAltWalk (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p x : V} (w : G.Walk p x) : Prop :=
  w.IsTrail ∧ AlternatesKH H K w ∧
  ∀ y : V,
    (w.length % 2 = 0 → K.Adj x y → s(x, y) ∈ w.edges) ∧
    (w.length % 2 = 1 → H.Adj x y → s(x, y) ∈ w.edges)

/-- The walk uses an edge lying inside the vertex set `S` (cuts that
component, when `S` is a cycle support). -/
def WalkCuts {G : SimpleGraph V} {p x : V} (w : G.Walk p x)
    (S : Finset V) : Prop :=
  ∃ e ∈ w.edges, ∀ v ∈ e, v ∈ S

/-- The walk cuts an odd component other than the poisoned support `S`: a
second odd `H`-cycle or any odd `K`-cycle (the REACH event of §6.10.4). -/
def CutsSecondOdd (H K : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (S : Finset V) {G : SimpleGraph V} {p x : V} (w : G.Walk p x) : Prop :=
  (∃ S' ∈ oddCycleSupports H, S' ≠ S ∧ WalkCuts w S') ∨
  (∃ S' ∈ oddCycleSupports K, WalkCuts w S')

/-- PROVED (round 15 helper).  At t ≤ 2, every vertex other than the two
degree-3 path ends is `H`-full. -/
lemma Hfull_of_t2
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3) :
    ∀ v, v ≠ p → v ≠ q → H.degree v = 2 := by
  intro v hvp hvq
  by_contra hv
  have hb := half_degree_bounds G H K hdeg hsplit v
  have hv1 : H.degree v = 1 := by omega
  have hv3 : G.degree v = 3 := by
    have hsum := hsplit.2.2.2.2.2.2 v
    have hK := hsplit.2.2.2.2.2.1 v
    rcases hdeg v with h | h <;> omega
  have hsub : ({p, q, v} : Finset V) ⊆
      Finset.univ.filter (fun u => G.degree u = 3) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hu with rfl | rfl | rfl
    · exact hp3
    · exact hq3
    · exact hv3
  have hqv : q ∉ ({v} : Finset V) := by
    simp only [Finset.mem_singleton]
    exact fun h => hvq h.symm
  have hpqv : p ∉ ({q, v} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hpq, fun h => hvp h.symm⟩
  have hcard : ({p, q, v} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem hpqv, Finset.card_insert_of_notMem hqv,
      Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  unfold numDeg3 at ht2
  omega

/-- LADDER-PIN 12a (§6.10.1 Theorem A).  Every maximal alternating walk of
positive length ends at `q`, and its edge set is a valid toggle. -/
lemma alt_walk_termination
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2)
    {x : V} (w : G.Walk p x)
    (hmax : IsMaximalAltWalk G H K w) (hlen : 0 < w.length) :
    x = q ∧ IsValidToggle G H K w.edges.toFinset := by
  have htrail := hmax.1
  have halt := hmax.2.1
  have hmaxend := hmax.2.2
  have hdisj := hsplit.2.1
  have hsum := hsplit.2.2.2.2.2.2
  -- The edge list of `w` written as the image of the index map.
  have hem : w.edges
      = (List.range w.length).map (fun i => s(w.getVert i, w.getVert (i + 1))) := by
    apply List.ext_getElem
    · simp [SimpleGraph.Walk.length_edges]
    · intro n h1 h2
      simp only [SimpleGraph.Walk.edges, List.getElem_map, List.getElem_range]
      rw [SimpleGraph.Walk.darts_getElem_eq_getVert]; rfl
  have hinj : Set.InjOn (fun i => s(w.getVert i, w.getVert (i + 1)))
      (Finset.range w.length) := by
    have hnd := htrail.edges_nodup
    rw [hem] at hnd
    rw [List.nodup_map_iff_inj_on List.nodup_range] at hnd
    intro i hi j hj hij
    exact hnd i (by simpa using hi) j (by simpa using hj) hij
  have himg : w.edges.toFinset
      = (Finset.range w.length).image (fun i => s(w.getVert i, w.getVert (i + 1))) := by
    rw [hem]; ext e; simp [List.mem_toFinset, Finset.mem_image]
  -- The H-side and K-side incidence counts, transferred to index sets.
  have hcardH : ∀ v, #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v}
      = #{i ∈ Finset.range w.length | i % 2 = 1 ∧
          (w.getVert i = v ∨ w.getVert (i + 1) = v)} := by
    intro v
    rw [himg, Finset.filter_image,
      Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    congr 1
    apply Finset.filter_congr
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
    constructor
    · rintro ⟨hadj, hv⟩
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · exact absurd ((halt i hi).1 h0) (hdisj _ _ hadj)
      · exact ⟨h1, by rcases hv with h | h <;> simp [h]⟩
    · rintro ⟨hodd, hv⟩
      exact ⟨(halt i hi).2 hodd, by rcases hv with h | h <;> simp [h]⟩
  have hcardK : ∀ v, #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v}
      = #{i ∈ Finset.range w.length | i % 2 = 0 ∧
          (w.getVert i = v ∨ w.getVert (i + 1) = v)} := by
    intro v
    rw [himg, Finset.filter_image,
      Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    congr 1
    apply Finset.filter_congr
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
    constructor
    · rintro ⟨hadj, hv⟩
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · exact ⟨h0, by rcases hv with h | h <;> simp [h]⟩
      · exact absurd hadj (hdisj _ _ ((halt i hi).2 h1))
    · rintro ⟨heven, hv⟩
      exact ⟨(halt i hi).1 heven, by rcases hv with h | h <;> simp [h]⟩
  -- The core (k − h) accounting identity, via telescoping.
  have hident : ∀ v,
      ((#{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v} : ℤ)
        - #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v})
      = (if p = v then (1 : ℤ) else 0)
        + (if w.length % 2 = 1 then (if x = v then 1 else 0)
            else -(if x = v then 1 else 0)) := by
    intro v
    rw [hcardK v, hcardH v]
    have tele : ∀ (L : ℕ) (f : ℕ → ℤ),
        (∑ i ∈ Finset.range L, (-1 : ℤ) ^ i * (f i + f (i + 1)))
          = f 0 - (-1 : ℤ) ^ L * f L := by
      intro L f; induction L with
      | zero => simp
      | succ L ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
    have key :
        ((#{i ∈ Finset.range w.length | i % 2 = 0 ∧
              (w.getVert i = v ∨ w.getVert (i + 1) = v)} : ℤ)
          - #{i ∈ Finset.range w.length | i % 2 = 1 ∧
              (w.getVert i = v ∨ w.getVert (i + 1) = v)})
        = ∑ i ∈ Finset.range w.length, (-1 : ℤ) ^ i *
            ((if w.getVert i = v then 1 else 0) + (if w.getVert (i + 1) = v then 1 else 0)) := by
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hne : w.getVert i ≠ w.getVert (i + 1) := (w.adj_getVert_succ hi).ne
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · have hev : Even i := Nat.even_iff.mpr h0
        rw [hev.neg_one_pow]
        by_cases a : w.getVert i = v <;> by_cases b : w.getVert (i + 1) = v <;> simp_all
      · have hod : Odd i := Nat.odd_iff.mpr h1
        rw [hod.neg_one_pow]
        by_cases a : w.getVert i = v <;> by_cases b : w.getVert (i + 1) = v <;> simp_all
    rw [key, tele, w.getVert_zero, w.getVert_length]
    rcases Nat.mod_two_eq_zero_or_one w.length with h0 | h1
    · have hev : Even w.length := Nat.even_iff.mpr h0
      rw [hev.neg_one_pow]; simp [h0]; split_ifs <;> ring
    · have hod : Odd w.length := Nat.odd_iff.mpr h1
      rw [hod.neg_one_pow]; simp [h1]; split_ifs <;> ring
  -- Degree bounds on the incidence counts.
  have hbH : ∀ v, #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v} ≤ H.degree v := by
    intro v
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (fun e he => (Finset.mem_filter.mp he).2)
  have hbK : ∀ v, #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v} ≤ K.degree v := by
    intro v
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    exact Finset.card_le_card (fun e he => (Finset.mem_filter.mp he).2)
  -- Maximality restated: at the final vertex every demanded-half edge is used.
  have hmaxK : w.length % 2 = 0 →
      #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset x} = K.degree x := by
    intro hL0
    have hset : {e ∈ w.edges.toFinset | e ∈ K.incidenceFinset x} = K.incidenceFinset x := by
      ext e
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff] at he
        obtain ⟨hadj, hx⟩ := he
        rcases hx with rfl | rfl
        · simpa [List.mem_toFinset] using (hmaxend b).1 hL0 hadj
        · simpa [List.mem_toFinset, Sym2.eq_swap] using (hmaxend a).1 hL0 hadj.symm
    rw [hset, SimpleGraph.card_incidenceFinset_eq_degree]
  have hmaxH : w.length % 2 = 1 →
      #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset x} = H.degree x := by
    intro hL1
    have hset : {e ∈ w.edges.toFinset | e ∈ H.incidenceFinset x} = H.incidenceFinset x := by
      ext e
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff] at he
        obtain ⟨hadj, hx⟩ := he
        rcases hx with rfl | rfl
        · simpa [List.mem_toFinset] using (hmaxend b).2 hL1 hadj
        · simpa [List.mem_toFinset, Sym2.eq_swap] using (hmaxend a).2 hL1 hadj.symm
    rw [hset, SimpleGraph.card_incidenceFinset_eq_degree]
  -- Every non-`p`, non-`q` vertex has degree 4.
  have hprofile : ∀ v, v ≠ p → v ≠ q → G.degree v = 4 := by
    intro v hvp hvq
    have h2 := hHfull v hvp hvq
    have hk := hK2 v
    have hs := hsum v
    omega
  -- The walk terminates at `q`.
  have hxq : x = q := by
    by_contra hxne
    have hi := hident x
    have hbHx := hbH x
    have hbKx := hbK x
    rcases Nat.mod_two_eq_zero_or_one w.length with h0 | h1
    · have hk := hmaxK h0
      rw [if_neg (by omega : ¬ w.length % 2 = 1)] at hi
      by_cases hxp : x = p
      · subst hxp
        rw [hpH] at hbHx; rw [hK2 x] at hk
        simp only [if_true] at hi; omega
      · have hHx := hHfull x hxp hxne
        rw [hHx] at hbHx; rw [hK2 x] at hk
        rw [if_neg (fun h : p = x => hxp h.symm), if_pos rfl] at hi
        omega
    · have hk := hmaxH h1
      rw [if_pos h1] at hi
      by_cases hxp : x = p
      · subst hxp
        rw [hpH] at hk; rw [hK2 x] at hbKx
        simp only [if_true] at hi
        omega
      · have hHx := hHfull x hxp hxne
        rw [hHx] at hk; rw [hK2 x] at hbKx
        rw [if_neg (fun h : p = x => hxp h.symm), if_pos rfl] at hi
        omega
  subst hxq
  refine ⟨rfl, ?_⟩
  have hTsub : (↑(w.edges.toFinset) : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact w.edges_subset_edgeSet he
  rw [toggle_valid_iff G H K hdeg hsplit _ hTsub]
  intro v
  refine ⟨?_, ?_, ?_⟩
  · intro hg4
    have hvp : p ≠ v := by rintro rfl; rw [hp3] at hg4; omega
    have hvq : x ≠ v := by rintro rfl; rw [hq3] at hg4; omega
    have hi := hident v
    simp only [if_neg hvp, if_neg hvq] at hi
    split_ifs at hi <;> omega
  · rintro ⟨_, hK1⟩
    rw [hK2 v] at hK1
    omega
  · rintro ⟨hH1, _⟩
    have hvpq : p = v ∨ x = v := by
      by_contra hcon
      push_neg at hcon
      rw [hHfull v (fun h => hcon.1 h.symm) (fun h => hcon.2 h.symm)] at hH1
      omega
    rcases hvpq with rfl | rfl
    · have hi := hident p
      have hqp : ¬ x = p := fun h => hpq h.symm
      right
      rcases Nat.mod_two_eq_zero_or_one w.length with h0 | h1
      · rw [if_pos rfl, if_neg (by omega : ¬ w.length % 2 = 1), if_neg hqp] at hi
        omega
      · rw [if_pos rfl, if_pos h1, if_neg hqp] at hi
        omega
    · have hi := hident x
      rw [if_neg (fun h : p = x => hpq h)] at hi
      rcases Nat.mod_two_eq_zero_or_one w.length with h0 | h1
      · exfalso
        have hk := hmaxK h0
        have hb := hbH x
        rw [hqH] at hb; rw [hK2 x] at hk
        rw [if_neg (by omega : ¬ w.length % 2 = 1), if_pos rfl] at hi
        omega
      · right
        rw [if_pos h1, if_pos rfl] at hi
        omega

/-- LADDER-PIN 12bc (§6.10.2 Theorem B + §6.10.3 Theorem C, joint EFFECT form;
see PINS2.md round-15 note).  The chain invariant and crossing dichotomy steer
any reach witness into a shape-1/2-disciplined maximal walk: it still cuts the
poisoned support and a second odd component, creates NO new odd `K`-cycle
support, and at most ONE new odd `H`-cycle support (the main cycle).  The
faithful per-trace forms of B and C (chain positions, `π` counts) require the
debris-linkage trace formalism, deferred with §9 item 11; this post-hoc form
is what Theorem D consumes.

SUPERSEDED (XSEL analysis, 2026-07-12; two bare-sorry Aristotle returns, W13 +
W16 — see rung4-moonshot/XSEL-ANALYSIS.md).  Two statement-level defects:
(1) it DROPS the config-(i) poison geometry (`S = {z₁,z₂,z₃}`, `K.Adj p z₁/z₂`,
`K.Adj q z₃`, `hvar`) that §6.10.4 uses to derive `WalkCuts w S` ("the walk's
first `H`-edge is a `Z`-edge") — with only `hS`, nothing forces a walk from `p`
to touch `S`, so the constructive route is blocked and only the vacuous route
(via `hmin`) remains, which is as hard as the whole theorem; (2) its conclusion
over-claims vs Theorem C's four winner shapes: shape 4 permits exactly one odd
private cycle ON EITHER SIDE, so "no new odd `K`-support" is not guaranteed by
the informal theorems.  Superseded by `maximal_walk_cuts_poisoned` +
`crossing_selection_geo` + `strict_of_reach_geo` below.  Kept for the record;
do NOT re-dispatch this form.
FALSIFIED 2026-07-13 (fresh-strike/LENS-B3-SURGERY.md §1,
fresh-strike/LENS-B3-INVARIANT.md §1): explicit 9-vertex counterexamples
falsify the geo/sum conclusion forms on instances satisfying every stated
geometry hypothesis; this two-conjunct conclusion is false a fortiori.
Kept ONLY because the retired `strict_of_reach` record still compiles
against it.  Historical record; never dispatch. -/
lemma crossing_selection
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hS : S ∈ oddCycleSupports H)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ WalkCuts w S ∧ CutsSecondOdd H K S w ∧
      oddCycleSupports (toggled K w.edges.toFinset) ⊆ oddCycleSupports K ∧
      (oddCycleSupports (toggled H w.edges.toFinset) \ oddCycleSupports H).card ≤ 1 := by
  sorry

/-- LADDER-PIN 12b-geo (NEW, round 19 restatement; §6.10.4 Theorem D's
"`a ≥ 1` always" parenthetical: "the walk's first `H`-edge is a `Z`-edge —
`p`'s `K`-germs enter `Z`, whose vertices' `H`-edges are `Z`-edges — so `Z` is
always cut").  Under the config-(i) poison geometry of `poisoned_t2_shape`,
EVERY maximal alternating walk from `p` cuts the poisoned support `S`: `p`'s
two `K`-edges both enter `S` (`K.degree p = 2` with `K.Adj p z₁`, `K.Adj p z₂`),
support vertices are `H`-degree-2 with both `H`-germs inside `S` (support
closure), and maximality forbids stopping at a support vertex with unused
`H`-germs — so the walk's second edge lies inside `S`. -/
lemma maximal_walk_cuts_poisoned
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p z₁ z₂ z₃ : V} {S : Finset V}
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂)
    (hK2 : ∀ v, K.degree v = 2)
    {x : V} (w : G.Walk p x)
    (hmax : IsMaximalAltWalk G H K w) :
    WalkCuts w S := by
  classical
  have hHle2 : ∀ v, H.degree v ≤ 2 := fun v => hsplit.2.2.2.2.1 v
  have halt := hmax.2.1
  have hmaxend := hmax.2.2
  -- Edge-membership from consecutive `getVert`s.
  have hedge : ∀ i, i < w.length →
      s(w.getVert i, w.getVert (i + 1)) ∈ w.edges := by
    intro i hi
    rw [show w.edges
        = (List.range w.length).map (fun j => s(w.getVert j, w.getVert (j + 1))) from ?_]
    · simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩
    · apply List.ext_getElem
      · simp [SimpleGraph.Walk.length_edges]
      · intro n h1 h2
        simp only [SimpleGraph.Walk.edges, List.getElem_map, List.getElem_range]
        rw [SimpleGraph.Walk.darts_getElem_eq_getVert]; rfl
  -- The three support vertices are distinct.
  have hcard3 : 3 ≤ S.card := oddCycleSupports_three_le_card H S hS
  have hz12 : z₁ ≠ z₂ := by
    rintro rfl
    rw [hSeq, Finset.insert_idem] at hcard3
    have := Finset.card_insert_le z₁ ({z₃} : Finset V)
    simp only [Finset.card_singleton] at this
    omega
  -- Extract the odd `H`-cycle whose support is `S`.
  obtain ⟨x0, c, hc⟩ :
      ∃ x0 : V, ∃ cc : H.Walk x0 x0,
        cc.IsCycle ∧ Odd cc.length ∧ cc.support.toFinset = S := by
    contrapose! hS; simp_all +decide [oddCycleSupports]
  have hg0 : w.getVert 0 = p := SimpleGraph.Walk.getVert_zero w
  -- The walk has positive length: the birth `K`-edge at `p` must be present.
  have hlen : 0 < w.length := by
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · exfalso
      have hxp : x = p := (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
      have hmem : s(x, z₁) ∈ w.edges :=
        (hmaxend z₁).1 (by omega) (hxp ▸ hpz₁)
      have : w.edges = [] := List.length_eq_zero_iff.mp (by
        rw [SimpleGraph.Walk.length_edges]; exact h0)
      rw [this] at hmem; simp at hmem
    · exact hpos
  -- The first edge is a `K`-edge from `p`.
  have hK01 : K.Adj p (w.getVert 1) := by
    have := (halt 0 hlen).1 (by decide)
    rwa [hg0] at this
  -- `p`'s two `K`-neighbours are exactly `z₁, z₂`, so `getVert 1 ∈ S`.
  have hsubn : ({z₁, z₂} : Finset V) ⊆ K.neighborFinset p := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact (K.mem_neighborFinset p a).mpr hpz₁
    · exact (K.mem_neighborFinset p a).mpr hpz₂
  have hcard2 : ({z₁, z₂} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hz12]), Finset.card_singleton]
  have hneq : ({z₁, z₂} : Finset V) = K.neighborFinset p := by
    apply Finset.eq_of_subset_of_card_le hsubn
    rw [K.card_neighborFinset_eq_degree, hK2 p, hcard2]
  have hv1mem : w.getVert 1 ∈ ({z₁, z₂} : Finset V) := by
    rw [hneq]; exact (K.mem_neighborFinset p _).mpr hK01
  have hv1S : w.getVert 1 ∈ S := by
    rw [hSeq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv1mem ⊢
    tauto
  -- `getVert 1` lies on the cycle `c`.
  have hv1sup : w.getVert 1 ∈ c.support :=
    List.mem_toFinset.mp (by rw [hc.2.2]; exact hv1S)
  by_cases hpS : p ∈ S
  · -- `p` itself is a support vertex, so the first (K-)edge lies inside `S`.
    refine ⟨s(w.getVert 0, w.getVert 1), hedge 0 hlen, ?_⟩
    intro v hv
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · rw [hg0]; exact hpS
    · exact hv1S
  · -- `p ∉ S`: maximality forces a second (H-)edge, which stays inside `S`.
    have hlen2 : 2 ≤ w.length := by
      by_contra hcon
      have hl1 : w.length = 1 := by omega
      have hx1 : x = w.getVert 1 := by
        rw [← hl1]; exact (SimpleGraph.Walk.getVert_length w).symm
      have hxS : x ∈ S := hx1 ▸ hv1S
      have hxsup : x ∈ c.support := List.mem_toFinset.mp (by rw [hc.2.2]; exact hxS)
      have hxdeg : H.degree x = 2 := oddCycleSupport_Hdeg2 H hHle2 hS x hxS
      obtain ⟨y, hy⟩ : ∃ y, H.Adj x y :=
        (H.degree_pos_iff_exists_adj x).mp (by omega)
      have hysup : y ∈ c.support := cycle_support_closed_adj H hHle2 hc.1 hxsup hy
      have hyS : y ∈ S := by rw [← hc.2.2]; exact List.mem_toFinset.mpr hysup
      have hmem : s(x, y) ∈ w.edges := (hmaxend y).2 (by rw [hl1]) hy
      have hedges1 : w.edges = [s(w.getVert 0, w.getVert 1)] := by
        apply List.ext_getElem
        · simp [SimpleGraph.Walk.length_edges, hl1]
        · intro n h1 h2
          simp only [SimpleGraph.Walk.length_edges, hl1] at h1
          interval_cases n
          · simp only [SimpleGraph.Walk.edges, List.getElem_map] at *
            rw [SimpleGraph.Walk.darts_getElem_eq_getVert]; rfl
      rw [hedges1] at hmem
      simp only [List.mem_singleton] at hmem
      rw [hg0, ← hx1] at hmem
      rw [Sym2.eq_iff] at hmem
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hpS (h1 ▸ hxS)
      · exact hpS (h2 ▸ hyS)
    -- The second edge is an `H`-edge inside `S`.
    have hHadj : H.Adj (w.getVert 1) (w.getVert 2) := (halt 1 (by omega)).2 (by decide)
    have hv2sup : w.getVert 2 ∈ c.support :=
      cycle_support_closed_adj H hHle2 hc.1 hv1sup hHadj
    have hv2S : w.getVert 2 ∈ S := by rw [← hc.2.2]; exact List.mem_toFinset.mpr hv2sup
    refine ⟨s(w.getVert 1, w.getVert 2), hedge 1 (by omega), ?_⟩
    intro v hv
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact hv1S
    · exact hv2S

/-! ## The Euler-trail route to NAV-CHAR (fresh-strike round 19, 2026-07-12)

Three independent fresh-context derivations (fresh-strike/LENS-MECHANISM.md,
Kotzig balance + virtual edge; fresh-strike/LENS-CYCLESPACE.md,
transition-merge/Hierholzer; fresh-strike/LEAD-TOGGLE.md, parity analysis)
converged on the same mechanism: the blocked world's degree profile
(`deg_K ≡ 2`; `deg_H ≡ 2` except `deg_H p = deg_H q = 1`) is exactly Kotzig's
condition after adding one virtual `H`-edge `pq`, so an ALTERNATING EULERIAN
`p → q` trail exists — a single maximal alternating walk using EVERY edge of
`G`.  NAV-CHAR's "dynamic return question" dissolves: the walk does not have
to navigate to the supply because it uses everything; `supply_of_blocked`
(PROVED) manufactures the supply in both parities.  Empirical support:
18,131/18,131 splits (mechanism lane) + 368/368 + 250/250 (cycle-space lane,
two independent algorithms), zero exceptions.

The route: PIN EULER-A (the one classical lemma, alternating Euler trail;
sorry — Aristotle target with the transition-merge proof plan) + EULER-B
(all-edges ⇒ maximal; PROVED) + EULER-C (odd supports carry an internal edge;
PROVED) + the assembly in `navchar_of_blocked` (PROVED from A+B+C+supply). -/

/-! ### Tagged germs for the transition-system proof

The two constructors of `anchorGermAt p q v` are formal half-edges at `p`
and `q`.  They are deliberately not represented by `s(p,q)`: that pair may
already be a real edge of either half of the split.  Adding these two tagged
germs makes the local `H` and `K` populations both have size two. -/

private abbrev colorGermAt (M : SimpleGraph V) [DecidableRel M.Adj] (v : V) :=
  M.neighborSet v

private inductive AnchorTag
  | atP
  | atQ
  deriving DecidableEq, Fintype

private def anchorTagsAt (p q v : V) : Finset AnchorTag :=
  (if v = p then {.atP} else ∅) ∪ (if v = q then {.atQ} else ∅)

private abbrev anchorGermAt (p q v : V) :=
  {a : AnchorTag // a ∈ anchorTagsAt p q v}

private abbrev augmentedHGermAt (H : SimpleGraph V) [DecidableRel H.Adj]
    (p q v : V) :=
  colorGermAt H v ⊕ anchorGermAt p q v

private lemma card_colorGermAt
    (M : SimpleGraph V) [DecidableRel M.Adj] (v : V) :
    Fintype.card (colorGermAt M v) = M.degree v := by
  exact SimpleGraph.card_neighborSet_eq_degree M v

private lemma card_anchorGermAt (p q v : V) (hpq : p ≠ q) :
    Fintype.card (anchorGermAt p q v) = if v = p ∨ v = q then 1 else 0 := by
  classical
  by_cases hvp : v = p
  · subst v
    simp [anchorTagsAt, hpq]
  · by_cases hvq : v = q
    · subst v
      simp [anchorTagsAt, hpq, hvp]
    · simp [anchorTagsAt, hvp, hvq]

private lemma vertex_eq_p_of_anchorAtP
    (p q v : V) (a : anchorGermAt p q v) (ha : a.1 = AnchorTag.atP) :
    v = p := by
  rcases a with ⟨a, haMem⟩
  dsimp at ha
  subst a
  by_contra hv
  have hnot : AnchorTag.atP ∉ anchorTagsAt p q v := by
    simp only [anchorTagsAt]
    rw [if_neg hv]
    split <;> simp
  exact hnot haMem

private lemma vertex_eq_q_of_anchorAtQ
    (p q v : V) (a : anchorGermAt p q v) (ha : a.1 = AnchorTag.atQ) :
    v = q := by
  rcases a with ⟨a, haMem⟩
  dsimp at ha
  subst a
  by_contra hv
  have hnot : AnchorTag.atQ ∉ anchorTagsAt p q v := by
    simp only [anchorTagsAt]
    rw [if_neg hv]
    split <;> simp
  exact hnot haMem

private lemma card_augmentedHGermAt_eq_two
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2) (v : V) :
    Fintype.card (augmentedHGermAt H p q v) = 2 := by
  rw [Fintype.card_sum, card_colorGermAt, card_anchorGermAt p q v hpq]
  by_cases hvp : v = p
  · subst v
    simp [hpH]
  · by_cases hvq : v = q
    · subst v
      simp [hqH]
    · simp [hvp, hvq, hHfull v hvp hvq]

private lemma exists_localTransition
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2) :
    ∀ v, Nonempty (colorGermAt K v ≃ augmentedHGermAt H p q v) := by
  intro v
  apply Fintype.card_eq.mp
  rw [card_colorGermAt, hK2 v,
    card_augmentedHGermAt_eq_two H hpq hpH hqH hHfull v]

private abbrev AltTransitionSystem
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) :=
  ∀ v, colorGermAt K v ≃ augmentedHGermAt H p q v

private lemma exists_altTransitionSystem
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2) :
    Nonempty (AltTransitionSystem H K p q) := by
  classical
  exact ⟨fun v =>
    (exists_localTransition H K hpq hpH hqH hHfull hK2 v).some⟩

private abbrev ColorGerm (M : SimpleGraph V) [DecidableRel M.Adj] :=
  Σ v, colorGermAt M v

private def reverseColorGerm
    (M : SimpleGraph V) [DecidableRel M.Adj] : ColorGerm M → ColorGerm M
  | ⟨v, u⟩ => ⟨u, v, u.property.symm⟩

private lemma reverseColorGerm_involutive
    (M : SimpleGraph V) [DecidableRel M.Adj] :
    Function.Involutive (reverseColorGerm M) := by
  rintro ⟨v, u, huv⟩
  rfl

private def colorGermEdge
    (M : SimpleGraph V) [DecidableRel M.Adj] (g : ColorGerm M) : Sym2 V :=
  s(g.1, g.2.1)

private lemma colorGermEdge_mem
    (M : SimpleGraph V) [DecidableRel M.Adj] (g : ColorGerm M) :
    colorGermEdge M g ∈ M.edgeSet := by
  exact g.2.2

private lemma colorGermEdge_reverse
    (M : SimpleGraph V) [DecidableRel M.Adj] (g : ColorGerm M) :
    colorGermEdge M (reverseColorGerm M g) = colorGermEdge M g := by
  rcases g with ⟨v, u, huv⟩
  exact Sym2.eq_swap

private abbrev AugmentedHColorGerm
    (H : SimpleGraph V) [DecidableRel H.Adj] :=
  ColorGerm H ⊕ AnchorTag

private def reverseAugmentedHColorGerm
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    AugmentedHColorGerm H → AugmentedHColorGerm H
  | .inl g => .inl (reverseColorGerm H g)
  | .inr .atP => .inr .atQ
  | .inr .atQ => .inr .atP

private lemma reverseAugmentedHColorGerm_involutive
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Function.Involutive (reverseAugmentedHColorGerm H) := by
  rintro (g | (_ | _))
  · simp only [reverseAugmentedHColorGerm, Sum.inl.injEq]
    rw [reverseColorGerm_involutive H g]
  · rfl
  · rfl

private abbrev AugmentedHGerm
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V) :=
  Σ v, augmentedHGermAt H p q v

private def altTransitionSystemEquiv
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) :
    ColorGerm K ≃ AugmentedHGerm H p q :=
  Equiv.sigmaCongrRight τ

private def reverseAugmentedHGerm
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V) :
    AugmentedHGerm H p q → AugmentedHGerm H p q
  | ⟨v, .inl u⟩ => ⟨u, .inl ⟨v, u.property.symm⟩⟩
  | ⟨_, .inr ⟨.atP, _⟩⟩ =>
      ⟨q, .inr ⟨.atQ, by simp [anchorTagsAt]⟩⟩
  | ⟨_, .inr ⟨.atQ, _⟩⟩ =>
      ⟨p, .inr ⟨.atP, by simp [anchorTagsAt]⟩⟩

private lemma reverseAugmentedHGerm_involutive
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V) :
    Function.Involutive (reverseAugmentedHGerm H p q) := by
  rintro ⟨v, (u | ⟨a, ha⟩)⟩
  · rfl
  · cases a with
    | atP =>
        have hv : v = p := by
          by_contra hv
          have hnot : AnchorTag.atP ∉ anchorTagsAt p q v := by
            simp only [anchorTagsAt]
            rw [if_neg hv]
            split <;> simp
          exact hnot ha
        subst v
        rfl
    | atQ =>
        have hv : v = q := by
          by_contra hv
          have hnot : AnchorTag.atQ ∉ anchorTagsAt p q v := by
            simp only [anchorTagsAt]
            rw [if_neg hv]
            split <;> simp
          exact hnot ha
        subst v
        rfl

private def reverseColorGermEquiv
    (M : SimpleGraph V) [DecidableRel M.Adj] : ColorGerm M ≃ ColorGerm M where
  toFun := reverseColorGerm M
  invFun := reverseColorGerm M
  left_inv := reverseColorGerm_involutive M
  right_inv := reverseColorGerm_involutive M

private def reverseAugmentedHGermEquiv
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V) :
    AugmentedHGerm H p q ≃ AugmentedHGerm H p q where
  toFun := reverseAugmentedHGerm H p q
  invFun := reverseAugmentedHGerm H p q
  left_inv := reverseAugmentedHGerm_involutive H p q
  right_inv := reverseAugmentedHGerm_involutive H p q

private def transitionComponentPerm
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) : Equiv.Perm (ColorGerm K) :=
  (reverseColorGermEquiv K).trans
    ((altTransitionSystemEquiv H K p q τ).trans
      ((reverseAugmentedHGermEquiv H p q).trans
        (altTransitionSystemEquiv H K p q τ).symm))

private lemma transitionComponentPerm_pairing_step
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K) :
    altTransitionSystemEquiv H K p q τ
        (transitionComponentPerm H K p q τ g) =
      reverseAugmentedHGerm H p q
        (altTransitionSystemEquiv H K p q τ (reverseColorGerm K g)) := by
  simp [transitionComponentPerm, reverseColorGermEquiv,
    reverseAugmentedHGermEquiv]

private lemma transitionComponentPerm_real_adj
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q v u : V) (τ : AltTransitionSystem H K p q)
    (hK : K.Adj v u) (h : colorGermAt H u)
    (hpair : τ u ⟨v, hK.symm⟩ = .inl h) :
    H.Adj u (transitionComponentPerm H K p q τ ⟨v, u, hK⟩).1 := by
  have hstep := transitionComponentPerm_pairing_step H K p q τ
    (⟨v, u, hK⟩ : ColorGerm K)
  have hv := congrArg Sigma.fst hstep
  simp [altTransitionSystemEquiv, reverseColorGerm,
    reverseAugmentedHGerm, hpair] at hv
  rw [hv]
  exact h.property

private def anchorGermAtP (p q : V) : anchorGermAt p q p :=
  ⟨.atP, by simp [anchorTagsAt]⟩

private def anchorGermAtQ (p q : V) : anchorGermAt p q q :=
  ⟨.atQ, by simp [anchorTagsAt]⟩

private def anchorKGermP
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) : ColorGerm K :=
  ⟨p, (τ p).symm (.inr (anchorGermAtP p q))⟩

private def anchorKGermQ
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) : ColorGerm K :=
  ⟨q, (τ q).symm (.inr (anchorGermAtQ p q))⟩

private lemma altTransitionSystemEquiv_anchorKGermP
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) :
    altTransitionSystemEquiv H K p q τ (anchorKGermP H K p q τ) =
      ⟨p, .inr (anchorGermAtP p q)⟩ := by
  simp [altTransitionSystemEquiv, anchorKGermP]

private lemma altTransitionSystemEquiv_anchorKGermQ
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) :
    altTransitionSystemEquiv H K p q τ (anchorKGermQ H K p q τ) =
      ⟨q, .inr (anchorGermAtQ p q)⟩ := by
  simp [altTransitionSystemEquiv, anchorKGermQ]

private lemma transitionComponentPerm_eq_anchorP_ends_q
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K)
    (hnext : transitionComponentPerm H K p q τ g =
      anchorKGermP H K p q τ) :
    (reverseColorGerm K g).1 = q := by
  rcases g with ⟨v, u, hK⟩
  change u = q
  have hstep := transitionComponentPerm_pairing_step H K p q τ
    (⟨v, u, hK⟩ : ColorGerm K)
  rw [hnext, altTransitionSystemEquiv_anchorKGermP H K p q τ] at hstep
  cases hval : τ u ⟨v, hK.symm⟩ with
  | inl h =>
      simp [altTransitionSystemEquiv, reverseColorGerm,
        reverseAugmentedHGerm, hval] at hstep
      cases hstep.1
      have hbad := hstep.2
      rw [heq_eq_eq] at hbad
      simp at hbad
  | inr a =>
      rcases a with ⟨a, ha⟩
      cases a with
      | atP =>
          simp [altTransitionSystemEquiv, reverseColorGerm,
            reverseAugmentedHGerm, hval] at hstep
          exact (vertex_eq_p_of_anchorAtP p q u ⟨.atP, ha⟩ rfl).trans hstep.1
      | atQ =>
          exact vertex_eq_q_of_anchorAtQ p q u ⟨.atQ, ha⟩ rfl

private def walkOfIsChain (G : SimpleGraph V) (a : V) :
    (l : List V) → List.IsChain G.Adj (a :: l) → Σ b, G.Walk a b
  | [], _ => ⟨a, SimpleGraph.Walk.nil⟩
  | b :: l, h =>
      let hab : G.Adj a b := (List.isChain_cons_cons.mp h).1
      let htail : List.IsChain G.Adj (b :: l) := (List.isChain_cons_cons.mp h).2
      let w := walkOfIsChain G b l htail
      ⟨w.1, SimpleGraph.Walk.cons hab w.2⟩

private def flattenColorGerms
    (M : SimpleGraph V) [DecidableRel M.Adj] : List (ColorGerm M) → List V
  | [] => []
  | g :: gs => g.1 :: g.2.1 :: flattenColorGerms M gs

private def consecutiveEdges (a : V) : List V → List (Sym2 V)
  | [] => []
  | b :: l => s(a, b) :: consecutiveEdges b l

private lemma walkOfIsChain_edges
    (G : SimpleGraph V) (a : V) (l : List V)
    (h : List.IsChain G.Adj (a :: l)) :
    (walkOfIsChain G a l h).2.edges = consecutiveEdges a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
      simp only [walkOfIsChain, SimpleGraph.Walk.edges_cons, consecutiveEdges,
        List.cons.injEq, true_and]
      exact ih b (List.isChain_cons_cons.mp h).2

private noncomputable def anchorComponent
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) : Finset (ColorGerm K) := by
  classical
  exact Finset.univ.filter fun g =>
    (transitionComponentPerm H K p q τ).SameCycle
      (anchorKGermP H K p q τ) g

private noncomputable def anchorOrbit
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) : List (ColorGerm K) := by
  classical
  let σ := transitionComponentPerm H K p q τ
  let a := anchorKGermP H K p q τ
  exact if σ a = a then [a] else σ.toList a

private lemma anchorOrbit_nodup
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) :
    (anchorOrbit H K p q τ).Nodup := by
  classical
  simp only [anchorOrbit]
  split
  · exact List.nodup_singleton _
  · exact Equiv.Perm.nodup_toList _ _

private lemma mem_anchorOrbit_iff_mem_anchorComponent
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K) :
    g ∈ anchorOrbit H K p q τ ↔ g ∈ anchorComponent H K p q τ := by
  classical
  let σ := transitionComponentPerm H K p q τ
  let a := anchorKGermP H K p q τ
  have hcomponent :
      g ∈ anchorComponent H K p q τ ↔ σ.SameCycle a g := by
    simp [anchorComponent, σ, a]
  rw [hcomponent]
  change g ∈ (if σ a = a then [a] else σ.toList a) ↔ σ.SameCycle a g
  by_cases hfix : σ a = a
  · rw [if_pos hfix]
    constructor
    · intro hg
      simp only [List.mem_singleton] at hg
      subst g
      exact Equiv.Perm.SameCycle.rfl
    · intro hg
      have hag : a = g := hg.eq_of_left hfix
      simpa [hag]
  · rw [if_neg hfix, Equiv.Perm.mem_toList_iff]
    simp [Equiv.Perm.mem_support, hfix]

private lemma anchorOrbit_shape
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) :
    let σ := transitionComponentPerm H K p q τ
    let a := anchorKGermP H K p q τ
    (σ a = a ∧ anchorOrbit H K p q τ = [a]) ∨
      (σ a ≠ a ∧ anchorOrbit H K p q τ = σ.toList a) := by
  classical
  let σ := transitionComponentPerm H K p q τ
  let a := anchorKGermP H K p q τ
  by_cases hfix : σ a = a
  · exact Or.inl ⟨hfix, by simp [anchorOrbit, σ, a, hfix]⟩
  · exact Or.inr ⟨hfix, by simp [anchorOrbit, σ, a, hfix]⟩

private lemma exists_anchorComponent_maximizer
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (hne : Nonempty (AltTransitionSystem H K p q)) :
    ∃ τ : AltTransitionSystem H K p q, ∀ τ',
      (anchorComponent H K p q τ').card ≤
        (anchorComponent H K p q τ).card := by
  classical
  letI : Nonempty (AltTransitionSystem H K p q) := hne
  obtain ⟨τ, _, hτ⟩ := Finset.exists_max_image
    (Finset.univ : Finset (AltTransitionSystem H K p q))
    (fun σ => (anchorComponent H K p q σ).card) Finset.univ_nonempty
  exact ⟨τ, fun τ' => hτ τ' (Finset.mem_univ τ')⟩

/-! ### Crossover surgery (the EULER-A maximality-exchange crux)

Abstract toolkit: a permutation `g` agreeing with `f` everywhere except that
it crosses over at two points of different `f`-cycles has those two cycles
merged (`sameCycle_of_crossover`); a permutation agreeing with `f` on the
whole `f`-cycle of `z` has the same cycle through `z`
(`sameCycle_iff_of_agree_on_cycle`).

Structural facts about the successor `σ`: the `K`-germ reversal `R`
conjugates `σ` to `σ⁻¹` (`transitionPerm_reverse_conj`), and since both `R`
and the `H`-hop `g ↦ σ (R g)` are fixed-point-free, NO `σ`-orbit contains a
germ together with its reversal (`not_sameCycle_reverse`).  This kills every
degenerate case of the exchange: re-pairing the two `K`-germs at one vertex
changes `σ` at exactly four points — two virtual transpositions — and the
no-self-reverse fact guarantees each transposition merges (never splits), so
the anchor component strictly grows, contradicting maximality. -/

private lemma sameCycle_crossover_one_side
    {α : Type*} [Fintype α] [DecidableEq α] {f g : Equiv.Perm α} {x y : α}
    (hxy : ¬ f.SameCycle x y)
    (hgx : g x = f y)
    (hgz : ∀ z, z ≠ x → z ≠ y → g z = f z) :
    ∀ z, f.SameCycle y z → g.SameCycle x z := by
  classical
  set m := Function.minimalPeriod (⇑f) y with hm
  have hmem : y ∈ Function.periodicPts (⇑f) := by
    refine Function.mem_periodicPts.mpr ⟨orderOf f, orderOf_pos f, ?_⟩
    show (⇑f)^[orderOf f] y = y
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hmpos : 0 < m := Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hfm : (f ^ m) y = y := by
    have h := Function.iterate_minimalPeriod (f := ⇑f) (x := y)
    rw [← hm] at h
    rw [Equiv.Perm.coe_pow]
    exact h
  have key : ∀ n : ℕ, 0 < n → n ≤ m → (g ^ n) x = (f ^ n) y := by
    intro n
    induction n with
    | zero => exact fun h _ => absurd h (Nat.lt_irrefl 0)
    | succ k ih =>
      intro _ hk1m
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hgx
      · have hkm : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk1m
        have hprev := ih hk hkm.le
        have hne_y : (f ^ k) y ≠ y := by
          intro hfix
          have hper : Function.IsPeriodicPt (⇑f) k y := by
            show (⇑f)^[k] y = y
            rw [← Equiv.Perm.coe_pow]
            exact hfix
          have hle := hper.minimalPeriod_le hk
          rw [← hm] at hle
          omega
        have hne_x : (f ^ k) y ≠ x := by
          intro hfix
          exact hxy (Equiv.Perm.SameCycle.symm
            ⟨(k : ℤ), by rw [zpow_natCast]; exact hfix⟩)
        calc (g ^ (k + 1)) x = g ((g ^ k) x) := by
              rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ k) y) := by rw [hprev]
          _ = f ((f ^ k) y) := hgz _ hne_x hne_y
          _ = (f ^ (k + 1)) y := by rw [pow_succ', Equiv.Perm.mul_apply]
  intro z hz
  obtain ⟨i, _, hiz⟩ := hz.exists_pow_eq'
  have hiter : (f ^ (i % m)) y = (f ^ i) y := by
    have h := Function.iterate_mod_minimalPeriod_eq (f := ⇑f) (x := y) (n := i)
    rw [← hm] at h
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
    exact h
  by_cases hi0 : i % m = 0
  · have hzy : y = z := by
      rw [← hiz, ← hiter, hi0, pow_zero, Equiv.Perm.one_apply]
    exact ⟨(m : ℤ), by rw [zpow_natCast, key m hmpos le_rfl, hfm, hzy]⟩
  · have hpos : 0 < i % m := Nat.pos_of_ne_zero hi0
    have hlt : i % m < m := Nat.mod_lt _ hmpos
    exact ⟨((i % m : ℕ) : ℤ), by rw [zpow_natCast, key _ hpos hlt.le, hiter, hiz]⟩

private lemma sameCycle_of_crossover
    {α : Type*} [Fintype α] [DecidableEq α] {f g : Equiv.Perm α} {x y : α}
    (hxy : ¬ f.SameCycle x y)
    (hgx : g x = f y) (hgy : g y = f x)
    (hgz : ∀ z, z ≠ x → z ≠ y → g z = f z) :
    ∀ z, f.SameCycle x z ∨ f.SameCycle y z → g.SameCycle x z := by
  have hxy' : ¬ f.SameCycle y x := fun h => hxy h.symm
  have hswap : ∀ z, z ≠ y → z ≠ x → g z = f z := fun z hzy hzx => hgz z hzx hzy
  have hy_side := sameCycle_crossover_one_side hxy hgx hgz
  have hx_side := sameCycle_crossover_one_side hxy' hgy hswap
  have hbridge : g.SameCycle x y := hy_side y (Equiv.Perm.SameCycle.refl f y)
  rintro z (hzx | hzy)
  · exact hbridge.trans (hx_side z hzx)
  · exact hy_side z hzy

private lemma sameCycle_iff_of_agree_on_cycle
    {α : Type*} [Fintype α] [DecidableEq α] {f g : Equiv.Perm α} {z : α}
    (hagree : ∀ w, f.SameCycle z w → g w = f w) :
    ∀ w, g.SameCycle z w ↔ f.SameCycle z w := by
  have key : ∀ n : ℕ, (g ^ n) z = (f ^ n) z := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
        hagree _ ⟨(k : ℤ), by rw [zpow_natCast]⟩]
  intro w
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, ← key, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, key, hn]⟩

private lemma reverseColorGerm_ne
    (K : SimpleGraph V) [DecidableRel K.Adj] (z : ColorGerm K) :
    reverseColorGerm K z ≠ z := by
  rcases z with ⟨v, u, huv⟩
  intro h
  have hfst := congrArg Sigma.fst h
  exact ((SimpleGraph.mem_neighborSet K v u).mp huv).ne' hfst

private lemma reverseAugmentedHGerm_fst_ne
    (H : SimpleGraph V) [DecidableRel H.Adj] {p q : V} (hpq : p ≠ q)
    (u : AugmentedHGerm H p q) :
    (reverseAugmentedHGerm H p q u).1 ≠ u.1 := by
  rcases u with ⟨v, hg | a⟩
  · exact ((SimpleGraph.mem_neighborSet H v hg.1).mp hg.2).ne'
  · rcases a with ⟨tag, ht⟩
    cases tag with
    | atP =>
      have hv : v = p := vertex_eq_p_of_anchorAtP p q v ⟨.atP, ht⟩ rfl
      subst hv
      exact fun hqp => hpq hqp.symm
    | atQ =>
      have hv : v = q := vertex_eq_q_of_anchorAtQ p q v ⟨.atQ, ht⟩ rfl
      subst hv
      exact fun hpq' => hpq hpq'

private lemma transitionPerm_reverse_apply
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (z : ColorGerm K) :
    transitionComponentPerm H K p q τ (reverseColorGerm K z)
      = (altTransitionSystemEquiv H K p q τ).symm
          (reverseAugmentedHGermEquiv H p q (altTransitionSystemEquiv H K p q τ z)) := by
  simp only [transitionComponentPerm, Equiv.trans_apply]
  rw [show reverseColorGermEquiv K (reverseColorGerm K z) = z from
    reverseColorGerm_involutive K z]

private lemma transitionPerm_reverse_fst_ne
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    (z : ColorGerm K) :
    (transitionComponentPerm H K p q τ (reverseColorGerm K z)).1 ≠ z.1 := by
  rw [transitionPerm_reverse_apply]
  exact reverseAugmentedHGerm_fst_ne H hpq (altTransitionSystemEquiv H K p q τ z)

private lemma transitionPerm_reverse_ne
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    (z : ColorGerm K) :
    transitionComponentPerm H K p q τ (reverseColorGerm K z) ≠ z :=
  fun h => transitionPerm_reverse_fst_ne H K hpq τ z (congrArg Sigma.fst h)

private lemma transitionPerm_reverse_conj
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (z : ColorGerm K) :
    reverseColorGerm K (transitionComponentPerm H K p q τ z)
      = (transitionComponentPerm H K p q τ)⁻¹ (reverseColorGerm K z) := by
  rw [Equiv.Perm.eq_inv_iff_eq]
  rw [transitionPerm_reverse_apply H K p q τ (transitionComponentPerm H K p q τ z)]
  rw [transitionComponentPerm_pairing_step H K p q τ z]
  rw [show reverseAugmentedHGermEquiv H p q
        (reverseAugmentedHGerm H p q
          (altTransitionSystemEquiv H K p q τ (reverseColorGerm K z)))
      = altTransitionSystemEquiv H K p q τ (reverseColorGerm K z) from
    reverseAugmentedHGerm_involutive H p q _]
  exact Equiv.symm_apply_apply _ _

private lemma transitionPerm_reverse_zpow
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (i : ℤ) (z : ColorGerm K) :
    reverseColorGerm K ((transitionComponentPerm H K p q τ ^ i) z)
      = ((transitionComponentPerm H K p q τ) ^ (-i)) (reverseColorGerm K z) := by
  classical
  set R : Equiv.Perm (ColorGerm K) := reverseColorGermEquiv K with hR
  have hRR : R * R = 1 := by
    apply Equiv.ext
    intro w
    show R (R w) = w
    exact reverseColorGerm_involutive K w
  have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_right hRR
  have hconj : R * transitionComponentPerm H K p q τ * R
      = (transitionComponentPerm H K p q τ)⁻¹ := by
    apply Equiv.ext
    intro w
    show R (transitionComponentPerm H K p q τ (R w))
      = (transitionComponentPerm H K p q τ)⁻¹ w
    have h := transitionPerm_reverse_conj H K p q τ
      (reverseColorGerm K w)
    rw [show reverseColorGerm K (reverseColorGerm K w) = w from
      reverseColorGerm_involutive K w] at h
    exact h
  have hzpow : R * (transitionComponentPerm H K p q τ) ^ i * R
      = (transitionComponentPerm H K p q τ) ^ (-i) := by
    have h1 : R * (transitionComponentPerm H K p q τ) ^ i * R⁻¹
        = (R * transitionComponentPerm H K p q τ * R⁻¹) ^ i := conj_zpow.symm
    rw [hRinv] at h1
    rw [h1, hconj, zpow_neg, inv_zpow]
  have happ : (R * (transitionComponentPerm H K p q τ) ^ i * R)
      (reverseColorGerm K z)
      = reverseColorGerm K (((transitionComponentPerm H K p q τ) ^ i) z) := by
    show R (((transitionComponentPerm H K p q τ) ^ i)
      (R (reverseColorGerm K z))) = _
    rw [show R (reverseColorGerm K z) = z from reverseColorGerm_involutive K z]
    rfl
  rw [← hzpow]
  exact happ.symm

private lemma sameCycle_reverse_of_sameCycle
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) {z w : ColorGerm K}
    (h : (transitionComponentPerm H K p q τ).SameCycle z w) :
    (transitionComponentPerm H K p q τ).SameCycle
      (reverseColorGerm K z) (reverseColorGerm K w) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨-i, by rw [← transitionPerm_reverse_zpow, hi]⟩

private lemma not_sameCycle_reverse
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    (g : ColorGerm K) :
    ¬ (transitionComponentPerm H K p q τ).SameCycle g (reverseColorGerm K g) := by
  rintro ⟨j, hj⟩
  rcases Int.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- j = k + k : the reversal would fix σ^k g — impossible.
    have h1 : reverseColorGerm K ((transitionComponentPerm H K p q τ ^ k) g)
        = (transitionComponentPerm H K p q τ ^ k) g := by
      rw [transitionPerm_reverse_zpow, ← hj, ← Equiv.Perm.mul_apply, ← zpow_add,
        show -k + j = k by omega]
    exact reverseColorGerm_ne K _ h1
  · -- j = 2k + 1 : the H-hop would fix σ^(k+1) g — impossible.
    have h1 : transitionComponentPerm H K p q τ
        (reverseColorGerm K ((transitionComponentPerm H K p q τ ^ (k + 1)) g))
        = (transitionComponentPerm H K p q τ ^ (k + 1)) g := by
      rw [transitionPerm_reverse_zpow, ← hj]
      have e1 : ((transitionComponentPerm H K p q τ) ^ (-(k + 1) : ℤ))
          (((transitionComponentPerm H K p q τ) ^ j) g)
          = ((transitionComponentPerm H K p q τ) ^ (-(k + 1) + j)) g := by
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
      rw [e1, show -(k + 1) + j = k by omega,
        show ((k : ℤ) + 1) = 1 + k by omega, zpow_one_add, Equiv.Perm.mul_apply]
    exact transitionPerm_reverse_ne H K hpq τ _ h1

private lemma mem_anchorComponent_iff
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K) :
    g ∈ anchorComponent H K p q τ ↔
      (transitionComponentPerm H K p q τ).SameCycle
        (anchorKGermP H K p q τ) g := by
  classical
  simp [anchorComponent]

/-- A germ lies on the anchor side if its `σ`-orbit or its reversal's
`σ`-orbit is the anchor component. -/
private def inAnchorSide
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K) : Prop :=
  (transitionComponentPerm H K p q τ).SameCycle (anchorKGermP H K p q τ) g ∨
  (transitionComponentPerm H K p q τ).SameCycle (anchorKGermP H K p q τ)
    (reverseColorGerm K g)

private lemma swap_sigma_mk
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {v : V} (k1 k2 k : colorGermAt K v) :
    Equiv.swap (⟨v, k1⟩ : ColorGerm K) ⟨v, k2⟩ ⟨v, k⟩
      = ⟨v, Equiv.swap k1 k2 k⟩ := by
  classical
  by_cases h1 : k = k1
  · subst h1
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases h2 : k = k2
    · subst h2
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun hc => h1 (by simpa using hc))
        (fun hc => h2 (by simpa using hc)),
        Equiv.swap_apply_of_ne_of_ne h1 h2]

private lemma swap_sigma_fix
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {v w : V} (hw : w ≠ v) (k1 k2 : colorGermAt K v) (k : colorGermAt K w) :
    Equiv.swap (⟨v, k1⟩ : ColorGerm K) ⟨v, k2⟩ ⟨w, k⟩ = ⟨w, k⟩ := by
  classical
  exact Equiv.swap_apply_of_ne_of_ne (fun hc => hw (congrArg Sigma.fst hc))
    (fun hc => hw (congrArg Sigma.fst hc))

set_option maxHeartbeats 1000000 in
/-- The exchange: at a vertex carrying an anchor-side `K`-germ and a foreign
`K`-germ, crossing the two pairings splices the foreign orbit into the anchor
component, strictly growing it. -/
private lemma exists_bigger_anchorComponent_of_mixed
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    {v : V} {k1 k2 : colorGermAt K v} (hk : k1 ≠ k2)
    (h1 : inAnchorSide H K p q τ ⟨v, k1⟩)
    (h2d : ¬ (transitionComponentPerm H K p q τ).SameCycle
      (anchorKGermP H K p q τ) ⟨v, k2⟩)
    (h2r : ¬ (transitionComponentPerm H K p q τ).SameCycle
      (anchorKGermP H K p q τ) (reverseColorGerm K ⟨v, k2⟩)) :
    ∃ τ' : AltTransitionSystem H K p q,
      (anchorComponent H K p q τ).card < (anchorComponent H K p q τ').card := by
  classical
  set d1 : ColorGerm K := ⟨v, k1⟩ with hd1def
  set d2 : ColorGerm K := ⟨v, k2⟩ with hd2def
  have hd12 : d1 ≠ d2 := by
    intro h
    exact hk (by simpa [hd1def, hd2def] using h)
  have hRR : ∀ z : ColorGerm K,
      reverseColorGerm K (reverseColorGerm K z) = z :=
    reverseColorGerm_involutive K
  -- shorthand facts
  have hstep1 : (transitionComponentPerm H K p q τ).SameCycle
      ((transitionComponentPerm H K p q τ)⁻¹ d1) d1 := ⟨1, by simp⟩
  have hstep2 : (transitionComponentPerm H K p q τ).SameCycle
      ((transitionComponentPerm H K p q τ)⁻¹ d2) d2 := ⟨1, by simp⟩
  have nrv1 : ¬ (transitionComponentPerm H K p q τ).SameCycle d1
      (reverseColorGerm K d1) := not_sameCycle_reverse H K hpq τ d1
  have nrv2 : ¬ (transitionComponentPerm H K p q τ).SameCycle d2
      (reverseColorGerm K d2) := not_sameCycle_reverse H K hpq τ d2
  -- cross-cycle disjointness bookkeeping
  have nc12 : ¬ (transitionComponentPerm H K p q τ).SameCycle d1 d2 := by
    intro hc
    rcases h1 with h1l | h1r
    · exact h2d (h1l.trans hc)
    · exact h2r (h1r.trans (sameCycle_reverse_of_sameCycle H K p q τ hc))
  have nc1R2 : ¬ (transitionComponentPerm H K p q τ).SameCycle d1
      (reverseColorGerm K d2) := by
    intro hc
    rcases h1 with h1l | h1r
    · exact h2r (h1l.trans hc)
    · have h := sameCycle_reverse_of_sameCycle H K p q τ hc
      rw [hRR] at h
      exact h2d (h1r.trans h)
  have ncR1d2 : ¬ (transitionComponentPerm H K p q τ).SameCycle
      (reverseColorGerm K d1) d2 := by
    intro hc
    rcases h1 with h1l | h1r
    · have h := sameCycle_reverse_of_sameCycle H K p q τ hc
      rw [hRR] at h
      exact h2r (h1l.trans h)
    · exact h2d (h1r.trans hc)
  have ncR1R2 : ¬ (transitionComponentPerm H K p q τ).SameCycle
      (reverseColorGerm K d1) (reverseColorGerm K d2) := by
    intro hc
    have h := sameCycle_reverse_of_sameCycle H K p q τ hc
    rw [hRR, hRR] at h
    exact nc12 h
  -- the crossed transition system
  set τ' : AltTransitionSystem H K p q :=
    Function.update τ v ((Equiv.swap k1 k2).trans (τ v)) with hτ'def
  have hE' : altTransitionSystemEquiv H K p q τ'
      = (Equiv.swap d1 d2).trans (altTransitionSystemEquiv H K p q τ) := by
    apply Equiv.ext
    rintro ⟨w, k⟩
    by_cases hw : w = v
    · subst hw
      simp only [altTransitionSystemEquiv, Equiv.sigmaCongrRight_apply,
        Equiv.trans_apply, hτ'def, hd1def, hd2def, Function.update_self,
        swap_sigma_mk]
    · simp only [altTransitionSystemEquiv, Equiv.sigmaCongrRight_apply,
        Equiv.trans_apply, hτ'def, hd1def, hd2def, Function.update_of_ne hw,
        swap_sigma_fix K hw]
  -- pointwise description of the new successor
  have hσ'app : ∀ z, transitionComponentPerm H K p q τ' z
      = Equiv.swap d1 d2 (transitionComponentPerm H K p q τ
          (reverseColorGerm K (Equiv.swap d1 d2 (reverseColorGerm K z)))) := by
    intro z
    show (altTransitionSystemEquiv H K p q τ').symm
        (reverseAugmentedHGermEquiv H p q
          (altTransitionSystemEquiv H K p q τ' (reverseColorGermEquiv K z))) = _
    rw [hE']
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_swap]
    rw [← transitionPerm_reverse_apply H K p q τ
      (Equiv.swap d1 d2 (reverseColorGermEquiv K z))]
    rfl
  -- the intermediate single-swap permutation
  set g0 : Equiv.Perm (ColorGerm K) :=
    transitionComponentPerm H K p q τ *
      Equiv.swap ((transitionComponentPerm H K p q τ)⁻¹ d1)
        ((transitionComponentPerm H K p q τ)⁻¹ d2) with hg0def
  have hinv12 : (transitionComponentPerm H K p q τ)⁻¹ d1
      ≠ (transitionComponentPerm H K p q τ)⁻¹ d2 :=
    fun h => hd12 (Equiv.injective _ h)
  have hg0x : g0 ((transitionComponentPerm H K p q τ)⁻¹ d1) = d2 := by
    rw [hg0def, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.Perm.apply_inv_self]
  have hg0y : g0 ((transitionComponentPerm H K p q τ)⁻¹ d2) = d1 := by
    rw [hg0def, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.Perm.apply_inv_self]
  have hg0z : ∀ z, z ≠ (transitionComponentPerm H K p q τ)⁻¹ d1 →
      z ≠ (transitionComponentPerm H K p q τ)⁻¹ d2 →
      g0 z = transitionComponentPerm H K p q τ z := by
    intro z hz1 hz2
    rw [hg0def, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hz1 hz2]
  -- vertex-move facts kill the coincidences
  have hfst1 : (transitionComponentPerm H K p q τ (reverseColorGerm K d1)).1 ≠ v :=
    transitionPerm_reverse_fst_ne H K hpq τ d1
  have hfst2 : (transitionComponentPerm H K p q τ (reverseColorGerm K d2)).1 ≠ v :=
    transitionPerm_reverse_fst_ne H K hpq τ d2
  have hηd1_ne1 : transitionComponentPerm H K p q τ (reverseColorGerm K d1) ≠ d1 :=
    fun h => hfst1 (by rw [h])
  have hηd1_ne2 : transitionComponentPerm H K p q τ (reverseColorGerm K d1) ≠ d2 :=
    fun h => hfst1 (by rw [h])
  have hηd2_ne1 : transitionComponentPerm H K p q τ (reverseColorGerm K d2) ≠ d1 :=
    fun h => hfst2 (by rw [h])
  have hηd2_ne2 : transitionComponentPerm H K p q τ (reverseColorGerm K d2) ≠ d2 :=
    fun h => hfst2 (by rw [h])
  have hRd1_ne_inv1 : reverseColorGerm K d1
      ≠ (transitionComponentPerm H K p q τ)⁻¹ d1 :=
    fun h => hηd1_ne1 (by rw [h, Equiv.Perm.apply_inv_self])
  have hRd1_ne_inv2 : reverseColorGerm K d1
      ≠ (transitionComponentPerm H K p q τ)⁻¹ d2 :=
    fun h => hηd1_ne2 (by rw [h, Equiv.Perm.apply_inv_self])
  have hRd2_ne_inv1 : reverseColorGerm K d2
      ≠ (transitionComponentPerm H K p q τ)⁻¹ d1 :=
    fun h => hηd2_ne1 (by rw [h, Equiv.Perm.apply_inv_self])
  have hRd2_ne_inv2 : reverseColorGerm K d2
      ≠ (transitionComponentPerm H K p q τ)⁻¹ d2 :=
    fun h => hηd2_ne2 (by rw [h, Equiv.Perm.apply_inv_self])
  -- pointwise comparison of σ' with g0
  have hσ'_gen : ∀ z, z ≠ reverseColorGerm K d1 → z ≠ reverseColorGerm K d2 →
      transitionComponentPerm H K p q τ' z = g0 z := by
    intro z hz1 hz2
    have hRz1 : reverseColorGerm K z ≠ d1 := by
      intro h
      exact hz1 (by rw [← hRR z, h])
    have hRz2 : reverseColorGerm K z ≠ d2 := by
      intro h
      exact hz2 (by rw [← hRR z, h])
    rw [hσ'app z, Equiv.swap_apply_of_ne_of_ne hRz1 hRz2, hRR]
    by_cases hc1 : z = (transitionComponentPerm H K p q τ)⁻¹ d1
    · subst hc1
      rw [Equiv.Perm.apply_inv_self, Equiv.swap_apply_left, hg0x]
    · by_cases hc2 : z = (transitionComponentPerm H K p q τ)⁻¹ d2
      · subst hc2
        rw [Equiv.Perm.apply_inv_self, Equiv.swap_apply_right, hg0y]
      · have hσz1 : transitionComponentPerm H K p q τ z ≠ d1 := by
          intro h
          exact hc1 (by rw [← h, Equiv.Perm.inv_apply_self])
        have hσz2 : transitionComponentPerm H K p q τ z ≠ d2 := by
          intro h
          exact hc2 (by rw [← h, Equiv.Perm.inv_apply_self])
        rw [Equiv.swap_apply_of_ne_of_ne hσz1 hσz2, hg0z z hc1 hc2]
  have hσ'_Rd1 : transitionComponentPerm H K p q τ' (reverseColorGerm K d1)
      = g0 (reverseColorGerm K d2) := by
    rw [hσ'app, hRR, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hηd2_ne1 hηd2_ne2,
      hg0z _ hRd2_ne_inv1 hRd2_ne_inv2]
  have hσ'_Rd2 : transitionComponentPerm H K p q τ' (reverseColorGerm K d2)
      = g0 (reverseColorGerm K d1) := by
    rw [hσ'app, hRR, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hηd1_ne1 hηd1_ne2,
      hg0z _ hRd1_ne_inv1 hRd1_ne_inv2]
  -- g0 preserves the reversed cycles
  have need1 : ∀ w, g0.SameCycle (reverseColorGerm K d1) w ↔
      (transitionComponentPerm H K p q τ).SameCycle (reverseColorGerm K d1) w := by
    apply sameCycle_iff_of_agree_on_cycle
    intro w hw
    apply hg0z
    · rintro rfl
      exact nrv1 ((hw.trans hstep1).symm)
    · rintro rfl
      exact ncR1d2 (hw.trans hstep2)
  have need2 : ∀ w, g0.SameCycle (reverseColorGerm K d2) w ↔
      (transitionComponentPerm H K p q τ).SameCycle (reverseColorGerm K d2) w := by
    apply sameCycle_iff_of_agree_on_cycle
    intro w hw
    apply hg0z
    · rintro rfl
      exact nc1R2 ((hw.trans hstep1).symm)
    · rintro rfl
      exact nrv2 ((hw.trans hstep2).symm)
  -- step 1: g0 merges the d1-cycle with the d2-cycle
  have hxy0 : ¬ (transitionComponentPerm H K p q τ).SameCycle
      ((transitionComponentPerm H K p q τ)⁻¹ d1)
      ((transitionComponentPerm H K p q τ)⁻¹ d2) := by
    intro hc
    exact nc12 ((hstep1.symm.trans hc).trans hstep2)
  have merge1 : ∀ z,
      (transitionComponentPerm H K p q τ).SameCycle
        ((transitionComponentPerm H K p q τ)⁻¹ d1) z ∨
      (transitionComponentPerm H K p q τ).SameCycle
        ((transitionComponentPerm H K p q τ)⁻¹ d2) z →
      g0.SameCycle ((transitionComponentPerm H K p q τ)⁻¹ d1) z :=
    sameCycle_of_crossover hxy0
      (by rw [hg0x, Equiv.Perm.apply_inv_self])
      (by rw [hg0y, Equiv.Perm.apply_inv_self])
      hg0z
  -- step 2: σ' merges the reversed cycles
  have hxy1 : ¬ g0.SameCycle (reverseColorGerm K d1) (reverseColorGerm K d2) := by
    rw [need1]
    exact ncR1R2
  have merge2 : ∀ z,
      g0.SameCycle (reverseColorGerm K d1) z ∨
      g0.SameCycle (reverseColorGerm K d2) z →
      (transitionComponentPerm H K p q τ').SameCycle (reverseColorGerm K d1) z :=
    sameCycle_of_crossover hxy1 hσ'_Rd1 hσ'_Rd2 hσ'_gen
  -- σ' preserves the merged forward cycle
  have keep3 : ∀ w, (transitionComponentPerm H K p q τ').SameCycle
      ((transitionComponentPerm H K p q τ)⁻¹ d1) w ↔
      g0.SameCycle ((transitionComponentPerm H K p q τ)⁻¹ d1) w := by
    apply sameCycle_iff_of_agree_on_cycle
    intro w hw
    apply hσ'_gen
    · rintro rfl
      exact nrv1 ((((need1 _).mp hw.symm).trans hstep1).symm)
    · rintro rfl
      exact nc1R2 ((((need2 _).mp hw.symm).trans hstep1).symm)
  -- the new anchor germ
  have hA' : anchorKGermP H K p q τ'
      = Equiv.swap d1 d2 (anchorKGermP H K p q τ) := by
    by_cases hv : p = v
    · subst hv
      simp only [anchorKGermP, hτ'def, hd1def, hd2def, Function.update_self,
        Equiv.symm_trans_apply, Equiv.symm_swap, swap_sigma_mk]
    · have hup : Function.update τ v ((Equiv.swap k1 k2).trans (τ v)) p = τ p :=
        Function.update_of_ne hv _ _
      simp only [anchorKGermP, hτ'def, hd1def, hd2def, hup, swap_sigma_fix K hv]
  have hane2 : anchorKGermP H K p q τ ≠ d2 := by
    intro h
    apply h2d
    rw [← h]
  -- case split on which side of the reversal carries the anchor
  rcases h1 with h1l | h1r
  · -- d1 lies in the anchor component itself
    have rel : ∀ z,
        (transitionComponentPerm H K p q τ).SameCycle d1 z ∨
        (transitionComponentPerm H K p q τ).SameCycle d2 z →
        (transitionComponentPerm H K p q τ').SameCycle
          ((transitionComponentPerm H K p q τ)⁻¹ d1) z := by
      intro z hz
      refine (keep3 z).mpr (merge1 z ?_)
      rcases hz with h | h
      · exact Or.inl (hstep1.trans h)
      · exact Or.inr (hstep2.trans h)
    by_cases hda : anchorKGermP H K p q τ = d1
    · -- crossed anchor: a' = d2, which is spliced into the merged cycle
      have ha' : anchorKGermP H K p q τ' = d2 := by
        rw [hA', hda, Equiv.swap_apply_left]
      have hsub : anchorComponent H K p q τ ⊆ anchorComponent H K p q τ' := by
        intro b hb
        rw [mem_anchorComponent_iff] at hb ⊢
        rw [ha']
        rw [hda] at hb
        exact (rel d2 (Or.inr (Equiv.Perm.SameCycle.refl _ _))).symm.trans
          (rel b (Or.inl hb))
      have hd2mem : d2 ∈ anchorComponent H K p q τ' := by
        rw [mem_anchorComponent_iff, ha']
      have hd2not : d2 ∉ anchorComponent H K p q τ := by
        rw [mem_anchorComponent_iff]
        exact h2d
      exact ⟨τ', Finset.card_lt_card
        ((Finset.ssubset_iff_of_subset hsub).mpr ⟨d2, hd2mem, hd2not⟩)⟩
    · have ha' : anchorKGermP H K p q τ' = anchorKGermP H K p q τ := by
        rw [hA', Equiv.swap_apply_of_ne_of_ne hda hane2]
      have hrelA : (transitionComponentPerm H K p q τ').SameCycle
          ((transitionComponentPerm H K p q τ)⁻¹ d1) (anchorKGermP H K p q τ) :=
        rel _ (Or.inl h1l.symm)
      have hsub : anchorComponent H K p q τ ⊆ anchorComponent H K p q τ' := by
        intro b hb
        rw [mem_anchorComponent_iff] at hb ⊢
        rw [ha']
        exact hrelA.symm.trans (rel b (Or.inl (h1l.symm.trans hb)))
      have hd2mem : d2 ∈ anchorComponent H K p q τ' := by
        rw [mem_anchorComponent_iff, ha']
        exact hrelA.symm.trans (rel d2 (Or.inr (Equiv.Perm.SameCycle.refl _ _)))
      have hd2not : d2 ∉ anchorComponent H K p q τ := by
        rw [mem_anchorComponent_iff]
        exact h2d
      exact ⟨τ', Finset.card_lt_card
        ((Finset.ssubset_iff_of_subset hsub).mpr ⟨d2, hd2mem, hd2not⟩)⟩
  · -- the reversal of d1 lies in the anchor component
    have rel2 : ∀ z,
        (transitionComponentPerm H K p q τ).SameCycle (reverseColorGerm K d1) z ∨
        (transitionComponentPerm H K p q τ).SameCycle (reverseColorGerm K d2) z →
        (transitionComponentPerm H K p q τ').SameCycle (reverseColorGerm K d1) z := by
      intro z hz
      exact merge2 z (hz.imp (fun h => (need1 z).mpr h) (fun h => (need2 z).mpr h))
    have hane1 : anchorKGermP H K p q τ ≠ d1 := by
      intro h
      exact nrv1 (h ▸ h1r)
    have ha' : anchorKGermP H K p q τ' = anchorKGermP H K p q τ := by
      rw [hA', Equiv.swap_apply_of_ne_of_ne hane1 hane2]
    have hrelA : (transitionComponentPerm H K p q τ').SameCycle
        (reverseColorGerm K d1) (anchorKGermP H K p q τ) :=
      rel2 _ (Or.inl h1r.symm)
    have hsub : anchorComponent H K p q τ ⊆ anchorComponent H K p q τ' := by
      intro b hb
      rw [mem_anchorComponent_iff] at hb ⊢
      rw [ha']
      exact hrelA.symm.trans (rel2 b (Or.inl (h1r.symm.trans hb)))
    have hnew_mem : reverseColorGerm K d2 ∈ anchorComponent H K p q τ' := by
      rw [mem_anchorComponent_iff, ha']
      exact hrelA.symm.trans
        (rel2 _ (Or.inr (Equiv.Perm.SameCycle.refl _ _)))
    have hnew_not : reverseColorGerm K d2 ∉ anchorComponent H K p q τ := by
      rw [mem_anchorComponent_iff]
      exact h2r
    exact ⟨τ', Finset.card_lt_card
      ((Finset.ssubset_iff_of_subset hsub).mpr
        ⟨reverseColorGerm K d2, hnew_mem, hnew_not⟩)⟩

set_option maxHeartbeats 1000000 in
private lemma anchorComponent_covers_K_of_maximal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected) (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    (hτmax : ∀ τ', (anchorComponent H K p q τ').card ≤
      (anchorComponent H K p q τ).card) :
    ∀ e ∈ K.edgeSet, ∃ g ∈ anchorComponent H K p q τ,
      colorGermEdge K g = e := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, heK, huncov⟩ := hcon
  revert heK huncov
  refine Sym2.inductionOn e ?_
  intro x y heK huncov
  have hxy : K.Adj x y := (SimpleGraph.mem_edgeSet K).mp heK
  have hRR : ∀ z : ColorGerm K,
      reverseColorGerm K (reverseColorGerm K z) = z :=
    reverseColorGerm_involutive K
  by_cases hmix : ∃ (w : V) (κ1 κ2 : colorGermAt K w),
      inAnchorSide H K p q τ ⟨w, κ1⟩ ∧ ¬ inAnchorSide H K p q τ ⟨w, κ2⟩
  · -- exchange: contradict maximality
    obtain ⟨w, κ1, κ2, hin, hout⟩ := hmix
    have hκ : κ1 ≠ κ2 := by
      rintro rfl
      exact hout hin
    rw [inAnchorSide, not_or] at hout
    obtain ⟨τ', hlt⟩ :=
      exists_bigger_anchorComponent_of_mixed H K hpq τ hκ hin hout.1 hout.2
    exact absurd (hτmax τ') (not_le.mpr hlt)
  · -- no mixed vertex: anchor-sidedness spreads along G, swallowing the
    -- uncovered edge — contradiction.
    push_neg at hmix
    have hclosure : ∀ u1 u2 : V, G.Adj u1 u2 →
        (∃ κ : colorGermAt K u1, inAnchorSide H K p q τ ⟨u1, κ⟩) →
        ∃ κ : colorGermAt K u2, inAnchorSide H K p q τ ⟨u2, κ⟩ := by
      rintro u1 u2 hadj ⟨κ0, hκ0⟩
      rcases (hsplit.1 u1 u2).mp hadj with hH | hK
      · -- H-edge: hop through the pairing at u1
        have hH' : u2 ∈ H.neighborSet u1 := hH
        have hdB : inAnchorSide H K p q τ
            ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩ := hmix u1 κ0 _ hκ0
        have hEd : altTransitionSystemEquiv H K p q τ
            ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩
            = ⟨u1, Sum.inl ⟨u2, hH'⟩⟩ := by
          simp [altTransitionSystemEquiv]
        have hg'2 : transitionComponentPerm H K p q τ
            (reverseColorGerm K ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩)
            = ⟨u2, (τ u2).symm (Sum.inl ⟨u1, hH.symm⟩)⟩ := by
          rw [transitionPerm_reverse_apply, hEd]
          rfl
        have hg'B : inAnchorSide H K p q τ
            (transitionComponentPerm H K p q τ
              (reverseColorGerm K ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩)) := by
          rcases hdB with hL | hR
          · refine Or.inr ?_
            rw [transitionPerm_reverse_conj, hRR]
            exact hL.trans ⟨-1, by simp⟩
          · exact Or.inl (hR.trans ⟨1, by simp⟩)
        rw [hg'2] at hg'B
        exact ⟨_, hg'B⟩
      · -- K-edge: the reversal is a germ at the far endpoint
        have hK1 : u2 ∈ K.neighborSet u1 := hK
        have hK2 : u1 ∈ K.neighborSet u2 := hK.symm
        have hdB : inAnchorSide H K p q τ ⟨u1, ⟨u2, hK1⟩⟩ := hmix u1 κ0 _ hκ0
        refine ⟨⟨u1, hK2⟩, ?_⟩
        rcases hdB with hL | hR
        · exact Or.inr hL
        · exact Or.inl hR
    have hwalk : ∀ (u w : V) (W : G.Walk u w),
        (∃ κ : colorGermAt K u, inAnchorSide H K p q τ ⟨u, κ⟩) →
        ∃ κ : colorGermAt K w, inAnchorSide H K p q τ ⟨w, κ⟩ := by
      intro u w W
      induction W with
      | nil => exact id
      | cons hadj _ ih => exact fun hu => ih (hclosure _ _ hadj hu)
    have hbase : ∃ κ : colorGermAt K p, inAnchorSide H K p q τ ⟨p, κ⟩ :=
      ⟨(τ p).symm (Sum.inr (anchorGermAtP p q)),
        Or.inl (Equiv.Perm.SameCycle.refl _ _)⟩
    obtain ⟨W⟩ := hconn.preconnected p x
    obtain ⟨κ0, hκ0⟩ := hwalk p x W hbase
    have hyx : y ∈ K.neighborSet x := hxy
    have hin_de : inAnchorSide H K p q τ ⟨x, ⟨y, hyx⟩⟩ := hmix x κ0 _ hκ0
    rcases hin_de with hA | hRA
    · exact huncov _ ((mem_anchorComponent_iff H K p q τ _).mpr hA) rfl
    · refine huncov _ ((mem_anchorComponent_iff H K p q τ _).mpr hRA) ?_
      rw [colorGermEdge_reverse]
      rfl

/-! ### Extraction of the Euler trail from a covering anchor component

Pure-data route: the anchor orbit is the sequence `D k = σ^k a`,
`k < m := minimalPeriod σ a`.  Each dart contributes its `K`-edge; between
consecutive darts the pairing crosses a real `H`-germ (tags are excluded by
the no-self-reverse fact and orbit minimality), giving the `H`-edges.  The
walk is built by recursion with an explicit `getVert` spec; the trail
property and the two coverage clauses reduce to dart-level injectivity
arguments (`hDinj`, `hnorevD`) via two edge-dichotomy helpers. -/

private lemma kdart_edge_dichotomy
    (K : SimpleGraph V) [DecidableRel K.Adj]
    {w1 w2 a1 a2 : V} (h1 : a1 ∈ K.neighborSet w1) (h2 : a2 ∈ K.neighborSet w2)
    (he : s(w1, a1) = s(w2, a2)) :
    (⟨w2, ⟨a2, h2⟩⟩ : ColorGerm K) = ⟨w1, ⟨a1, h1⟩⟩ ∨
    (⟨w2, ⟨a2, h2⟩⟩ : ColorGerm K) = reverseColorGerm K ⟨w1, ⟨a1, h1⟩⟩ := by
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma hgerm_edge_dichotomy
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V)
    {w1 w2 a1 a2 : V} (h1 : a1 ∈ H.neighborSet w1) (h2 : a2 ∈ H.neighborSet w2)
    (he : s(w1, a1) = s(w2, a2)) :
    (⟨w2, Sum.inl ⟨a2, h2⟩⟩ : AugmentedHGerm H p q) = ⟨w1, Sum.inl ⟨a1, h1⟩⟩ ∨
    (⟨w2, Sum.inl ⟨a2, h2⟩⟩ : AugmentedHGerm H p q)
      = reverseAugmentedHGerm H p q ⟨w1, Sum.inl ⟨a1, h1⟩⟩ := by
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma augGerm_inl_ne_inr
    (H : SimpleGraph V) [DecidableRel H.Adj] (p q : V)
    {w1 w2 : V} (x : colorGermAt H w1) (t : anchorGermAt p q w2) :
    (⟨w1, Sum.inl x⟩ : AugmentedHGerm H p q) ≠ ⟨w2, Sum.inr t⟩ := by
  intro h
  have h1 : w1 = w2 := congrArg Sigma.fst h
  subst h1
  simpa using h

private lemma transitionPerm_apply_eq
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q) (g : ColorGerm K) :
    transitionComponentPerm H K p q τ g
      = (altTransitionSystemEquiv H K p q τ).symm
          (reverseAugmentedHGermEquiv H p q
            (altTransitionSystemEquiv H K p q τ (reverseColorGerm K g))) :=
  rfl

/-- At a dart whose successor is not the anchor germ and whose reversal is
not the anchor germ, the transition pairing crosses a REAL `H`-germ. -/
private lemma transitionPerm_step_inl
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (p q : V) (τ : AltTransitionSystem H K p q)
    (v0 : V) (u0 : colorGermAt K v0)
    (hσa : transitionComponentPerm H K p q τ ⟨v0, u0⟩ ≠ anchorKGermP H K p q τ)
    (hRa : reverseColorGerm K (⟨v0, u0⟩ : ColorGerm K) ≠ anchorKGermP H K p q τ) :
    ∃ x : colorGermAt H (↑u0 : V),
      altTransitionSystemEquiv H K p q τ (reverseColorGerm K ⟨v0, u0⟩)
        = ⟨(↑u0 : V), Sum.inl x⟩ ∧
      transitionComponentPerm H K p q τ ⟨v0, u0⟩
        = ⟨(↑x : V), (τ ↑x).symm (Sum.inl ⟨↑u0, x.2.symm⟩)⟩ := by
  classical
  rcases hval : (τ (↑u0 : V)) ⟨v0, u0.2.symm⟩ with x | t
  · have h0 : altTransitionSystemEquiv H K p q τ (reverseColorGerm K ⟨v0, u0⟩)
        = ⟨(↑u0 : V), Sum.inl x⟩ := by
      show (⟨(↑u0 : V), (τ (↑u0 : V)) ⟨v0, u0.2.symm⟩⟩ : AugmentedHGerm H p q) = _
      rw [hval]
    refine ⟨x, h0, ?_⟩
    rw [transitionPerm_apply_eq, h0]
    rfl
  · exfalso
    rcases t with ⟨tag, htag⟩
    cases tag with
    | atP =>
      have hu : (↑u0 : V) = p :=
        vertex_eq_p_of_anchorAtP p q _ ⟨.atP, htag⟩ rfl
      apply hRa
      apply Equiv.injective (altTransitionSystemEquiv H K p q τ)
      rw [altTransitionSystemEquiv_anchorKGermP]
      show (⟨(↑u0 : V), (τ (↑u0 : V)) ⟨v0, u0.2.symm⟩⟩ : AugmentedHGerm H p q) = _
      rw [hval]
      subst hu
      rfl
    | atQ =>
      apply hσa
      rw [transitionPerm_apply_eq]
      have h0 : altTransitionSystemEquiv H K p q τ (reverseColorGerm K ⟨v0, u0⟩)
          = ⟨(↑u0 : V), Sum.inr ⟨.atQ, htag⟩⟩ := by
        show (⟨(↑u0 : V), (τ (↑u0 : V)) ⟨v0, u0.2.symm⟩⟩ : AugmentedHGerm H p q) = _
        rw [hval]
      rw [h0]
      rfl

set_option maxHeartbeats 1600000 in
private lemma walk_of_anchorComponent_covers_K
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q) (τ : AltTransitionSystem H K p q)
    (hcover : ∀ e ∈ K.edgeSet, ∃ g ∈ anchorComponent H K p q τ,
      colorGermEdge K g = e) :
    ∃ w : G.Walk p q,
      w.IsTrail ∧ AlternatesKH H K w ∧
      (∀ e ∈ K.edgeSet, e ∈ w.edges) ∧
      (∀ e ∈ H.edgeSet, e ∈ w.edges) := by
  classical
  -- ### the dart iterates
  set D : ℕ → ColorGerm K :=
    fun k => ((transitionComponentPerm H K p q τ) ^ k) (anchorKGermP H K p q τ)
    with hDdef
  set m := Function.minimalPeriod (⇑(transitionComponentPerm H K p q τ))
    (anchorKGermP H K p q τ) with hmdef
  have hmem : anchorKGermP H K p q τ ∈
      Function.periodicPts (⇑(transitionComponentPerm H K p q τ)) := by
    refine Function.mem_periodicPts.mpr
      ⟨orderOf (transitionComponentPerm H K p q τ),
        orderOf_pos (transitionComponentPerm H K p q τ), ?_⟩
    show (⇑(transitionComponentPerm H K p q τ))^[orderOf _] _ = _
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hm1 : 0 < m := Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hD0 : D 0 = anchorKGermP H K p q τ := by
    simp only [hDdef, pow_zero, Equiv.Perm.one_apply]
  have hDm : D m = anchorKGermP H K p q τ := by
    have h := Function.iterate_minimalPeriod
      (f := ⇑(transitionComponentPerm H K p q τ)) (x := anchorKGermP H K p q τ)
    rw [← hmdef] at h
    simp only [hDdef]
    rw [Equiv.Perm.coe_pow]
    exact h
  have hDne : ∀ i, 0 < i → i < m → D i ≠ D 0 := by
    intro i hi0 him hcon
    have hper : Function.IsPeriodicPt
        (⇑(transitionComponentPerm H K p q τ)) i (anchorKGermP H K p q τ) := by
      show (⇑(transitionComponentPerm H K p q τ))^[i] _ = _
      rw [← Equiv.Perm.coe_pow]
      rw [hD0] at hcon
      exact hcon
    have hle := hper.minimalPeriod_le hi0
    rw [← hmdef] at hle
    omega
  have hDinj : ∀ i j, i < m → j < m → D i = D j → i = j := by
    have core : ∀ i j, i < j → j < m → D i ≠ D j := by
      intro i j hij hjm hcon
      have h1 : D j = ((transitionComponentPerm H K p q τ) ^ i) (D (j - i)) := by
        simp only [hDdef]
        rw [← Equiv.Perm.mul_apply, ← pow_add, show i + (j - i) = j by omega]
      have h2 : D i = ((transitionComponentPerm H K p q τ) ^ i) (D 0) := by
        rw [hD0]
      have h3 : ((transitionComponentPerm H K p q τ) ^ i) (D 0)
          = ((transitionComponentPerm H K p q τ) ^ i) (D (j - i)) := by
        rw [← h2, hcon, h1]
      exact hDne (j - i) (by omega) (by omega) (Equiv.injective _ h3).symm
    intro i j him hjm heq
    rcases Nat.lt_trichotomy i j with hij | rfl | hji
    · exact absurd heq (core i j hij hjm)
    · rfl
    · exact absurd heq.symm (core j i hji him)
  have hsucc : ∀ k, transitionComponentPerm H K p q τ (D k) = D (k + 1) := by
    intro k
    simp only [hDdef]
    rw [pow_succ', Equiv.Perm.mul_apply]
  have hRR : ∀ z : ColorGerm K,
      reverseColorGerm K (reverseColorGerm K z) = z :=
    reverseColorGerm_involutive K
  have hRfst : ∀ g : ColorGerm K, (reverseColorGerm K g).1 = g.2.1 := by
    rintro ⟨v, u⟩
    rfl
  have hend : (D (m - 1)).2.1 = q := by
    have hlastD : transitionComponentPerm H K p q τ (D (m - 1))
        = anchorKGermP H K p q τ := by
      rw [hsucc, show m - 1 + 1 = m by omega, hDm]
    have h := transitionComponentPerm_eq_anchorP_ends_q H K p q τ (D (m - 1)) hlastD
    rwa [hRfst] at h
  have hDsc : ∀ k, (transitionComponentPerm H K p q τ).SameCycle
      (anchorKGermP H K p q τ) (D k) := by
    intro k
    exact ⟨(k : ℤ), by simp only [hDdef]; rw [zpow_natCast]⟩
  have hDsurj : ∀ g, (transitionComponentPerm H K p q τ).SameCycle
      (anchorKGermP H K p q τ) g → ∃ k, k < m ∧ g = D k := by
    intro g hg
    obtain ⟨n, hn⟩ := hg.exists_nat_pow_eq
    refine ⟨n % m, Nat.mod_lt _ hm1, ?_⟩
    have h := Function.iterate_mod_minimalPeriod_eq
      (f := ⇑(transitionComponentPerm H K p q τ)) (x := anchorKGermP H K p q τ)
      (n := n)
    rw [← hmdef] at h
    simp only [hDdef]
    rw [← hn]
    have h' : ((transitionComponentPerm H K p q τ) ^ (n % m))
        (anchorKGermP H K p q τ)
        = ((transitionComponentPerm H K p q τ) ^ n) (anchorKGermP H K p q τ) := by
      rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
      exact h
    exact h'.symm
  have hnorevD : ∀ i j, reverseColorGerm K (D i) ≠ D j := by
    intro i j hcon
    have h1 : (transitionComponentPerm H K p q τ).SameCycle
        (anchorKGermP H K p q τ) (reverseColorGerm K (D i)) := by
      rw [hcon]
      exact hDsc j
    exact not_sameCycle_reverse H K hpq τ (D i) (((hDsc i).symm).trans h1)
  -- ### the K- and H-adjacency data along the orbit
  have hfstD : ∀ k, K.Adj ((D k).1) ((D k).2.1) := by
    intro k
    exact (SimpleGraph.mem_neighborSet K _ _).mp (D k).2.2
  have hDstep : ∀ k, k + 1 < m → ∃ x : colorGermAt H ((D k).2.1),
      altTransitionSystemEquiv H K p q τ (reverseColorGerm K (D k))
        = ⟨((D k).2.1 : V), Sum.inl x⟩ ∧
      D (k + 1) = ⟨(↑x : V), (τ ↑x).symm (Sum.inl ⟨(D k).2.1, x.2.symm⟩)⟩ := by
    intro k hk
    have hσne : transitionComponentPerm H K p q τ (D k) ≠ anchorKGermP H K p q τ := by
      rw [hsucc, ← hD0]
      exact hDne (k + 1) (by omega) hk
    have hRne : reverseColorGerm K (D k) ≠ anchorKGermP H K p q τ := by
      rw [← hD0]
      exact hnorevD k 0
    obtain ⟨x, hx1, hx2⟩ :=
      transitionPerm_step_inl H K p q τ (D k).1 (D k).2 hσne hRne
    refine ⟨x, hx1, ?_⟩
    rw [← hsucc]
    exact hx2
  have hDadjH : ∀ k, k + 1 < m → H.Adj ((D k).2.1) ((D (k + 1)).1) := by
    intro k hk
    obtain ⟨x, _, hx2⟩ := hDstep k hk
    have hfst : (D (k + 1)).1 = (↑x : V) := by rw [hx2]
    rw [hfst]
    exact (SimpleGraph.mem_neighborSet H _ _).mp x.2
  -- ### the vertex profile and the walk
  set VX : ℕ → V :=
    fun j => if j % 2 = 0 then (D (j / 2)).1 else (D (j / 2)).2.1 with hVXdef
  have hVXe : ∀ t, VX (2 * t) = (D t).1 := by
    intro t
    simp only [hVXdef]
    rw [if_pos (show (2 * t) % 2 = 0 by omega), show 2 * t / 2 = t by omega]
  have hVXo : ∀ t, VX (2 * t + 1) = (D t).2.1 := by
    intro t
    simp only [hVXdef]
    rw [if_neg (show ¬ (2 * t + 1) % 2 = 0 by omega),
      show (2 * t + 1) / 2 = t by omega]
  have build : ∀ n k, k < m → m - k = n + 1 →
      ∃ w : G.Walk ((D k).1) q, w.length = 2 * (m - k) - 1 ∧
        ∀ i, i ≤ w.length → w.getVert i = VX (2 * k + i) := by
    intro n
    induction n with
    | zero =>
      intro k hkm hmk
      have hk1 : k = m - 1 := by omega
      have hendk : (D k).2.1 = q := by rw [hk1]; exact hend
      have hadjG : G.Adj ((D k).1) q := by
        rw [← hendk]
        exact hsplit.2.2.2.1 (hfstD k)
      refine ⟨SimpleGraph.Walk.cons hadjG SimpleGraph.Walk.nil, by simp; omega, ?_⟩
      intro i hi
      have hlen : (SimpleGraph.Walk.cons hadjG SimpleGraph.Walk.nil).length = 1 := by
        simp
      rw [hlen] at hi
      rcases i with _ | i
      · rw [SimpleGraph.Walk.getVert_zero, Nat.add_zero, hVXe]
      · rcases i with _ | i
        · rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_nil,
            hVXo, hendk]
        · omega
    | succ n ih =>
      intro k hkm hmk
      have hk1 : k + 1 < m := by omega
      obtain ⟨w', hlen', hget'⟩ := ih (k + 1) hk1 (by omega)
      have hadjG1 : G.Adj ((D k).1) ((D k).2.1) := hsplit.2.2.2.1 (hfstD k)
      have hadjG2 : G.Adj ((D k).2.1) ((D (k + 1)).1) :=
        hsplit.2.2.1 (hDadjH k hk1)
      refine ⟨SimpleGraph.Walk.cons hadjG1 (SimpleGraph.Walk.cons hadjG2 w'),
        ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_cons, hlen']
        omega
      · intro i hi
        rcases i with _ | i
        · rw [SimpleGraph.Walk.getVert_zero, Nat.add_zero, hVXe]
        · rcases i with _ | i
          · rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero,
              hVXo]
          · have hi' : i ≤ w'.length := by
              simp only [SimpleGraph.Walk.length_cons] at hi
              omega
            rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_cons_succ,
              hget' i hi', show 2 * (k + 1) + i = 2 * k + (i + 1 + 1) by omega]
  obtain ⟨w0, hlen0, hget0⟩ := build (m - 1) 0 hm1 (by omega)
  have hD0p : (D 0).1 = p := by
    rw [hD0]
    rfl
  -- ### the walk and its index toolkit
  have hWlen : (w0.copy hD0p rfl).length = 2 * m - 1 := by
    rw [SimpleGraph.Walk.length_copy, hlen0]
    omega
  have hWget : ∀ i, i ≤ 2 * m - 1 → (w0.copy hD0p rfl).getVert i = VX i := by
    intro i hi
    rw [SimpleGraph.Walk.getVert_copy]
    have h := hget0 i (by omega)
    rw [h, show 2 * 0 + i = i by omega]
  have hedgelen : (w0.copy hD0p rfl).edges.length = 2 * m - 1 := by
    rw [SimpleGraph.Walk.length_edges, hWlen]
  have hWedge : ∀ i, (hi : i < 2 * m - 1) →
      (w0.copy hD0p rfl).edges[i]'(by rw [hedgelen]; exact hi)
        = s(VX i, VX (i + 1)) := by
    intro i hi
    have hi' : i < (w0.copy hD0p rfl).darts.length := by
      rw [SimpleGraph.Walk.length_darts, hWlen]
      exact hi
    have h1 : (w0.copy hD0p rfl).edges[i]'(by rw [hedgelen]; exact hi)
        = s((w0.copy hD0p rfl).getVert i, (w0.copy hD0p rfl).getVert (i + 1)) := by
      show ((w0.copy hD0p rfl).darts.map SimpleGraph.Dart.edge)[i]'_ = _
      rw [List.getElem_map]
      rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
      rfl
    rw [h1, hWget i (by omega), hWget (i + 1) (by omega)]
  refine ⟨w0.copy hD0p rfl, ?_, ?_, ?_, ?_⟩
  · -- IsTrail : the interleaved edge list has no duplicates
    refine ⟨?_⟩
    show List.Pairwise (· ≠ ·) (w0.copy hD0p rfl).edges
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [hedgelen] at hi hj
    rw [hWedge i hi, hWedge j hj]
    intro hcon
    rcases Nat.even_or_odd i with ⟨s, hs⟩ | ⟨s, hs⟩ <;>
      rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · -- K-edge vs K-edge
      subst hs; subst ht
      rw [show s + s = 2 * s by omega] at hcon hij hi
      rw [show t + t = 2 * t by omega] at hcon hij hj
      rw [hVXe, hVXo, hVXe, hVXo] at hcon
      rcases kdart_edge_dichotomy K ((D s).2.2) ((D t).2.2) hcon with h | h
      · have : t = s := hDinj t s (by omega) (by omega) h
        omega
      · exact hnorevD s t h.symm
    · -- K-edge vs H-edge
      subst hs; subst ht
      rw [show s + s = 2 * s by omega] at hcon hij hi
      rw [hVXe, hVXo, hVXo, show 2 * t + 1 + 1 = 2 * (t + 1) by omega, hVXe]
        at hcon
      have hKmem : s((D t).2.1, (D (t + 1)).1) ∈ K.edgeSet := by
        rw [← hcon]
        exact colorGermEdge_mem K (D s)
      exact hsplit.2.1 _ _ (hDadjH t (by omega))
        ((SimpleGraph.mem_edgeSet K).mp hKmem)
    · -- H-edge vs K-edge
      subst hs; subst ht
      rw [show t + t = 2 * t by omega] at hcon hij hj
      rw [hVXo, show 2 * s + 1 + 1 = 2 * (s + 1) by omega, hVXe, hVXe, hVXo]
        at hcon
      have hKmem : s((D s).2.1, (D (s + 1)).1) ∈ K.edgeSet := by
        rw [hcon]
        exact colorGermEdge_mem K (D t)
      exact hsplit.2.1 _ _ (hDadjH s (by omega))
        ((SimpleGraph.mem_edgeSet K).mp hKmem)
    · -- H-edge vs H-edge
      subst hs; subst ht
      rw [hVXo, show 2 * s + 1 + 1 = 2 * (s + 1) by omega, hVXe,
        hVXo, show 2 * t + 1 + 1 = 2 * (t + 1) by omega, hVXe] at hcon
      have hsm : s + 1 < m := by omega
      have htm : t + 1 < m := by omega
      obtain ⟨xs, hxs1, hxs2⟩ := hDstep s hsm
      obtain ⟨xt, hxt1, hxt2⟩ := hDstep t htm
      have hfs : (D (s + 1)).1 = (↑xs : V) := by rw [hxs2]
      have hft : (D (t + 1)).1 = (↑xt : V) := by rw [hxt2]
      rw [hfs, hft] at hcon
      rcases hgerm_edge_dichotomy H p q xs.2 xt.2 hcon with h | h
      · -- same H-germ : the darts coincide
        have hEE : altTransitionSystemEquiv H K p q τ
            (reverseColorGerm K (D t))
            = altTransitionSystemEquiv H K p q τ (reverseColorGerm K (D s)) := by
          rw [hxt1, hxs1]
          exact h
        have hRt := Equiv.injective _ hEE
        have hDD := congrArg (reverseColorGerm K) hRt
        rw [hRR, hRR] at hDD
        have : t = s := hDinj t s (by omega) (by omega) hDD
        omega
      · -- reversed H-germ : the successor of D t is the reversal of D s
        have hEE : altTransitionSystemEquiv H K p q τ
            (reverseColorGerm K (D t))
            = reverseAugmentedHGerm H p q
                (altTransitionSystemEquiv H K p q τ (reverseColorGerm K (D s))) := by
          rw [hxt1, hxs1]
          exact h
        have hσt : transitionComponentPerm H K p q τ (D t)
            = reverseColorGerm K (D s) := by
          rw [transitionPerm_apply_eq, hEE]
          rw [show reverseAugmentedHGermEquiv H p q
                (reverseAugmentedHGerm H p q
                  (altTransitionSystemEquiv H K p q τ (reverseColorGerm K (D s))))
              = altTransitionSystemEquiv H K p q τ (reverseColorGerm K (D s)) from
            reverseAugmentedHGerm_involutive H p q _]
          exact Equiv.symm_apply_apply _ _
        rw [hsucc] at hσt
        exact hnorevD s (t + 1) hσt.symm
  · -- AlternatesKH : even steps in K, odd steps in H
    intro i hilen
    rw [hWlen] at hilen
    constructor
    · intro hpar
      obtain ⟨t, rfl⟩ : ∃ t, i = 2 * t := ⟨i / 2, by omega⟩
      rw [hWget _ (by omega), hWget _ (by omega), hVXe, hVXo]
      exact hfstD t
    · intro hpar
      obtain ⟨t, rfl⟩ : ∃ t, i = 2 * t + 1 := ⟨i / 2, by omega⟩
      rw [hWget _ (by omega), hWget _ (by omega), hVXo,
        show 2 * t + 1 + 1 = 2 * (t + 1) by omega, hVXe]
      exact hDadjH t (by omega)
  · -- K-coverage
    intro e he
    obtain ⟨g, hgmem, hge⟩ := hcover e he
    rw [mem_anchorComponent_iff] at hgmem
    obtain ⟨k, hkm, hg⟩ := hDsurj g hgmem
    subst hg
    rw [List.mem_iff_getElem]
    refine ⟨2 * k, by rw [hedgelen]; omega, ?_⟩
    rw [hWedge (2 * k) (by omega), hVXe, hVXo]
    exact hge
  · -- H-coverage
    intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro w w' he
    have hadj' : w' ∈ H.neighborSet w := (SimpleGraph.mem_edgeSet H).mp he
    have hcE : altTransitionSystemEquiv H K p q τ
        (⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩ : ColorGerm K)
        = ⟨w, Sum.inl ⟨w', hadj'⟩⟩ := by
      show (⟨w, (τ w) ((τ w).symm (Sum.inl ⟨w', hadj'⟩))⟩ : AugmentedHGerm H p q) = _
      rw [Equiv.apply_symm_apply]
    obtain ⟨g, hgmem, hge⟩ := hcover
      (colorGermEdge K ⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩)
      (colorGermEdge_mem K _)
    rw [mem_anchorComponent_iff] at hgmem
    obtain ⟨k, hkm, hg⟩ := hDsurj g hgmem
    subst hg
    rcases kdart_edge_dichotomy K
        ((⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩ : ColorGerm K).2.2)
        ((D k).2.2) hge.symm with h | h
    · -- D k IS the germ dart : use the PREVIOUS step's H-edge
      have h' : D k = (⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩ : ColorGerm K) := h
      have hk0 : k ≠ 0 := by
        intro hk0
        subst hk0
        have hEa := altTransitionSystemEquiv_anchorKGermP H K p q τ
        rw [← hD0, h'] at hEa
        rw [hcE] at hEa
        exact augGerm_inl_ne_inr H p q ⟨w', hadj'⟩ (anchorGermAtP p q) hEa
      have hkstep : (k - 1) + 1 < m := by omega
      obtain ⟨x, hx1, hx2⟩ := hDstep (k - 1) hkstep
      rw [show k - 1 + 1 = k by omega] at hx2
      have hEDk : altTransitionSystemEquiv H K p q τ (D k)
          = ⟨(↑x : V), Sum.inl ⟨(D (k - 1)).2.1, x.2.symm⟩⟩ := by
        rw [hx2]
        show (⟨(↑x : V), (τ ↑x) ((τ ↑x).symm
          (Sum.inl ⟨(D (k - 1)).2.1, x.2.symm⟩))⟩ : AugmentedHGerm H p q) = _
        rw [Equiv.apply_symm_apply]
      have hEDk' : altTransitionSystemEquiv H K p q τ (D k)
          = ⟨w, Sum.inl ⟨w', hadj'⟩⟩ := by
        rw [h', hcE]
      have hxw : (↑x : V) = w := by
        have h2 := hEDk.symm.trans hEDk'
        exact congrArg Sigma.fst h2
      subst hxw
      have hsnd : (⟨(D (k - 1)).2.1, x.2.symm⟩ : colorGermAt H (↑x : V))
          = ⟨w', hadj'⟩ := by
        have h2 := hEDk.symm.trans hEDk'
        simpa using h2
      have hw' : (D (k - 1)).2.1 = w' := congrArg Subtype.val hsnd
      rw [List.mem_iff_getElem]
      refine ⟨2 * (k - 1) + 1, by rw [hedgelen]; omega, ?_⟩
      rw [hWedge (2 * (k - 1) + 1) (by omega), hVXo,
        show 2 * (k - 1) + 1 + 1 = 2 * (k - 1 + 1) by omega, hVXe,
        show k - 1 + 1 = k by omega]
      have hfk : (D k).1 = (↑x : V) := by rw [hx2]
      rw [hfk, ← hw']
      exact Sym2.eq_swap
    · -- D k is the REVERSED germ dart : use this step's H-edge
      have h' : D k = reverseColorGerm K
          (⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩ : ColorGerm K) := h
      have hRDk : reverseColorGerm K (D k)
          = ⟨w, (τ w).symm (Sum.inl ⟨w', hadj'⟩)⟩ := by
        have h2 := congrArg (reverseColorGerm K) h'
        rwa [hRR] at h2
      have hkm1 : k + 1 < m := by
        rcases Nat.lt_or_ge (k + 1) m with hlt | hge
        · exact hlt
        · exfalso
          have hkm' : k + 1 = m := by omega
          have hσk : transitionComponentPerm H K p q τ (D k)
              = anchorKGermP H K p q τ := by
            rw [hsucc, hkm', hDm]
          have hEσ : altTransitionSystemEquiv H K p q τ
              (transitionComponentPerm H K p q τ (D k))
              = ⟨p, Sum.inr (anchorGermAtP p q)⟩ := by
            rw [hσk]
            exact altTransitionSystemEquiv_anchorKGermP H K p q τ
          rw [transitionComponentPerm_pairing_step, hRDk, hcE] at hEσ
          exact augGerm_inl_ne_inr H p q ⟨w, hadj'.symm⟩
            (anchorGermAtP p q) (by rw [← hEσ]; rfl)
      obtain ⟨x, hx1, hx2⟩ := hDstep k hkm1
      have hEeq : (⟨((D k).2.1 : V), Sum.inl x⟩ : AugmentedHGerm H p q)
          = ⟨w, Sum.inl ⟨w', hadj'⟩⟩ := by
        rw [← hx1, hRDk, hcE]
      have hfw : (D k).2.1 = w := congrArg Sigma.fst hEeq
      subst hfw
      have hsnd : x = (⟨w', hadj'⟩ : colorGermAt H ((D k).2.1)) := by
        simpa using hEeq
      rw [List.mem_iff_getElem]
      refine ⟨2 * k + 1, by rw [hedgelen]; omega, ?_⟩
      rw [hWedge (2 * k + 1) (by omega), hVXo,
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hVXe]
      have hfk1 : (D (k + 1)).1 = (↑x : V) := by rw [hx2]
      have hxv : (↑x : V) = w' := congrArg Subtype.val hsnd
      rw [hfk1, hxv]

/-- PIN EULER-A (fresh-strike round 19; Kotzig 1968 / Fleischner transition
systems — the alternating-Euler-trail lemma).  In the blocked world's degree
profile — `G` connected, `K` 2-regular, `H` 2-regular except at the two
anchors where it has degree 1 — there is a `p → q` trail alternating
`K,H,K,…,K` that uses EVERY edge of `G`.

Proof plan (LENS-CYCLESPACE §3, transition-merge): pair `K`-germs with
`H`-germs at every vertex (2+2 perfect at deg-4; at `p, q` pair the single
`H`-germ with one `K`-germ, one loose `K`-germ each); following pairings
partitions `E` into one open alternating `p`–`q` trail + alternating closed
trails; if ≥ 2 trails, connectivity gives two trails sharing a vertex and a
pairing swap merges them (splitting would need both passes on the SAME
trail); induct on trail count.  Hierholzer variant riding banked machinery:
`alt_walk_termination` (A1) + unused-germ balance (A2) + balanced-leftover
alternating-circuit decomposition (A3) + phase-consistent splice (A4).
Deliberately MINIMAL hypotheses (no `hmin`, no triangle `S`, no `hvar`, no
`hPodd`): the three lenses agree none are needed. -/
lemma exists_alternating_euler_trail
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2) :
    ∃ w : G.Walk p q, w.IsTrail ∧ AlternatesKH H K w ∧
      ∀ e ∈ G.edgeSet, e ∈ w.edges := by
  classical
  have hsystems : Nonempty (AltTransitionSystem H K p q) :=
    exists_altTransitionSystem H K hpq hpH hqH hHfull hK2
  obtain ⟨τ, hτmax⟩ :=
    exists_anchorComponent_maximizer H K p q hsystems
  have hcomponent_covers_K :
      ∀ e ∈ K.edgeSet, ∃ g ∈ anchorComponent H K p q τ,
        colorGermEdge K g = e := by
    exact anchorComponent_covers_K_of_maximal G H K hconn hsplit hpq τ hτmax
  have horbit_to_walk :
      ∃ w : G.Walk p q,
        w.IsTrail ∧ AlternatesKH H K w ∧
        (∀ e ∈ K.edgeSet, e ∈ w.edges) ∧
        (∀ e ∈ H.edgeSet, e ∈ w.edges) := by
    exact walk_of_anchorComponent_covers_K G H K hsplit hpq τ hcomponent_covers_K
  obtain ⟨w, htrail, halt, hKedges, hHedges⟩ := horbit_to_walk
  have hall : ∀ e ∈ G.edgeSet, e ∈ w.edges := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hGuv : G.Adj u v := by
          simpa only [SimpleGraph.mem_edgeSet] using he
        rcases (hsplit.1 u v).mp hGuv with hHuv | hKuv
        · exact hHedges s(u, v) (by
            simpa only [SimpleGraph.mem_edgeSet] using hHuv)
        · exact hKedges s(u, v) (by
            simpa only [SimpleGraph.mem_edgeSet] using hKuv)
  exact ⟨w, htrail, halt, hall⟩

/-- EULER-B (fresh-strike round 19; PROVED).  An all-edges alternating trail
is a maximal alternating walk: the maximality clause quantifies over unused
demanded-half edges at the terminus, and an Eulerian trail leaves none —
every `H`- or `K`-edge is a `G`-edge (split contract) and hence used. -/
lemma isMaximalAltWalk_of_all_edges
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p x : V} (w : G.Walk p x)
    (htrail : w.IsTrail) (halt : AlternatesKH H K w)
    (hall : ∀ e ∈ G.edgeSet, e ∈ w.edges) :
    IsMaximalAltWalk G H K w := by
  refine ⟨htrail, halt, fun y => ⟨fun _ hKxy => hall s(x, y) ?_, fun _ hHxy => hall s(x, y) ?_⟩⟩
  · simpa only [SimpleGraph.mem_edgeSet] using hsplit.2.2.2.1 hKxy
  · simpa only [SimpleGraph.mem_edgeSet] using hsplit.2.2.1 hHxy

/-- EULER-C (fresh-strike round 19; PROVED).  Every odd cycle support carries
an edge of its own graph with both endpoints inside the support — the
witnessing cycle's first edge.  Composed with an all-edges trail this yields
`WalkCuts w X` for every odd support of either half. -/
lemma oddCycleSupport_has_internal_edge
    (M : SimpleGraph V)
    {X : Finset V} (hX : X ∈ oddCycleSupports M) :
    ∃ e ∈ M.edgeSet, ∀ v ∈ e, v ∈ X := by
  unfold oddCycleSupports at hX
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
  obtain ⟨x, c, hcyc, hodd, hsupp⟩ := hX
  have hnil : ¬ c.Nil := by
    intro h
    have h0 : c.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp h
    obtain ⟨k, hk⟩ := hodd
    omega
  have he : s(x, c.snd) ∈ c.edges := SimpleGraph.Walk.mk_start_snd_mem_edges hnil
  refine ⟨s(x, c.snd), c.edges_subset_edgeSet he, ?_⟩
  intro v hv
  rw [← hsupp]
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact List.mem_toFinset.mpr c.start_mem_support
  · exact List.mem_toFinset.mpr (c.snd_mem_support_of_mem_edges he)

/-! ### Balanced cocircuits: alternating-trail realization (Fable SUM-PIN lane, 2026-07-13)

The transition machinery above uses its degree-(2,2,1) hypotheses ONLY in the
local pairing-cardinality lemma (`card_augmentedHGermAt_eq_two` /
`exists_localTransition`); germ BALANCE is the true hypothesis.  Applied to
the `deleteEdges` triple `(G∖F, H∖F, K∖F)` for a germ-balanced `F`, it yields
an all-edges alternating `p→q` trail of `G∖F` — with toggle set exactly
`E∖F`, and maximal as a walk of `(G,H,K)` when `q`'s three germs avoid `F`.
HISTORY: built to reduce the walk-level SUM pin to a walk-free cocircuit pin
(TRIAGE-W12-15.md SUM-PIN addendum); the same night BOTH the walk pin and
the cocircuit pin were FALSIFIED outright (fresh-strike/LENS-B3-SURGERY.md,
fresh-strike/LENS-B3-INVARIANT.md — the falsified statements are kept below
as commented records).  The machinery itself is TRUE, kernel-checked, and is
the realization arm of repair route B (FREE-STOP): dropping the `q`-germ
marks, `maximal_walk_of_balanced_cocircuit` constructs exactly the free-stop
trail family (the balance hypothesis at `q` already encodes the odd-length
arrival). -/

private lemma getVert_transfer
    {G G' : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (h : ∀ e ∈ w.edges, e ∈ G'.edgeSet) (i : ℕ) :
    (w.transfer G' h).getVert i = w.getVert i := by
  induction w generalizing i with
  | nil => rfl
  | cons hadj w ih =>
      cases i with
      | zero => rfl
      | succ n =>
          simp only [SimpleGraph.Walk.transfer, SimpleGraph.Walk.getVert_cons_succ]
          exact ih _ n

private lemma exists_altTransitionSystem_balanced
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    {p q : V} (hpq : p ≠ q)
    (hbal : ∀ v, v ≠ p → v ≠ q → K.degree v = H.degree v)
    (hbalp : K.degree p = H.degree p + 1)
    (hbalq : K.degree q = H.degree q + 1) :
    Nonempty (AltTransitionSystem H K p q) := by
  classical
  have hcard : ∀ v, Fintype.card (colorGermAt K v)
      = Fintype.card (augmentedHGermAt H p q v) := by
    intro v
    rw [card_colorGermAt, Fintype.card_sum, card_colorGermAt,
      card_anchorGermAt p q v hpq]
    by_cases hvp : v = p
    · subst hvp
      rw [if_pos (Or.inl rfl), hbalp]
    · by_cases hvq : v = q
      · subst hvq
        rw [if_pos (Or.inr rfl), hbalq]
      · rw [if_neg (by simp [hvp, hvq]), hbal v hvp hvq, Nat.add_zero]
  exact ⟨fun v => (Fintype.card_eq.mp (hcard v)).some⟩

set_option maxHeartbeats 1000000 in
private lemma anchorComponent_covers_K_of_maximal_pre
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (hpre : ∀ x y, K.Adj x y → G.Reachable p x)
    (τ : AltTransitionSystem H K p q)
    (hτmax : ∀ τ', (anchorComponent H K p q τ').card ≤
      (anchorComponent H K p q τ).card) :
    ∀ e ∈ K.edgeSet, ∃ g ∈ anchorComponent H K p q τ,
      colorGermEdge K g = e := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, heK, huncov⟩ := hcon
  revert heK huncov
  refine Sym2.inductionOn e ?_
  intro x y heK huncov
  have hxy : K.Adj x y := (SimpleGraph.mem_edgeSet K).mp heK
  have hRR : ∀ z : ColorGerm K,
      reverseColorGerm K (reverseColorGerm K z) = z :=
    reverseColorGerm_involutive K
  by_cases hmix : ∃ (w : V) (κ1 κ2 : colorGermAt K w),
      inAnchorSide H K p q τ ⟨w, κ1⟩ ∧ ¬ inAnchorSide H K p q τ ⟨w, κ2⟩
  · -- exchange: contradict maximality
    obtain ⟨w, κ1, κ2, hin, hout⟩ := hmix
    have hκ : κ1 ≠ κ2 := by
      rintro rfl
      exact hout hin
    rw [inAnchorSide, not_or] at hout
    obtain ⟨τ', hlt⟩ :=
      exists_bigger_anchorComponent_of_mixed H K hpq τ hκ hin hout.1 hout.2
    exact absurd (hτmax τ') (not_le.mpr hlt)
  · -- no mixed vertex: anchor-sidedness spreads along G, swallowing the
    -- uncovered edge — contradiction.
    push_neg at hmix
    have hclosure : ∀ u1 u2 : V, G.Adj u1 u2 →
        (∃ κ : colorGermAt K u1, inAnchorSide H K p q τ ⟨u1, κ⟩) →
        ∃ κ : colorGermAt K u2, inAnchorSide H K p q τ ⟨u2, κ⟩ := by
      rintro u1 u2 hadj ⟨κ0, hκ0⟩
      rcases (hsplit.1 u1 u2).mp hadj with hH | hK
      · -- H-edge: hop through the pairing at u1
        have hH' : u2 ∈ H.neighborSet u1 := hH
        have hdB : inAnchorSide H K p q τ
            ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩ := hmix u1 κ0 _ hκ0
        have hEd : altTransitionSystemEquiv H K p q τ
            ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩
            = ⟨u1, Sum.inl ⟨u2, hH'⟩⟩ := by
          simp [altTransitionSystemEquiv]
        have hg'2 : transitionComponentPerm H K p q τ
            (reverseColorGerm K ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩)
            = ⟨u2, (τ u2).symm (Sum.inl ⟨u1, hH.symm⟩)⟩ := by
          rw [transitionPerm_reverse_apply, hEd]
          rfl
        have hg'B : inAnchorSide H K p q τ
            (transitionComponentPerm H K p q τ
              (reverseColorGerm K ⟨u1, (τ u1).symm (Sum.inl ⟨u2, hH'⟩)⟩)) := by
          rcases hdB with hL | hR
          · refine Or.inr ?_
            rw [transitionPerm_reverse_conj, hRR]
            exact hL.trans ⟨-1, by simp⟩
          · exact Or.inl (hR.trans ⟨1, by simp⟩)
        rw [hg'2] at hg'B
        exact ⟨_, hg'B⟩
      · -- K-edge: the reversal is a germ at the far endpoint
        have hK1 : u2 ∈ K.neighborSet u1 := hK
        have hK2 : u1 ∈ K.neighborSet u2 := hK.symm
        have hdB : inAnchorSide H K p q τ ⟨u1, ⟨u2, hK1⟩⟩ := hmix u1 κ0 _ hκ0
        refine ⟨⟨u1, hK2⟩, ?_⟩
        rcases hdB with hL | hR
        · exact Or.inr hL
        · exact Or.inl hR
    have hwalk : ∀ (u w : V) (W : G.Walk u w),
        (∃ κ : colorGermAt K u, inAnchorSide H K p q τ ⟨u, κ⟩) →
        ∃ κ : colorGermAt K w, inAnchorSide H K p q τ ⟨w, κ⟩ := by
      intro u w W
      induction W with
      | nil => exact id
      | cons hadj _ ih => exact fun hu => ih (hclosure _ _ hadj hu)
    have hbase : ∃ κ : colorGermAt K p, inAnchorSide H K p q τ ⟨p, κ⟩ :=
      ⟨(τ p).symm (Sum.inr (anchorGermAtP p q)),
        Or.inl (Equiv.Perm.SameCycle.refl _ _)⟩
    obtain ⟨W⟩ := hpre x y hxy
    obtain ⟨κ0, hκ0⟩ := hwalk p x W hbase
    have hyx : y ∈ K.neighborSet x := hxy
    have hin_de : inAnchorSide H K p q τ ⟨x, ⟨y, hyx⟩⟩ := hmix x κ0 _ hκ0
    rcases hin_de with hA | hRA
    · exact huncov _ ((mem_anchorComponent_iff H K p q τ _).mpr hA) rfl
    · refine huncov _ ((mem_anchorComponent_iff H K p q τ _).mpr hRA) ?_
      rw [colorGermEdge_reverse]
      rfl

private lemma incidenceFinset_deleteEdges
    (M : SimpleGraph V) [DecidableRel M.Adj] (F : Finset (Sym2 V))
    [DecidableRel (M.deleteEdges (↑F : Set (Sym2 V))).Adj] (v : V) :
    (M.deleteEdges (↑F : Set (Sym2 V))).incidenceFinset v
      = M.incidenceFinset v \ F := by
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, Finset.mem_sdiff,
    SimpleGraph.incidenceSet, Set.mem_setOf_eq, SimpleGraph.edgeSet_deleteEdges,
    Set.mem_diff, Finset.mem_coe]
  tauto

private lemma degree_deleteEdges_eq
    (M : SimpleGraph V) [DecidableRel M.Adj] (F : Finset (Sym2 V))
    [DecidableRel (M.deleteEdges (↑F : Set (Sym2 V))).Adj] (v : V) :
    (M.deleteEdges (↑F : Set (Sym2 V))).degree v
      = (M.incidenceFinset v \ F).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,
    incidenceFinset_deleteEdges M F v]

private lemma isEdgeSplit_deleteEdges
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K) (F : Finset (Sym2 V))
    [DecidableRel (G.deleteEdges (↑F : Set (Sym2 V))).Adj]
    [DecidableRel (H.deleteEdges (↑F : Set (Sym2 V))).Adj]
    [DecidableRel (K.deleteEdges (↑F : Set (Sym2 V))).Adj] :
    IsEdgeSplit (G.deleteEdges (↑F : Set (Sym2 V)))
      (H.deleteEdges (↑F : Set (Sym2 V)))
      (K.deleteEdges (↑F : Set (Sym2 V))) := by
  obtain ⟨hpart, hdisj, hHle, hKle, hdegH, hdegK, hsum⟩ := hsplit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp only [SimpleGraph.deleteEdges_adj, hpart u v, or_and_right]
  · intro u v h1 h2
    rw [SimpleGraph.deleteEdges_adj] at h1 h2
    exact hdisj u v h1.1 h2.1
  · intro u v h
    rw [SimpleGraph.deleteEdges_adj] at h ⊢
    exact ⟨hHle h.1, h.2⟩
  · intro u v h
    rw [SimpleGraph.deleteEdges_adj] at h ⊢
    exact ⟨hKle h.1, h.2⟩
  · intro v
    have hsub : (H.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v
        ⊆ H.neighborFinset v := by
      intro u hu
      rw [SimpleGraph.mem_neighborFinset] at hu ⊢
      rw [SimpleGraph.deleteEdges_adj] at hu
      exact hu.1
    exact le_trans (Finset.card_le_card hsub) (hdegH v)
  · intro v
    have hsub : (K.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v
        ⊆ K.neighborFinset v := by
      intro u hu
      rw [SimpleGraph.mem_neighborFinset] at hu ⊢
      rw [SimpleGraph.deleteEdges_adj] at hu
      exact hu.1
    exact le_trans (Finset.card_le_card hsub) (hdegK v)
  · intro v
    have hunion : (G.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v
        = (H.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v
          ∪ (K.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v := by
      ext u
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset,
        SimpleGraph.deleteEdges_adj, hpart v u, or_and_right]
    have hdisj2 : Disjoint
        ((H.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v)
        ((K.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hu1 hu2
      exact hdisj v u hu1.1 hu2.1
    show ((H.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v).card
        + ((K.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v).card
        = ((G.deleteEdges (↑F : Set (Sym2 V))).neighborFinset v).card
    rw [hunion, Finset.card_union_of_disjoint hdisj2]

set_option maxHeartbeats 1000000 in
/-- (Fable SUM-PIN lane, 2026-07-13.)  The balanced-cocircuit trail theorem:
for `F` germ-balanced off the anchors (with the `+1` `K`-imbalance at both
anchors, stated as incidence counts) whose complement is reachable from `p`,
the complement `E∖F` is the edge set of ONE alternating `p→q` trail — the
transition machinery applied verbatim to the `deleteEdges` triple. -/
lemma maximal_walk_of_balanced_cocircuit
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (F : Finset (Sym2 V))
    (hbal : ∀ v, v ≠ p → v ≠ q →
      (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card)
    (hbalp : (K.incidenceFinset p \ F).card = (H.incidenceFinset p \ F).card + 1)
    (hbalq : (K.incidenceFinset q \ F).card = (H.incidenceFinset q \ F).card + 1)
    (hpre : ∀ e ∈ G.edgeSet, e ∉ F → ∀ v ∈ e,
      (G.deleteEdges (↑F : Set (Sym2 V))).Reachable p v) :
    ∃ w : G.Walk p q, w.IsTrail ∧ AlternatesKH H K w ∧
      w.edges.toFinset = G.edgeFinset \ F := by
  classical
  letI iG : DecidableRel (G.deleteEdges (↑F : Set (Sym2 V))).Adj :=
    Classical.decRel _
  letI iH : DecidableRel (H.deleteEdges (↑F : Set (Sym2 V))).Adj :=
    Classical.decRel _
  letI iK : DecidableRel (K.deleteEdges (↑F : Set (Sym2 V))).Adj :=
    Classical.decRel _
  have hsplit' := isEdgeSplit_deleteEdges G H K hsplit F
  have hbal' : ∀ v, v ≠ p → v ≠ q →
      (K.deleteEdges (↑F : Set (Sym2 V))).degree v
        = (H.deleteEdges (↑F : Set (Sym2 V))).degree v := by
    intro v hvp hvq
    rw [degree_deleteEdges_eq, degree_deleteEdges_eq, hbal v hvp hvq]
  have hbalp' : (K.deleteEdges (↑F : Set (Sym2 V))).degree p
      = (H.deleteEdges (↑F : Set (Sym2 V))).degree p + 1 := by
    rw [degree_deleteEdges_eq, degree_deleteEdges_eq, hbalp]
  have hbalq' : (K.deleteEdges (↑F : Set (Sym2 V))).degree q
      = (H.deleteEdges (↑F : Set (Sym2 V))).degree q + 1 := by
    rw [degree_deleteEdges_eq, degree_deleteEdges_eq, hbalq]
  have hne := exists_altTransitionSystem_balanced
    (H.deleteEdges (↑F : Set (Sym2 V))) (K.deleteEdges (↑F : Set (Sym2 V)))
    hpq hbal' hbalp' hbalq'
  obtain ⟨τ, hτmax⟩ := exists_anchorComponent_maximizer
    (H.deleteEdges (↑F : Set (Sym2 V))) (K.deleteEdges (↑F : Set (Sym2 V)))
    p q hne
  have hpre' : ∀ x y, (K.deleteEdges (↑F : Set (Sym2 V))).Adj x y →
      (G.deleteEdges (↑F : Set (Sym2 V))).Reachable p x := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj] at hxy
    refine hpre s(x, y) ((SimpleGraph.mem_edgeSet G).mpr
      (hsplit.2.2.2.1 hxy.1)) ?_ x (Sym2.mem_mk_left x y)
    intro hc
    exact hxy.2 (Finset.mem_coe.mpr hc)
  have hcover := anchorComponent_covers_K_of_maximal_pre
    (G.deleteEdges (↑F : Set (Sym2 V))) (H.deleteEdges (↑F : Set (Sym2 V)))
    (K.deleteEdges (↑F : Set (Sym2 V))) hsplit' hpq hpre' τ hτmax
  obtain ⟨w', htrail', halt', hKcov, hHcov⟩ :=
    walk_of_anchorComponent_covers_K
      (G.deleteEdges (↑F : Set (Sym2 V))) (H.deleteEdges (↑F : Set (Sym2 V)))
      (K.deleteEdges (↑F : Set (Sym2 V))) hsplit' hpq τ hcover
  have hall : ∀ e ∈ (G.deleteEdges (↑F : Set (Sym2 V))).edgeSet,
      e ∈ w'.edges := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hGuv := (SimpleGraph.mem_edgeSet _).mp he
        rcases (hsplit'.1 u v).mp hGuv with hH | hK
        · exact hHcov s(u, v) ((SimpleGraph.mem_edgeSet _).mpr hH)
        · exact hKcov s(u, v) ((SimpleGraph.mem_edgeSet _).mpr hK)
  have hWG : ∀ e ∈ w'.edges, e ∈ G.edgeSet := by
    intro e he
    have hmem := w'.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at hmem
    exact hmem.1
  refine ⟨w'.transfer G hWG, ⟨?_⟩, ?_, ?_⟩
  · rw [SimpleGraph.Walk.edges_transfer]
    exact htrail'.edges_nodup
  · intro i hi
    rw [SimpleGraph.Walk.length_transfer] at hi
    have h := halt' i hi
    constructor
    · intro hpar
      have hKadj := h.1 hpar
      rw [SimpleGraph.deleteEdges_adj] at hKadj
      rw [getVert_transfer w' hWG i, getVert_transfer w' hWG (i + 1)]
      exact hKadj.1
    · intro hpar
      have hHadj := h.2 hpar
      rw [SimpleGraph.deleteEdges_adj] at hHadj
      rw [getVert_transfer w' hWG i, getVert_transfer w' hWG (i + 1)]
      exact hHadj.1
  · ext e
    rw [List.mem_toFinset, SimpleGraph.Walk.edges_transfer, Finset.mem_sdiff,
      SimpleGraph.mem_edgeFinset]
    constructor
    · intro he
      have hmem := w'.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at hmem
      exact ⟨hmem.1, fun hc => hmem.2 (Finset.mem_coe.mpr hc)⟩
    · intro he
      apply hall
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he.1, fun hc => he.2 (Finset.mem_coe.mp hc)⟩

/-- (Fable SUM-PIN lane, 2026-07-13.)  Terminal maximality from the germ
marks: a trail whose edge set is `E∖F` with all three of `q`'s germs outside
`F` is a maximal alternating walk — both terminal clauses are discharged by
edge coverage, whatever the length parity. -/
lemma isMaximalAltWalk_of_edges_sdiff
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (F : Finset (Sym2 V)) (w : G.Walk p q)
    (htrail : w.IsTrail) (halt : AlternatesKH H K w)
    (hedges : w.edges.toFinset = G.edgeFinset \ F)
    (hqH : ∀ y, H.Adj q y → s(q, y) ∉ F)
    (hqK : ∀ y, K.Adj q y → s(q, y) ∉ F) :
    IsMaximalAltWalk G H K w := by
  refine ⟨htrail, halt, fun y => ⟨fun _ hK => ?_, fun _ hH => ?_⟩⟩
  · have hmem : s(q, y) ∈ G.edgeFinset \ F :=
      Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet G).mpr (hsplit.2.2.2.1 hK)), hqK y hK⟩
    rw [← hedges] at hmem
    exact List.mem_toFinset.mp hmem
  · have hmem : s(q, y) ∈ G.edgeFinset \ F :=
      Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet G).mpr (hsplit.2.2.1 hH)), hqH y hH⟩
    rw [← hedges] at hmem
    exact List.mem_toFinset.mp hmem

/-! ### Free-stop family and toggle composition (Fable TOGGLE lane, 2026-07-13)

Shared infrastructure for BOTH repair routes of `crossing_selection_toggle_sum`
(the one live pin below; see its docstring and TRIAGE-W12-15.md, 2026-07-13
reconciliation addendum).

* `alt_trail_incidence_count` — the exact per-vertex germ ledger of an
  alternating trail (Theorem A's `(k−h)` bookkeeping in exact, not mod-2,
  form): at every vertex the `K`-incidence count of the trail's edge set
  exceeds the `H`-incidence count by precisely the start/parity boundary
  terms.  Structural induction carrying BOTH alternation phases as a
  conjunction (the tail of a `K`-first trail is `H`-first).
* `freestop_toggle_valid` — the FREE-STOP validity law
  (fresh-strike/LENS-B3-INVARIANT.md §4, there derived by anchor degree
  arithmetic): EVERY alternating `K`-first `p→q` trail of ODD length is a
  valid toggle; endpoint maximality is NOT needed.  This formally widens the
  witness family from `IsMaximalAltWalk` — whose forced continuation is
  exactly what parity-locked the falsified walk-level pin into the Euler
  half-swap — to arbitrary odd-length `q`-stops, the family route B selects
  over.
* `alt_circuit_toggle_valid` — alternating EVEN circuits are germ-neutral at
  every vertex, hence always valid toggles (the lens's second witness
  family; also the validity engine for the quad).
* `toggled_toggled` / `toggle_compose` — toggles compose through symmetric
  difference: a valid toggle of a TOGGLED split composes with the original
  toggle into a valid toggle of the original split.  Route A (quad exchange)
  lives at this composite level.
* `quad_valid` — the LENS-B3-SURGERY §4 exchange primitive: an alternating
  quad `a–b–c–d` (edges alternately in `H` and `K`) is a valid toggle —
  proved by exhibiting the quad as an even alternating closed trail and
  invoking `alt_circuit_toggle_valid`, with no hand germ-count analysis.
-/

private lemma alt_trail_incidence_count_aux
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdisj : ∀ u v, H.Adj u v → K.Adj u v → False)
    {G : SimpleGraph V} {a b : V} (w : G.Walk a b) :
    w.IsTrail →
    ((AlternatesKH H K w → ∀ v : V,
      #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v}
        + (if w.length % 2 = 0 then (if v = b then 1 else 0) else 0)
      = #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v}
        + (if v = a then 1 else 0)
        + (if w.length % 2 = 1 then (if v = b then 1 else 0) else 0)) ∧
    (AlternatesKH K H w → ∀ v : V,
      #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v}
        + (if w.length % 2 = 0 then (if v = b then 1 else 0) else 0)
      = #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v}
        + (if v = a then 1 else 0)
        + (if w.length % 2 = 1 then (if v = b then 1 else 0) else 0))) := by
  induction w with
  | nil => intro _; constructor <;> intro _ v <;> simp
  | @cons a c b hadj w' ih =>
    intro htrail
    have hnd := htrail.edges_nodup
    rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnd
    have htrail' : w'.IsTrail := ⟨hnd.2⟩
    have hnotmem : s(a, c) ∉ w'.edges.toFinset :=
      fun hc => hnd.1 (List.mem_toFinset.mp hc)
    have hac : a ≠ c := hadj.ne
    have ihp := ih htrail'
    -- Inserting the first edge bumps the count of its own half at its two
    -- (distinct) endpoints and leaves the other half's count unchanged.
    have hcard : ∀ (M : SimpleGraph V) [DecidableRel M.Adj], M.Adj a c → ∀ v : V,
        #{e ∈ (SimpleGraph.Walk.cons hadj w').edges.toFinset |
            e ∈ M.incidenceFinset v}
          = #{e ∈ w'.edges.toFinset | e ∈ M.incidenceFinset v}
            + ((if v = a then 1 else 0) + (if v = c then 1 else 0)) := by
      intro M _ hM v
      rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons, Finset.filter_insert]
      by_cases hva : v = a
      · have hvc : ¬ v = c := fun h => hac (hva.symm.trans h)
        have hmem : s(a, c) ∈ M.incidenceFinset v := by
          rw [SimpleGraph.mem_incidenceFinset]
          refine ⟨(SimpleGraph.mem_edgeSet M).mpr hM, ?_⟩
          rw [hva]
          exact Sym2.mem_mk_left a c
        rw [if_pos hmem, Finset.card_insert_of_notMem
          (fun hc => hnotmem (Finset.mem_of_mem_filter _ hc)),
          if_pos hva, if_neg hvc]
      · by_cases hvc : v = c
        · have hmem : s(a, c) ∈ M.incidenceFinset v := by
            rw [SimpleGraph.mem_incidenceFinset]
            refine ⟨(SimpleGraph.mem_edgeSet M).mpr hM, ?_⟩
            rw [hvc]
            exact Sym2.mem_mk_right a c
          rw [if_pos hmem, Finset.card_insert_of_notMem
            (fun hc => hnotmem (Finset.mem_of_mem_filter _ hc)),
            if_neg hva, if_pos hvc]
        · have hnmem : s(a, c) ∉ M.incidenceFinset v := by
            intro hc
            rw [SimpleGraph.mem_incidenceFinset] at hc
            have h2 := hc.2
            rw [Sym2.mem_iff] at h2
            tauto
          rw [if_neg hnmem, if_neg hva, if_neg hvc]
          omega
    have hskip : ∀ (M : SimpleGraph V) [DecidableRel M.Adj], ¬ M.Adj a c → ∀ v : V,
        #{e ∈ (SimpleGraph.Walk.cons hadj w').edges.toFinset |
            e ∈ M.incidenceFinset v}
          = #{e ∈ w'.edges.toFinset | e ∈ M.incidenceFinset v} := by
      intro M _ hM v
      have hna : s(a, c) ∉ M.incidenceFinset v := by
        intro hc
        rw [SimpleGraph.mem_incidenceFinset] at hc
        exact hM ((SimpleGraph.mem_edgeSet M).mp hc.1)
      rw [SimpleGraph.Walk.edges_cons, List.toFinset_cons, Finset.filter_insert,
        if_neg hna]
    constructor
    · intro halt v
      have hKac : K.Adj a c := by
        have h0 := halt 0 (by rw [SimpleGraph.Walk.length_cons]; omega)
        have h1 := h0.1 rfl
        rw [SimpleGraph.Walk.getVert_zero] at h1
        rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] at h1
        exact h1
      have halt' : AlternatesKH K H w' := by
        intro i hi
        have h := halt (i + 1) (by rw [SimpleGraph.Walk.length_cons]; omega)
        simp only [SimpleGraph.Walk.getVert_cons_succ] at h
        exact ⟨fun hp => h.2 (by omega), fun hp => h.1 (by omega)⟩
      have hIH := ihp.2 halt' v
      have hK := hcard K hKac v
      have hH := hskip H (fun hc => hdisj a c hc hKac) v
      rw [hK, hH, SimpleGraph.Walk.length_cons]
      split_ifs at hIH ⊢ <;> omega
    · intro halt v
      have hHac : H.Adj a c := by
        have h0 := halt 0 (by rw [SimpleGraph.Walk.length_cons]; omega)
        have h1 := h0.1 rfl
        rw [SimpleGraph.Walk.getVert_zero] at h1
        rw [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] at h1
        exact h1
      have halt' : AlternatesKH H K w' := by
        intro i hi
        have h := halt (i + 1) (by rw [SimpleGraph.Walk.length_cons]; omega)
        simp only [SimpleGraph.Walk.getVert_cons_succ] at h
        exact ⟨fun hp => h.2 (by omega), fun hp => h.1 (by omega)⟩
      have hIH := ihp.1 halt' v
      have hH := hcard H hHac v
      have hK := hskip K (fun hc => hdisj a c hHac hc) v
      rw [hK, hH, SimpleGraph.Walk.length_cons]
      split_ifs at hIH ⊢ <;> omega

/-- (Fable TOGGLE lane, 2026-07-13.)  The exact per-vertex germ ledger of an
alternating `K`-first trail: `K`-incidence count = `H`-incidence count
+ (start boundary at `a`) + (odd-parity end boundary at `b`), with the
even-parity end boundary on the left.  Theorem A's `(k−h)` bookkeeping in
exact form, with NO maximality hypothesis. -/
lemma alt_trail_incidence_count
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdisj : ∀ u v, H.Adj u v → K.Adj u v → False)
    {G : SimpleGraph V} {a b : V} (w : G.Walk a b)
    (htrail : w.IsTrail) (halt : AlternatesKH H K w) (v : V) :
    #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v}
      + (if w.length % 2 = 0 then (if v = b then 1 else 0) else 0)
    = #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v}
      + (if v = a then 1 else 0)
      + (if w.length % 2 = 1 then (if v = b then 1 else 0) else 0) :=
  (alt_trail_incidence_count_aux H K hdisj w htrail).1 halt v

/-- FREE-STOP VALIDITY (fresh-strike/LENS-B3-INVARIANT.md §4, formalized).
Every alternating `K`-first `p→q` trail of ODD length is a valid toggle —
endpoint maximality is NOT required.  This is the witness-family widening of
repair route B: `IsMaximalAltWalk`'s endpoint clause forbids exactly these
odd-length `q`-stops, and that forced continuation is what parity-locked the
falsified walk-level sum pin into the Euler half-swap on the counterexample
corpora. -/
lemma freestop_toggle_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (w : G.Walk p q) (htrail : w.IsTrail) (halt : AlternatesKH H K w)
    (hodd : w.length % 2 = 1) :
    IsValidToggle G H K w.edges.toFinset := by
  have hT : ↑w.edges.toFinset ⊆ G.edgeSet := by
    intro e he
    exact w.edges_subset_edgeSet (List.mem_toFinset.mp (Finset.mem_coe.mp he))
  rw [toggle_valid_iff G H K hdeg hsplit _ hT]
  intro v
  have hcnt := alt_trail_incidence_count H K hsplit.2.1 w htrail halt v
  rw [if_neg (by omega : ¬ w.length % 2 = 0), if_pos hodd] at hcnt
  refine ⟨fun h4 => ?_, fun hHK => ?_, fun hHK => ?_⟩
  · have hvp : v ≠ p := fun h => by rw [h] at h4; omega
    have hvq : v ≠ q := fun h => by rw [h] at h4; omega
    rw [if_neg hvp, if_neg hvq] at hcnt
    omega
  · obtain ⟨hH2, _⟩ := hHK
    have hvp : v ≠ p := fun h => by rw [h] at hH2; omega
    have hvq : v ≠ q := fun h => by rw [h] at hH2; omega
    rw [if_neg hvp, if_neg hvq] at hcnt
    left; omega
  · by_cases hvp : v = p
    · subst hvp
      rw [if_pos rfl, if_neg hpq] at hcnt
      right; omega
    · by_cases hvq : v = q
      · subst hvq
        rw [if_neg (fun h => hpq h.symm), if_pos rfl] at hcnt
        right; omega
      · rw [if_neg hvp, if_neg hvq] at hcnt
        left; omega

/- ROUTE-A VALIDITY/COMPOSITION SUBLOCK RELOCATED to end-of-file (2026-07-13, Fable TOGGLE lane): `alt_circuit_toggle_valid`, `toggled_edgeFinset`, `toggled_toggled`, `degree_eq_of_graph_eq`, `isEdgeSplit_congr`, `toggle_compose`, `quad_valid`.  Nothing in this file consumes them; placing them here perturbed the environment seen by the known-fragile `grind +suggestions` step inside `double_visit_uses_H_edge` (same phenomenon as the three fragile steps reproved in-env during the W12 transplants) and broke its search.  Environment-order insulation, no content change. -/


/- FALSE-SUPERSEDED (2026-07-13, same lane, hours after authoring): via the
PROVED `maximal_walk_of_balanced_cocircuit` this cocircuit pin IMPLIES the
walk-level `crossing_selection_geo_sum`, which was falsified by two
independent fresh-look lenses (fresh-strike/LENS-B3-SURGERY.md §1: 9-vertex
counterexample, min new-odd SUM = 2 over all 308 maximal walks;
fresh-strike/LENS-B3-INVARIANT.md §1: independent CE1 n=9 + scalable
corridor family CE2) — hence FALSE.  Kept per the falsification-record
convention; NEVER dispatch.

/-- LADDER-PIN 12bc-F (Fable SUM-PIN lane, 2026-07-13; the walk-free core of
the SUM-card crossing selection — honest restatement after the
`birth_exchange` accounting failed on paper, TRIAGE-W12-15.md SUM-PIN
addendum).  In the blocked configuration there is a germ-balanced edge set
`F` (equal numbers of unused `K`- and `H`-germs at every non-anchor vertex,
the `+1` `K`-imbalance at both anchors), avoiding a marked internal edge
`eC` of the second odd component `R` and all three of `q`'s germs, whose
complement `E∖F` is reachable from `p` and — the entire selection content —
births at most ONE new odd-cycle support IN TOTAL when `E∖F` is toggled.
`F = ∅` (the Euler trail) satisfies every conjunct except the last, whose
Euler value is the half-swap ledger `|oddSupp K ∖ oddSupp H| + |oddSupp H ∖
oddSupp K| ≥ 2`; the pin asserts the corpus-verified minimum (133/133, net
odd privates ≤ min(1, a+b−1)) is achievable.  Via
`maximal_walk_of_balanced_cocircuit` (PROVED) this is equivalent to the
walk-level pin; no walk dynamics, debris trace, or forced spliced-end events
remain in this statement. -/
lemma exists_low_birth_cocircuit
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    {R : Finset V}
    (hR : (R ∈ oddCycleSupports H ∧ R ≠ S) ∨ R ∈ oddCycleSupports K)
    {eC : Sym2 V} (heCG : eC ∈ G.edgeSet) (heCR : ∀ v ∈ eC, v ∈ R) :
    ∃ F : Finset (Sym2 V),
      (∀ v, v ≠ p → v ≠ q →
        (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card) ∧
      (K.incidenceFinset p \ F).card = (H.incidenceFinset p \ F).card + 1 ∧
      (K.incidenceFinset q \ F).card = (H.incidenceFinset q \ F).card + 1 ∧
      (∀ e ∈ G.edgeSet, e ∉ F → ∀ v ∈ e,
        (G.deleteEdges (↑F : Set (Sym2 V))).Reachable p v) ∧
      eC ∉ F ∧
      (∀ y, H.Adj q y → s(q, y) ∉ F) ∧
      (∀ y, K.Adj q y → s(q, y) ∉ F) ∧
      (oddCycleSupports (toggled H (G.edgeFinset \ F)) \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K (G.edgeFinset \ F)) \ oddCycleSupports K).card
          ≤ 1 := by
  sorry
-/


/- FALSE (2026-07-13, cross-confirmed): falsified outright by both B3
lenses on the same instances as the sum pin (fresh-strike/LENS-B3-SURGERY.md
§1: min union card = 2; fresh-strike/LENS-B3-INVARIANT.md §1).  Was already
marked do-NOT-dispatch for the weaker too-weak-conclusion reason; now known
FALSE.  Record only.

/-- LADDER-PIN 12bc-geo (NEW, round 19 restatement of `crossing_selection`;
§6.10.2 Theorem B + §6.10.3 Theorem C, joint EFFECT form, config-(i) geometry
RESTORED and minimality DROPPED — the walk theorems never use `hmin`; Theorem D
only contradicts it afterwards).  The crossing steering of a reach witness:
some maximal alternating walk cuts `S`, cuts a second odd component, and
creates AT MOST ONE new odd-cycle support IN TOTAL across the two toggled
halves.  The union-card form is faithful to the four winner shapes of §6.10.3:
shapes 1/2 create no new odd support (main cycle even, privates even), shape 4
creates exactly one odd new cycle in total — possibly on the `K` side, which is
why the superseded two-conjunct form (`K`-subset + `H`-card) was too strong.
Consumed by `strict_of_reach_geo` via the death lemmas
(`strict_of_reach_deathH`/`deathK`) and the card accounting of the proved
`strict_of_reach` body.

SUPERSEDED (Fable finisher lane, 2026-07-13).  The UNION-card conclusion is
formally too weak for the Δω ledger: `card (A ∪ B) ≤ 1` permits
`A = B = {X}` — the same vertex set arising as a NEW odd support on BOTH
toggled halves (possible: the halves are edge-disjoint, and a deg-4 set can
carry an odd cycle in each) — in which case `card A + card B = 2` and the
glue accounting gives only `Δω ≤ 0`, not `< 0`.  §6.10.3's winner shapes
bound the number of new odd CYCLES in total, i.e. the SUM of the two sides'
new-support counts; a both-sides support is two new cycles and is excluded
informally but not by this statement.  Faithful form: the SUM-card pin
`crossing_selection_geo_sum` below.  Kept for the record; do NOT dispatch
this form — a proof of it cannot complete `strict_of_reach_geo`. -/
lemma crossing_selection_geo
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w ∧
      ((oddCycleSupports (toggled H w.edges.toFinset) \ oddCycleSupports H)
        ∪ (oddCycleSupports (toggled K w.edges.toFinset) \ oddCycleSupports K)).card
          ≤ 1 := by
  sorry
-/

/- FALSE (2026-07-13, DOUBLE-falsified; orchestrator redirect).  Explicit
counterexamples on instances satisfying EVERY hypothesis:
fresh-strike/LENS-B3-SURGERY.md §1 (n=9: all 308 maximal alternating walks
give new-odd SUM = 2; the whole walk class is Δω-parity-locked at 0 —
Δω ≡ ℓ + ℓ₀ (mod 2) — so NO walk-internal selection or exchange can repair
it) and fresh-strike/LENS-B3-INVARIANT.md §1 (independent CE1 n=9, 312
walks, min = 2; scalable corridor family CE2 n=10+4s; root cause:
`IsMaximalAltWalk`'s endpoint clause forbids the odd-length `q`-stop,
forcing the Euler half-swap; minimizers' two "new" supports are MIGRATIONS
of the two dead ones).  ~9-12% of random geometry-valid instances violate.
Live replacement: `crossing_selection_toggle_sum` below.  Kept per the
falsification-record convention; NEVER dispatch.

/-- LADDER-PIN 12bc-geo-sum (Fable finisher lane, 2026-07-13; the faithful
SUM-card restatement of `crossing_selection_geo`, which is superseded — its
union-card conclusion admits the both-sides corner `A = B = {X}` that breaks
the Δω ledger, see its docstring).  §6.10.3's four winner shapes bound the
number of new odd CYCLES in total: shapes 1/2 create none, shape 4 creates
exactly ONE (on either side).  The effect form of that bound is the SUM of
the two sides' new-odd-support counts, which is what the `strict_of_reach_geo`
glue (now PROVED below, consuming this pin) needs: two dead supports
(`S` by `maximal_walk_cuts_poisoned` + the second odd by `CutsSecondOdd`,
via the death lemmas) against ≤ 1 new in total gives `Δω ≤ −1`.
Note the Euler route does NOT trivialize this pin: the alternating Eulerian
trail's toggle is the exact half-swap (`H △ E(G) = K`, `K △ E(G) = H`,
`Δω = 0` identically — 2026-07-13 derivation, TRIAGE addendum), so the
steering/selection content — pick a maximal walk minimizing new odd supports;
exchange at re-entries (`germ_flip`) reduces any walk with ≥ 2 — remains the
one open hard core of the navigation route. -/
lemma crossing_selection_geo_sum
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w ∧
      (oddCycleSupports (toggled H w.edges.toFinset) \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K w.edges.toFinset) \ oddCycleSupports K).card
          ≤ 1 := by
  sorry
-/

/-- LADDER-PIN 12bc-FS-ODD (PARITY-SPLIT sub-pin, Fable parity-split lane
2026-07-13; the ONE open object of the t ≤ 2 navigation route).  The odd-ℓ_P
case of `exists_low_birth_freestop_cocircuit` below.  Wave 21's three failed
prover framings (shortest / exchange / direct) converged on the same
structure: the SELECT-pin reduces to the parity of the p–q H-path.  EVEN
ℓ_P is IMPOSSIBLE in the hypothesis world — `canonical_strict_of_ellP_even`
(PROVED) yields a strict valid toggle contradicting `hmin` via
`not_minimal_iff_exists_strict_toggle`; see the parity-split assembly in the
parent pin below.  So the parent reduces to THIS pin.  The extra hypothesis
`hPodd` says every p–q H-path has odd length; since `H` has maximum degree 2
the p–q H-path is unique, so this is exactly "ℓ_P is odd" — the form every
corpus instance satisfies (`hPodd`/`has_odd_simple_path` is part of the
hypothesis gate in the executable semantics), hence the PREVALIDATE-FREESTOP
validation (≈12,500 hypothesis-passing instances, 130 prior-hard cex, born
≤ 1 tight, zero failures) covers this pin VERBATIM.  Hypothesis block and
conclusion are otherwise BYTE-IDENTICAL to the parent (do-not-diverge:
mirrored edits only, same clause as `genxsel_general`).
WAVE-22 NEGATIVE INTELLIGENCE (validated 2026-07-13 BEFORE authoring;
fresh-strike/FALSIFY-DEBRIS-CONNECTIVITY.md): the recommended
debris-connectivity strengthening (conclude j_H = 1 ∧ j_K = 1 for the
realized free-stop trail, FABLE-TOGGLE-PARTIAL §3) is FALSE as a required
conjunct — exhaustive scans over the full free-stop witness space found
hypothesis-passing instances where NO valid free-stop trail has connected
H-debris (falsifier n=15; corridor15), NO trail has connected K-debris
(surgeon n=9, corridor15), and NO winner even boundary-crosses a second odd
support (surgeon n=9).  Winners exist on every instance (the ledger
conjuncts alone), but their debris may be disconnected, the extra components
even or migrating.  Do NOT dispatch connectivity-conclusion variants.  What
the scans confirm mechanically (0 violations corpus-wide): a boundary-crossed
support always dies (`cut_supports_die_general`, PROVED), and connected
K-debris ⇒ born_K = 0 where it does hold.  The open content is the H-side
low-birth selection (born_H ≤ 1) with migration corners excluded by `hmin`. -/
lemma exists_low_birth_freestop_cocircuit_odd
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∀ w : H.Walk p q, w.IsPath → Odd w.length)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ F : Finset (Sym2 V),
      (∀ v, v ≠ p → v ≠ q →
        (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card) ∧
      (K.incidenceFinset p \ F).card = (H.incidenceFinset p \ F).card + 1 ∧
      (K.incidenceFinset q \ F).card = (H.incidenceFinset q \ F).card + 1 ∧
      (∀ e ∈ G.edgeSet, e ∉ F → ∀ v ∈ e,
        (G.deleteEdges (↑F : Set (Sym2 V))).Reachable p v) ∧
      (G.edgeFinset \ F).card % 2 = 1 ∧
      2 ≤ (oddCycleSupports H
            \ oddCycleSupports (toggled H (G.edgeFinset \ F))).card
        + (oddCycleSupports K
            \ oddCycleSupports (toggled K (G.edgeFinset \ F))).card ∧
      (oddCycleSupports (toggled H (G.edgeFinset \ F))
            \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K (G.edgeFinset \ F))
            \ oddCycleSupports K).card ≤ 1 := by
  sorry

/-- LADDER-PIN 12bc-FS (SELECT-pin, Fable TOGGLE lane 2026-07-13; the
walk-free route-B selection core of `crossing_selection_toggle_sum` below,
stated in the TRANSITION-SYSTEM formalism per the STRIKE-C §0.5 route
preference — the general-t descent is assembly-only if the t ≤ 2 pin closes
in this formalism).  In the blocked minimal configuration there is a
germ-balanced edge set `F` — equal numbers of unused `K`- and `H`-germs at
every non-anchor vertex, the `+1` `K`-imbalance at BOTH anchors — whose
complement is reachable from `p`, and whose complement-toggle satisfies the
descent ledger: at least TWO dead original odd supports against at most ONE
born one (card sums, so migrations net zero).  Differences from the
FALSIFIED `exists_low_birth_cocircuit` (commented record above): (i) NO
`q`-germ marks — the balance at `q` already encodes an odd-length
`q`-arrival, and the marks were exactly the over-restriction that forced
endpoint maximality and the Euler half-swap (LENS-B3-INVARIANT §4 root
cause); (ii) `hmin` CARRIED (the falsifier's load-bearing hypothesis);
(iii) the dead-card conjunct is part of the selection (under free stops,
`S`-death is a selection property, not automatic).  The odd-card conjunct
is implied by the three balance conjuncts (handshake on the deleted halves:
`|E_K∖F| = |E_H∖F| + 1`); it is included so the assembly needs no
double-count derivation.  COMPUTATIONAL VALIDATION (PREVALIDATE-FREESTOP.md,
2026-07-13, pre-registered hunts): the free-stop family satisfies this
conclusion on ALL ≈12,500 hypothesis-passing instances tested, including
all 130 known maximal-walk counterexamples and the corridor family through
n = 41 (born ≤ 1 tight, never exceeded; winning trails short); zero
counterexamples.  Via `maximal_walk_of_balanced_cocircuit` +
`freestop_toggle_valid` (both PROVED) this pin yields
`crossing_selection_toggle_sum` — see the assembly there.
PARITY-SPLIT (Fable parity-split lane 2026-07-13; statement BYTE-UNTOUCHED):
the body is now the PROVED two-case assembly the three wave-21 provers
converged on — EVEN p–q H-path: `canonical_strict_of_ellP_even` (PROVED)
produces a strict valid toggle, contradicting `hmin` via
`not_minimal_iff_exists_strict_toggle` (the even world is EMPTY, by proof —
not a vacuity shortcut on the whole hypothesis block, which remains
uncertified); ODD (every p–q H-path odd): the frozen sub-pin
`exists_low_birth_freestop_cocircuit_odd` above.  sorryAx flows SOLELY
through that sub-pin. -/
lemma exists_low_birth_freestop_cocircuit
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ F : Finset (Sym2 V),
      (∀ v, v ≠ p → v ≠ q →
        (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card) ∧
      (K.incidenceFinset p \ F).card = (H.incidenceFinset p \ F).card + 1 ∧
      (K.incidenceFinset q \ F).card = (H.incidenceFinset q \ F).card + 1 ∧
      (∀ e ∈ G.edgeSet, e ∉ F → ∀ v ∈ e,
        (G.deleteEdges (↑F : Set (Sym2 V))).Reachable p v) ∧
      (G.edgeFinset \ F).card % 2 = 1 ∧
      2 ≤ (oddCycleSupports H
            \ oddCycleSupports (toggled H (G.edgeFinset \ F))).card
        + (oddCycleSupports K
            \ oddCycleSupports (toggled K (G.edgeFinset \ F))).card ∧
      (oddCycleSupports (toggled H (G.edgeFinset \ F))
            \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K (G.edgeFinset \ F))
            \ oddCycleSupports K).card ≤ 1 := by
  -- PARITY-SPLIT ASSEMBLY (Fable parity-split lane, 2026-07-13; statement
  -- byte-untouched).  Split on the existence of an EVEN p–q H-path.
  classical
  by_cases hPeven : ∃ w : H.Walk p q, w.IsPath ∧ Even w.length
  · -- EVEN case: the canonical §6.2 argument (PROVED) yields a strict valid
    -- toggle, contradicting minimality — this branch of the world is empty.
    exact absurd hmin
      ((not_minimal_iff_exists_strict_toggle G H K hdeg hmin.1).mpr
        (canonical_strict_of_ellP_even G H K hconn hdeg hmin ht2 hpq hp3 hq3
          hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hPeven))
  · -- ODD case: every p–q H-path is odd — the frozen sub-pin above.
    push_neg at hPeven
    exact exists_low_birth_freestop_cocircuit_odd G H K hconn hdeg hmin ht2
      hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2
      (fun w hw => Nat.not_even_iff_odd.mp (hPeven w hw)) hreach

/-- LADDER-PIN 12bc-T (TOGGLE-LEVEL restatement, Fable SUM-PIN lane
2026-07-13, after the double falsification of the walk-level sum pin — see
the commented record above; TRIPLE-confirmed by the adversarial falsifier,
fresh-strike/FALSIFY-SUMPIN.md, which adds its own n=15 counterexample AND
the third root cause: the informal winner-shape argument is MINIMALITY-
using, both counterexample families are non-minimal, and no minimal
counterexample could be constructed across ~11,500 gadgets — so `hmin` is
load-bearing and is RESTORED here, replacing `hsplit = hmin.1`; the three
CE corpora all negate the hypotheses of this strengthened form, validating
it computationally before authoring).  The consumer needs only a valid toggle with
at least TWO dead original odd supports against at most ONE born one IN
TOTAL (cards, so a support MIGRATING across halves counts on both sides of
the ledger and nets zero).  The witness family is deliberately NOT fixed.
Two validated repair routes supply it: (A) QUAD EXCHANGE
(fresh-strike/LENS-B3-SURGERY.md §3, 40/40 repairs): an argmin maximal-walk
toggle composed with an alternating quad on the TOGGLED split — the
existence ranges over (walk, quad) pairs; (B) FREE-STOP
(fresh-strike/LENS-B3-INVARIANT.md §4, 173/173 incl. the corridor family):
alternating K-first trails allowed to stop at any odd-length `q`-arrival —
always a valid toggle by the anchor degree arithmetic; the free-stop winners
exhibit ≥ 2 non-resurrected deaths + ≤ 1 genuine debris.  Route B is the
recommended proof route: it deletes an over-restriction instead of adding
machinery, and `maximal_walk_of_balanced_cocircuit` above (PROVED) already
constructs the free-stop family from balanced cocircuits (balance at `q`
encodes the odd-length arrival; the `q`-germ marks are exactly the dropped
over-restriction).  Accounting spine, paper-verified against both lenses:
max-deg-2 spanning graphs have #odd components ≡ n − (total path support)
(mod 2); hence Δω ≡ ℓ + ℓ₀ (mod 2) — the parity lock that killed the walk
class, and that stopping early (or the quad's ℓ ← ℓ + |B|) flips. -/
lemma crossing_selection_toggle_sum
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧
      2 ≤ (oddCycleSupports H \ oddCycleSupports (toggled H T)).card
        + (oddCycleSupports K \ oddCycleSupports (toggled K T)).card ∧
      (oddCycleSupports (toggled H T) \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K T) \ oddCycleSupports K).card ≤ 1 := by
  -- ASSEMBLY (Fable TOGGLE lane, 2026-07-13; statement byte-untouched):
  -- route B through the transition-system machinery.  The SELECT-pin above
  -- supplies the balanced cocircuit `F`; `maximal_walk_of_balanced_cocircuit`
  -- (PROVED) realizes `E∖F` as one alternating `p→q` trail; its odd length
  -- comes from the odd-card conjunct; `freestop_toggle_valid` (PROVED) makes
  -- it a valid toggle with no maximality clause; the ledger conjuncts are the
  -- pin's conclusion verbatim.  sorryAx flows SOLELY through
  -- `exists_low_birth_freestop_cocircuit`.
  classical
  obtain ⟨F, hbal, hbalp, hbalq, hpre, hodd, hdead, hborn⟩ :=
    exists_low_birth_freestop_cocircuit G H K hconn hdeg hmin ht2 hpq hp3 hq3
      hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hreach
  obtain ⟨w, htrail, halt, hedges⟩ :=
    maximal_walk_of_balanced_cocircuit G H K hmin.1 hpq F hbal hbalp hbalq hpre
  have hlen : w.length % 2 = 1 := by
    have h1 : w.edges.length = w.length := SimpleGraph.Walk.length_edges w
    have h2 : w.edges.toFinset.card = w.edges.length :=
      List.toFinset_card_of_nodup htrail.edges_nodup
    rw [hedges] at h2
    omega
  have hvalid := freestop_toggle_valid G H K hdeg hmin.1 hpq hp3 hq3 hpH hqH
    w htrail halt hlen
  rw [hedges] at hvalid
  exact ⟨G.edgeFinset \ F, hvalid, hdead, hborn⟩

/-
Helper for `strict_of_reach` (§6.10.4).  A vertex on a cycle has two distinct neighbours, both on
the cycle.
-/
lemma cycle_two_distinct_nbrs
    {M : SimpleGraph V} {z : V} (c : M.Walk z z) (hc : c.IsCycle)
    {u : V} (hu : u ∈ c.support) :
    ∃ y y', y ≠ y' ∧ y ∈ c.support ∧ y' ∈ c.support ∧ M.Adj u y ∧ M.Adj u y' := by
  by_contra! h;
  obtain ⟨i, hi⟩ : ∃ i, i < c.length ∧ c.getVert i = u := by
    rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hu;
    obtain ⟨ n, rfl, hn ⟩ := hu;
    cases hn.eq_or_lt <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
    · exact ⟨ 0, Nat.pos_of_ne_zero ( by rintro h; simp_all +decide [ SimpleGraph.Walk.isCycle_def ] ), by simp +decide ⟩;
    · exact ⟨ n, by assumption, rfl ⟩;
  have h_adj : M.Adj (c.getVert (if i = 0 then c.length - 1 else i - 1)) (c.getVert i) ∧ M.Adj (c.getVert i) (c.getVert (if i = c.length - 1 then 0 else i + 1)) := by
    have h_adj : ∀ i < c.length, M.Adj (c.getVert i) (c.getVert (if i = c.length - 1 then 0 else i + 1)) := by
      intro i hi;
      convert c.adj_getVert_succ hi using 1;
      split_ifs <;> simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ c.length from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ];
    grind;
  have h_distinct : c.getVert (if i = 0 then c.length - 1 else i - 1) ≠ c.getVert (if i = c.length - 1 then 0 else i + 1) := by
    have h_distinct : ∀ i j : ℕ, i < c.length → j < c.length → i ≠ j → i ≠ 0 → j ≠ 0 → c.getVert i = c.getVert j → False := by
      intros i j hi hj hij hi0 hj0 h_eq;
      have := hc.getVert_injOn;
      exact hij ( this ⟨ Nat.pos_of_ne_zero hi0, hi.le ⟩ ⟨ Nat.pos_of_ne_zero hj0, hj.le ⟩ h_eq );
    rcases n : c.length with ( _ | _ | _ | n ) <;> simp_all +decide;
    · have := hc.three_le_length; simp_all +decide ;
    · grind +suggestions;
  apply h (c.getVert (if i = 0 then c.length - 1 else i - 1)) (c.getVert (if i = c.length - 1 then 0 else i + 1)) h_distinct;
  · grind +suggestions;
  · grind +suggestions;
  · rw [ ← hi.2 ] ; exact h_adj.1.symm;
  · grind

/-
Helper for `strict_of_reach` (§6.10.4, cut supports die).  A cut odd `H`-support dies under the
toggle by the maximal alternating walk (Pins2 surgery template).
-/
lemma strict_of_reach_deathH
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (hK2 : ∀ v, K.degree v = 2)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    {x' : V} (w' : G.Walk p x') (hmax' : IsMaximalAltWalk G H K w')
    (hvalid : IsValidToggle G H K w'.edges.toFinset)
    (S' : Finset V) (hS' : S' ∈ oddCycleSupports H) (hcut : WalkCuts w' S') :
    S' ∉ oddCycleSupports (toggled H w'.edges.toFinset) := by
  obtain ⟨ e, he, he' ⟩ := hcut;
  -- Since $p \notin S'$, there must be an edge $e$ in $w'$ that connects a vertex in $S'$ to a vertex not in $S'$.
  obtain ⟨i, hi⟩ : ∃ i < w'.length, w'.getVert i ∉ S' ∧ w'.getVert (i + 1) ∈ S' := by
    obtain ⟨a, ha⟩ : ∃ a ∈ w'.support, a ∈ S' ∧ w'.getVert 0 ∉ S' := by
      obtain ⟨a, ha⟩ : ∃ a ∈ w'.support, a ∈ S' := by
        rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.Walk.fst_mem_support_of_mem_edges ] ;
        exact ⟨ u, SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he, he'.1 ⟩;
      have h_p_not_in_S' : ∀ v ∈ S', H.degree v = 2 := by
        rw [ oddCycleSupports ] at hS';
        simp +zetaDelta at *;
        obtain ⟨ x, w, hw, hw', rfl ⟩ := hS';
        exact fun v hv => degree_eq_two_of_mem_cycle_support H ( fun v => hsplit.2.2.2.2.1 v ) hw ( by simpa using hv );
      exact ⟨ a, ha.1, ha.2, fun h => by have := h_p_not_in_S' _ h; aesop ⟩;
    obtain ⟨i, hi⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ∧ ∀ j < i, w'.getVert j ∉ S' := by
      obtain ⟨i, hi⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' := by
        obtain ⟨ i, hi ⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha.1; use i; aesop;
      exact ⟨ Nat.find ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ), Nat.find_spec ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ) |>.1, Nat.find_spec ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ) |>.2, fun j hj => fun hj' => Nat.find_min ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ) hj ⟨ by linarith [ Nat.find_spec ( ⟨ i, hi.1, hi.2 ⟩ : ∃ i ≤ w'.length, w'.getVert i ∈ S' ) |>.1 ], hj' ⟩ ⟩;
    rcases i <;> simp_all +decide;
    exact ⟨ _, hi.1, hi.2.2 _ le_rfl, hi.2.1 ⟩;
  -- Let $pr = w'.getVert i$ and $u = w'.getVert (i + 1)$.
  set pr := w'.getVert i
  set u := w'.getVert (i + 1);
  -- Since $pr \notin S'$ and $u \in S'$, we have $¬H.Adj u pr$.
  have h_not_adj : ¬H.Adj u pr := by
    -- Since $u$ is in $S'$ and $pr$ is not in $S'$, $u$ and $pr$ cannot be adjacent in $H$.
    have h_not_adj : ∀ v ∈ S', H.degree v = 2 := by
      have := hS';
      unfold oddCycleSupports at this; simp_all +decide ;
      obtain ⟨ x, w, hw₁, hw₂, hw₃ ⟩ := this; intro v hv; rw [ ← hw₃ ] at hv; exact degree_eq_two_of_mem_cycle_support H hsplit.2.2.2.2.1 hw₁ ( by aesop ) ;
    have h_not_adj : Finset.card (H.neighborFinset u \ S') = 0 := by
      have h_not_adj : Finset.card (H.neighborFinset u ∩ S') ≥ 2 := by
        obtain ⟨z, c, hc, hcsupp⟩ : ∃ z, ∃ c : H.Walk z z, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S' := by
          unfold oddCycleSupports at hS'; aesop;
        obtain ⟨y, y', hy, hy', hy_ne⟩ : ∃ y y', y ≠ y' ∧ y ∈ c.support ∧ y' ∈ c.support ∧ H.Adj u y ∧ H.Adj u y' := by
          apply cycle_two_distinct_nbrs c hc;
          exact List.mem_toFinset.mp ( hcsupp.2.symm ▸ hi.2.2 );
        refine' Finset.one_lt_card.mpr ⟨ y, _, y', _, _ ⟩ <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · exact hcsupp.2 ▸ by simpa using hy';
        · exact hcsupp.2 ▸ by simpa using hy_ne.1;
      have h_not_adj : Finset.card (H.neighborFinset u) = 2 := by
        aesop;
      grind;
    simp_all +decide [ Finset.ext_iff ];
    exact fun h => hi.2.1 ( h_not_adj _ h );
  -- Since $pr \notin S'$ and $u \in S'$, we have $(toggled H w'.edges.toFinset).Adj u pr$.
  have h_adj : (toggled H w'.edges.toFinset).Adj u pr := by
    have h_adj : s(u, pr) ∈ w'.edges := by
      have h_adj : s(pr, u) ∈ w'.edges := by
        have h_adj : ∀ {u v : V} {w : G.Walk u v} {i : ℕ}, i < w.length → s(w.getVert i, w.getVert (i + 1)) ∈ w.edges := by
          intros u v w i hi; induction' w with u v w ih generalizing i; aesop;
          rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
        exact h_adj hi.1;
      rwa [ Sym2.eq_swap ];
    unfold toggled; simp +decide [ *, symmDiff ] ;
    grind;
  intro hS'';
  obtain ⟨z, c, hc, hcsupp⟩ : ∃ z, ∃ c : (toggled H w'.edges.toFinset).Walk z z, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S' := by
    unfold oddCycleSupports at hS''; aesop;
  -- Since $u \in S'$ and $S'$ is an odd cycle support in $toggled H w'.edges.toFinset$, we have $(toggled H w'.edges.toFinset).degree u = 2$.
  have h_deg_u : (toggled H w'.edges.toFinset).degree u = 2 := by
    apply degree_eq_two_of_mem_cycle_support;
    any_goals exact c;
    · have := hvalid.2;
      exact this.2.2.2.2.1;
    · exact hc;
    · exact List.mem_toFinset.mp ( hcsupp.2.symm ▸ hi.2.2 );
  -- Since $u$ is in $S'$ and $S'$ is an odd cycle support in $toggled H w'.edges.toFinset$, we have $(toggled H w'.edges.toFinset).neighborFinset u = {pr, w₁, w₂}$ for some $w₁, w₂ \in S'$.
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁w₂⟩ : ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ w₁ ∈ S' ∧ w₂ ∈ S' ∧ (toggled H w'.edges.toFinset).Adj u w₁ ∧ (toggled H w'.edges.toFinset).Adj u w₂ := by
    have := cycle_two_distinct_nbrs c hc ( show u ∈ c.support from by
                                            exact List.mem_toFinset.mp ( hcsupp.2.symm ▸ hi.2.2 ) );
    obtain ⟨ y, y', hy, hy', hy'', hy''' ⟩ := this; use y, y'; simp_all +decide [ Finset.ext_iff ] ;
  have h_neighborFinset : (toggled H w'.edges.toFinset).neighborFinset u ⊇ {pr, w₁, w₂} := by
    simp_all +decide [ Finset.insert_subset_iff ];
  have := Finset.card_mono h_neighborFinset; simp_all +decide ;
  grind

/-
Helper for `strict_of_reach` (§6.10.4, cut supports die).  A cut odd `K`-support dies under the
toggle by the maximal alternating walk (Pins2 surgery template).
-/
lemma strict_of_reach_deathK
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (hK2 : ∀ v, K.degree v = 2)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    {x' : V} (w' : G.Walk p x') (hmax' : IsMaximalAltWalk G H K w')
    (hvalid : IsValidToggle G H K w'.edges.toFinset)
    (S' : Finset V) (hS' : S' ∈ oddCycleSupports K) (hcut : WalkCuts w' S')
    (hout : ∃ v ∈ w'.support, v ∉ S') :
    S' ∉ oddCycleSupports (toggled K w'.edges.toFinset) := by
  intro hcon;
  -- By definition of `oddCycleSupports`, there exists a cycle `c` in `K` such that `c.support.toFinset = S'`.
  obtain ⟨z, c, hc⟩ : ∃ z : V, ∃ c : K.Walk z z, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S' := by
    unfold oddCycleSupports at hS'; aesop;
  obtain ⟨u, pr, hpr⟩ : ∃ u pr : V, u ∈ S' ∧ pr ∉ S' ∧ s(pr, u) ∈ w'.edges ∧ G.Adj pr u := by
    obtain ⟨i, hi⟩ : ∃ i < w'.length, (w'.getVert i ∉ S' ∧ w'.getVert (i + 1) ∈ S') ∨ (w'.getVert i ∈ S' ∧ w'.getVert (i + 1) ∉ S') := by
      by_cases h_cases : w'.getVert 0 ∈ S';
      · obtain ⟨v, hv⟩ : ∃ v ∈ w'.support, v ∉ S' := hout;
        obtain ⟨i, hi⟩ : ∃ i ≤ w'.length, w'.getVert i ∉ S' ∧ ∀ j < i, w'.getVert j ∈ S' := by
          have h_exists_i : ∃ i ≤ w'.length, w'.getVert i ∉ S' := by
            rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hv ; aesop;
          exact ⟨ Nat.find h_exists_i, Nat.find_spec h_exists_i |>.1, Nat.find_spec h_exists_i |>.2, fun j hj => Classical.not_not.1 fun hj' => Nat.find_min h_exists_i hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_exists_i |>.1 ), hj' ⟩ ⟩;
        rcases i <;> simp_all +decide;
        exact ⟨ _, hi.1, Or.inr ⟨ hi.2.2 _ le_rfl, hi.2.1 ⟩ ⟩;
      · obtain ⟨a, ha⟩ : ∃ a ∈ w'.support, a ∈ S' := by
          obtain ⟨ e, he, he' ⟩ := hcut;
          rcases e with ⟨ u, v ⟩;
          exact ⟨ u, by simpa using SimpleGraph.Walk.fst_mem_support_of_mem_edges w' he, he' u ( by simp +decide ) ⟩;
        obtain ⟨i, hi⟩ : ∃ i < w'.length, w'.getVert (i + 1) ∈ S' := by
          obtain ⟨i, hi⟩ : ∃ i, i ≤ w'.length ∧ w'.getVert i ∈ S' := by
            have := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha.1; aesop;
          induction' i with i ih;
          · tauto;
          · exact ⟨ i, hi.1, hi.2 ⟩;
        induction' i with i ih;
        · exact ⟨ 0, hi.1, Or.inl ⟨ h_cases, hi.2 ⟩ ⟩;
        · grind;
    cases' hi.2 with h h;
    · use w'.getVert (i + 1), w'.getVert i;
      exact ⟨ h.2, h.1, by
        have h_edge : ∀ {u v : V} {w : G.Walk u v} {i : ℕ}, i < w.length → s(w.getVert i, w.getVert (i + 1)) ∈ w.edges := by
          intros u v w i hi; induction' w with u v w ih generalizing i; aesop;
          rcases i with ( _ | i ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        exact h_edge hi.1, by
        convert w'.adj_getVert_succ _;
        exact hi.1 ⟩;
    · use w'.getVert i, w'.getVert (i + 1);
      have h_edge : s(w'.getVert i, w'.getVert (i + 1)) ∈ w'.edges := by
        have h_edge : ∀ i < w'.length, s(w'.getVert i, w'.getVert (i + 1)) ∈ w'.edges := by
          intro i hi;
          have h_edge : ∀ {u v : V} {w : G.Walk u v} {i : ℕ}, i < w.length → s(w.getVert i, w.getVert (i + 1)) ∈ w.edges := by
            intros u v w i hi; induction' w with u v w ih generalizing i; aesop;
            rcases i with ( _ | i ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
          exact h_edge hi;
        exact h_edge i hi.1;
      exact ⟨ h.1, h.2, by simpa only [ Sym2.eq_swap ] using h_edge, by simpa only [ SimpleGraph.adj_comm ] using w'.adj_getVert_succ ( by linarith ) ⟩;
  -- Since $u$ is in $S'$ and $pr$ is not in $S'$, $u$ and $pr$ are not adjacent in $K$.
  have h_not_adj : ¬K.Adj u pr := by
    obtain ⟨y, y', hy, hy'⟩ : ∃ y y' : V, y ≠ y' ∧ y ∈ c.support ∧ y' ∈ c.support ∧ K.Adj u y ∧ K.Adj u y' := by
      apply cycle_two_distinct_nbrs c hc.left;
      exact List.mem_toFinset.mp ( hc.2.2.symm ▸ hpr.1 );
    have h_not_adj : K.neighborFinset u = {y, y'} := by
      rw [ Finset.eq_of_subset_of_card_le ( show { y, y' } ⊆ K.neighborFinset u from by aesop_cat ) ] ; aesop_cat;
    -- robust replacement for a fragile `grind +suggestions` (Windows quirk):
    -- `pr` is a `K`-neighbour of `u` ⇒ `pr ∈ {y, y'} ⊆ S'`, but `pr ∉ S'`.
    intro hadj
    have hpr_nbr : pr ∈ K.neighborFinset u := by
      rw [SimpleGraph.mem_neighborFinset]; exact hadj
    rw [h_not_adj] at hpr_nbr
    have hyS' : y ∈ S' := hc.2.2 ▸ List.mem_toFinset.mpr hy'.1
    have hy'S' : y' ∈ S' := hc.2.2 ▸ List.mem_toFinset.mpr hy'.2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpr_nbr
    rcases hpr_nbr with rfl | rfl
    · exact hpr.2.1 hyS'
    · exact hpr.2.1 hy'S'
  -- Since $u$ is in $S'$ and $pr$ is not in $S'$, $u$ and $pr$ are adjacent in the toggled graph.
  have h_adj_toggled : (toggled K w'.edges.toFinset).Adj u pr := by
    simp_all +decide [ toggled, SimpleGraph.fromEdgeSet_adj ];
    simp_all +decide [ symmDiff, SimpleGraph.adj_comm ];
    exact ⟨ by simpa only [ Sym2.eq_swap ] using hpr.2.2.1, by rintro rfl; exact hpr.2.1 hpr.1 ⟩;
  -- Since $u$ is in $S'$ and $pr$ is not in $S'$, $u$ and $pr$ are adjacent in the toggled graph, and $u$ has degree at most 2 in the toggled graph.
  have h_deg_toggled : (toggled K w'.edges.toFinset).degree u ≤ 2 := by
    exact hvalid.2.2.2.2.2.2.1 u;
  obtain ⟨z', c', hc'⟩ : ∃ z' : V, ∃ c' : (toggled K w'.edges.toFinset).Walk z' z', c'.IsCycle ∧ Odd c'.length ∧ c'.support.toFinset = S' := by
    unfold oddCycleSupports at hcon; aesop;
  obtain ⟨y, y', hy, hy', hy''⟩ : ∃ y y' : V, y ≠ y' ∧ y ∈ c'.support ∧ y' ∈ c'.support ∧ (toggled K w'.edges.toFinset).Adj u y ∧ (toggled K w'.edges.toFinset).Adj u y' := by
    apply cycle_two_distinct_nbrs c' hc'.1;
    exact List.mem_toFinset.mp ( hc'.2.2.symm ▸ hpr.1 );
  have h_deg_toggled : (toggled K w'.edges.toFinset).degree u ≥ 3 := by
    have h_deg_toggled : (toggled K w'.edges.toFinset).neighborFinset u ⊇ {pr, y, y'} := by
      simp_all +decide [ Finset.insert_subset_iff ];
    refine' le_trans _ ( Finset.card_mono h_deg_toggled );
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ * ];
    constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff ];
  linarith

/-
Helper for `strict_of_reach` (§6.10.4).  In a trail, the number of edges incident to a vertex has
the parity of the number of walk endpoints equal to it.
-/
lemma walk_incidence_parity
    {G : SimpleGraph V} {a b : V} (w : G.Walk a b) (htrail : w.IsTrail) (v : V) :
    (#{e ∈ w.edges.toFinset | v ∈ e}) % 2
      = ((if v = a then 1 else 0) + (if v = b then 1 else 0)) % 2 := by
  induction' w with a b w ih generalizing v;
  · split_ifs <;> simp +decide [ * ];
  · by_cases hv : v = b <;> by_cases hv' : v = w <;> simp_all +decide [ SimpleGraph.Walk.isTrail_cons ];
    · simp_all +decide [ SimpleGraph.adj_comm ];
    · rw [ Finset.filter_insert ] ; simp +decide [ *, Nat.add_mod ];
      split_ifs <;> simp +decide [ *, add_comm ];
    · rw [ Finset.filter_insert ] ; simp +decide [ *, Nat.add_mod ];
      split_ifs <;> simp +decide;
    · rw [ Finset.filter_insert ] ; aesop

/-
Helper for `strict_of_reach` (§6.10.4, Theorem A).  The start `p` of a maximal alternating walk (a `(1,2)`
vertex) loses net one `K`-edge under the toggle, so its toggled-`K` degree is
≤ 1 (Theorem A's `(k-h)(p) = 1`).
-/
lemma toggled_K_deg_start_le_one
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (hK2 : ∀ v, K.degree v = 2)
    {p q : V} (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    {x' : V} (w' : G.Walk p x') (hmax' : IsMaximalAltWalk G H K w')
    (hlen : 0 < w'.length) (hpx : p ≠ x')
    (hvalid : IsValidToggle G H K w'.edges.toFinset) :
    (toggled K w'.edges.toFinset).degree p ≤ 1 := by
  have hKdeg : (toggled K w'.edges.toFinset).degree p = (K.degree p - #{e ∈ w'.edges.toFinset | e ∈ K.incidenceFinset p}) + #{e ∈ w'.edges.toFinset | e ∈ H.incidenceFinset p} := by
    rw [ SimpleGraph.degree, SimpleGraph.degree ];
    rw [ show ( toggled K w'.edges.toFinset ).neighborFinset p = ( K.neighborFinset p \ Finset.filter ( fun y => s(p, y) ∈ w'.edges.toFinset ) ( K.neighborFinset p ) ) ∪ Finset.filter ( fun y => s(p, y) ∈ w'.edges.toFinset ) ( H.neighborFinset p ) from ?_ ];
    · rw [ Finset.card_union_of_disjoint ];
      · rw [ Finset.card_sdiff ];
        congr! 1;
        · refine' congr_arg _ ( Finset.card_bij ( fun y hy => s(p, y) ) _ _ _ ) <;> simp +decide [ SimpleGraph.incidenceSet ];
          · exact fun a ha₁ ha₂ ha₃ => ⟨ ha₂, ha₃ ⟩;
          · lia;
          · intro b hb hbK hp; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
            rcases hp with ( rfl | rfl ) <;> simp_all +decide [ SimpleGraph.adj_comm ];
            · exact ⟨ v, ⟨ ⟨ hbK, by simpa only [ Sym2.eq_swap ] using hb ⟩, hbK ⟩, Or.inl rfl ⟩;
            · exact ⟨ u, ⟨ ⟨ hbK, by simpa only [ Sym2.eq_swap ] using hb ⟩, hbK ⟩, Or.inr rfl ⟩;
        · refine' Finset.card_bij ( fun y hy => s(p, y) ) _ _ _ <;> simp +decide [ SimpleGraph.incidenceSet ];
          · exact fun a ha ha' => ⟨ ha', ha ⟩;
          · grind +qlia;
          · intro b hb hbH hp; rcases b with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
            rcases hp with ( rfl | rfl ) <;> simp_all +decide [ SimpleGraph.adj_comm ];
            · exact ⟨ v, ⟨ hbH, by simpa only [ Sym2.eq_swap ] using hb ⟩, Or.inl rfl ⟩;
            · exact ⟨ u, ⟨ hbH, by simpa only [ Sym2.eq_swap ] using hb ⟩, Or.inr rfl ⟩;
      · simp +contextual [ Finset.disjoint_left ];
    · ext y; simp [toggled];
      by_cases hy : K.Adj p y <;> by_cases hy' : s(p, y) ∈ w'.edges <;> simp +decide [ hy, hy', symmDiff ];
      · have := hsplit.2.1; simp_all +decide [ Finset.disjoint_left ] ;
        exact fun h => this _ _ h hy;
      · exact hy.ne;
      · have := hsplit.1 ( p ) ( y ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
        have := w'.edges_subset_edgeSet hy'; simp_all +decide [ SimpleGraph.adj_comm ] ;
        aesop;
  have hKdeg : (K.degree p - #{e ∈ w'.edges.toFinset | e ∈ K.incidenceFinset p}) + #{e ∈ w'.edges.toFinset | e ∈ H.incidenceFinset p} ≤ 2 := by
    have := hvalid.2; have := this.2.2.2.2.2.1 p; simp_all +decide ;
  have hKdeg : (#{e ∈ w'.edges.toFinset | e ∈ K.incidenceFinset p}) + (#{e ∈ w'.edges.toFinset | e ∈ H.incidenceFinset p}) = #{e ∈ w'.edges.toFinset | p ∈ e} := by
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with e ; simp +decide [ SimpleGraph.incidenceSet ];
      have := hsplit.1;
      rcases e with ⟨ u, v ⟩ ; simp +decide [ this ] ;
      by_cases hu : H.Adj u v <;> by_cases hv : K.Adj u v <;> simp +decide [ hu, hv, this ];
      intro he; have := w'.edges_subset_edgeSet he; simp_all +decide [ SimpleGraph.adj_comm ] ;
    · simp +decide [ Finset.disjoint_left, hsplit.2.1 ];
      intro e he₁ he₂ he₃ he₄; have := hsplit.2.1; simp_all +decide [ SimpleGraph.incidenceSet ] ;
      rcases e with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ] ;
  have hKdeg : (#{e ∈ w'.edges.toFinset | p ∈ e}) % 2 = 1 := by
    have := walk_incidence_parity w' hmax'.1 p; aesop;
  have hKdeg : (#{e ∈ w'.edges.toFinset | e ∈ K.incidenceFinset p}) ≤ K.degree p := by
    exact le_trans ( Finset.card_le_card ( show _ ⊆ K.incidenceFinset p from fun e he => by aesop ) ) ( by simp +decide [ SimpleGraph.card_incidenceFinset_eq_degree ] )
  have hKdeg : (#{e ∈ w'.edges.toFinset | e ∈ H.incidenceFinset p}) ≤ H.degree p := by
    grind;
  grind

/-- LADDER-PIN 12d (§6.10.4 Theorem D).  From a reach witness, a strict valid
toggle exists (the four-shape ledger disjunction; the walk's first `H`-edge is
a `Z`-edge, so the poisoned support is always cut). -/
lemma strict_of_reach
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hS : S ∈ oddCycleSupports H)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
  -- Steer the reach witness per `crossing_selection` (§6.10.2/§6.10.3):
  -- a maximal alternating walk `w'` that cuts the poisoned support `S`, cuts a
  -- second odd component, creates no new odd `K`-support and at most one new
  -- odd `H`-support (the main cycle).
  obtain ⟨x', w', hmax', hcutS, hcut2', hKsub, hHcard⟩ :=
    crossing_selection G H K hconn hdeg hmin ht2 hpq hp3 hq3 hpH hqH hS hK2 hreach
  have hsplit : IsEdgeSplit G H K := hmin.1
  have hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2 :=
    Hfull_of_t2 G H K hdeg hsplit ht2 hpq hp3 hq3
  -- Positive length: the walk cuts `S`, so it has at least one edge.
  have hlen : 0 < w'.length := by
    obtain ⟨e, he, -⟩ := hcutS
    rw [← w'.length_edges]
    exact List.length_pos_of_mem he
  -- Theorem A (`alt_walk_termination`): the walk ends at `q`, and the toggle is valid.
  have hterm := alt_walk_termination G H K hconn hdeg hsplit hpq hp3 hq3 hpH hqH hHfull hK2
      w' hmax' hlen
  have hend : x' = q := hterm.1
  have hpx : p ≠ x' := by rw [hend]; exact hpq
  have hvalid : IsValidToggle G H K w'.edges.toFinset := hterm.2
  refine ⟨w'.edges.toFinset, hvalid, ?_⟩
  -- Cut supports die (Pins2 surgery template, adapted to the toggle).
  have deathH : ∀ S' ∈ oddCycleSupports H, WalkCuts w' S' →
      S' ∉ oddCycleSupports (toggled H w'.edges.toFinset) := fun S' hS' hcut =>
    strict_of_reach_deathH G H K hconn hdeg hsplit hK2 hpq hp3 hq3 hpH hqH
      w' hmax' hvalid S' hS' hcut
  have deathK : ∀ S' ∈ oddCycleSupports K, WalkCuts w' S' → (∃ v ∈ w'.support, v ∉ S') →
      S' ∉ oddCycleSupports (toggled K w'.edges.toFinset) := fun S' hS' hcut hout =>
    strict_of_reach_deathK G H K hconn hdeg hsplit hK2 hpq hp3 hq3 hpH hqH
      w' hmax' hvalid S' hS' hcut hout
  -- The Δω ≤ -1 ledger (§6.10.3 four shapes; §6.10.4 Theorem D).
  show oddCycleCount (toggled H w'.edges.toFinset)
      + oddCycleCount (toggled K w'.edges.toFinset)
      < oddCycleCount H + oddCycleCount K
  simp only [oddCycleCount]
  set aH := oddCycleSupports (toggled H w'.edges.toFinset) with haH
  set aK := oddCycleSupports (toggled K w'.edges.toFinset) with haK
  set bH := oddCycleSupports H with hbH
  set bK := oddCycleSupports K with hbK
  have hSdead : S ∉ aH := deathH S hS hcutS
  have hKle : aK.card ≤ bK.card := Finset.card_le_card hKsub
  have hpart : (aH ∩ bH).card + (aH \ bH).card = aH.card :=
    Finset.card_inter_add_card_sdiff aH bH
  rcases hcut2' with ⟨S', hS'mem, hne, hcutS'⟩ | ⟨S'', hS''mem, hcutS''⟩
  · -- Case A: the second odd component is another odd `H`-cycle `S' ≠ S`.
    have hS'dead : S' ∉ aH := deathH S' hS'mem hcutS'
    have hdisj : Disjoint (aH ∩ bH) ({S, S'} : Finset (Finset V)) := by
      rw [Finset.disjoint_right]; intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact fun h => hSdead (Finset.mem_of_mem_inter_left h)
      · exact fun h => hS'dead (Finset.mem_of_mem_inter_left h)
    have hsub : (aH ∩ bH) ∪ ({S, S'} : Finset (Finset V)) ⊆ bH := by
      apply Finset.union_subset Finset.inter_subset_right
      intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hS
      · exact hS'mem
    have hcardpair : (({S, S'} : Finset (Finset V))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using (Ne.symm hne)),
        Finset.card_singleton]
    have hle : (aH ∩ bH).card + 2 ≤ bH.card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_union_of_disjoint hdisj, hcardpair] at this
    omega
  · -- Case B: the second odd component is an odd `K`-cycle `S''`.
    have hS''dead : S'' ∉ aK := by
      by_cases hpS'' : p ∈ S''
      · -- `p ∈ S''`: if `S''` survived, `p` would lie on a toggled-`K` cycle
        -- (degree 2), but the walk start has toggled-`K` degree ≤ 1.
        intro hmem
        rw [haK] at hmem
        obtain ⟨z, c', hc', -, hsupp'⟩ :
            ∃ z, ∃ c' : (toggled K w'.edges.toFinset).Walk z z,
              c'.IsCycle ∧ Odd c'.length ∧ c'.support.toFinset = S'' := by
          unfold oddCycleSupports at hmem; aesop
        have hpc' : p ∈ c'.support := List.mem_toFinset.mp (hsupp' ▸ hpS'')
        have hdeg2 : (toggled K w'.edges.toFinset).degree p = 2 :=
          degree_eq_two_of_mem_cycle_support _
            (fun v => (hvalid.2).2.2.2.2.2.1 v) hc' hpc'
        have hdeg1 : (toggled K w'.edges.toFinset).degree p ≤ 1 :=
          toggled_K_deg_start_le_one G H K hdeg hsplit hK2 hpq hp3 hq3 hpH hqH
            w' hmax' hlen hpx hvalid
        omega
      · exact deathK S'' hS''mem hcutS'' ⟨p, w'.start_mem_support, hpS''⟩
    have hleH : (aH ∩ bH).card + 1 ≤ bH.card := by
      have hsub : (aH ∩ bH) ∪ ({S} : Finset (Finset V)) ⊆ bH := by
        apply Finset.union_subset Finset.inter_subset_right
        intro a ha; simp only [Finset.mem_singleton] at ha; subst ha; exact hS
      have hdisj : Disjoint (aH ∩ bH) ({S} : Finset (Finset V)) := by
        rw [Finset.disjoint_right]; intro a ha
        simp only [Finset.mem_singleton] at ha; subst ha
        exact fun h => hSdead (Finset.mem_of_mem_inter_left h)
      have := Finset.card_le_card hsub
      rwa [Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at this
    have hleK : aK.card + 1 ≤ bK.card := by
      have hsub : aK ∪ ({S''} : Finset (Finset V)) ⊆ bK := by
        apply Finset.union_subset hKsub
        intro a ha; simp only [Finset.mem_singleton] at ha; subst ha; exact hS''mem
      have hdisj : Disjoint aK ({S''} : Finset (Finset V)) := by
        rw [Finset.disjoint_right]; intro a ha
        simp only [Finset.mem_singleton] at ha; subst ha; exact hS''dead
      have := Finset.card_le_card hsub
      rwa [Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at this
    omega

/-- LADDER-PIN 12d-geo (round 19; §6.10.4 Theorem D with the config-(i)
geometry restored and minimality dropped — D's own content is "a strict valid
toggle exists").  GLUE PROVED — REWIRED 2026-07-13 (Fable SUM-PIN lane) after
the walk-level sum pin was double-falsified: now consumes the TOGGLE-level
selection pin `crossing_selection_toggle_sum` (which RESTORES `hmin` per the
falsifier root-cause analysis; this lemma therefore carries `hmin` again,
callers pass `hmin` instead of `hmin.1`) directly, by pure card
accounting — at least 2 dead original odd supports against at most 1 born
one gives `Δω ≤ −1`.  The former walk-side steps
(`maximal_walk_cuts_poisoned`, `alt_walk_termination`, the death lemmas)
remain proved records feeding the pin's future proof, not this glue.
Consumers (`blocked_world_not_minimal`, `strict_merge_of_blocked`)
unchanged. -/
lemma strict_of_reach_geo
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hreach : ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w) :
    ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
  classical
  obtain ⟨T, hvalid, hdead, hborn⟩ :=
    crossing_selection_toggle_sum G H K hconn hdeg hmin ht2 hpq hp3 hq3 hpH
      hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hreach
  refine ⟨T, hvalid, ?_⟩
  show oddCycleCount (toggled H T) + oddCycleCount (toggled K T)
      < oddCycleCount H + oddCycleCount K
  simp only [oddCycleCount]
  set aH := oddCycleSupports (toggled H T) with haH
  set aK := oddCycleSupports (toggled K T) with haK
  set bH := oddCycleSupports H with hbH
  set bK := oddCycleSupports K with hbK
  have hpartH : (aH ∩ bH).card + (aH \ bH).card = aH.card :=
    Finset.card_inter_add_card_sdiff aH bH
  have hpartK : (aK ∩ bK).card + (aK \ bK).card = aK.card :=
    Finset.card_inter_add_card_sdiff aK bK
  have hpartH' : (bH ∩ aH).card + (bH \ aH).card = bH.card :=
    Finset.card_inter_add_card_sdiff bH aH
  have hpartK' : (bK ∩ aK).card + (bK \ aK).card = bK.card :=
    Finset.card_inter_add_card_sdiff bK aK
  have hHcomm : (aH ∩ bH).card = (bH ∩ aH).card := by rw [Finset.inter_comm]
  have hKcomm : (aK ∩ bK).card = (bK ∩ aK).card := by rw [Finset.inter_comm]
  omega

/-- PROVED helper (r4w14_double_visit return).  Each step edge
`s(getVert i, getVert (i+1))` of a walk is an edge of the walk. -/
lemma edge_getVert_mem {G : SimpleGraph V} {u v : V} (w : G.Walk u v) {i : ℕ}
    (h : i < w.length) : s(w.getVert i, w.getVert (i + 1)) ∈ w.edges := by
  induction w generalizing i with
  | nil => simp at h
  | @cons a b c hab p ih =>
    cases i with
    | zero => simp [SimpleGraph.Walk.getVert_zero]
    | succ n =>
      simp only [SimpleGraph.Walk.length_cons] at h
      have hn : n < p.length := by omega
      simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.edges_cons,
        List.mem_cons]
      exact Or.inr (ih hn)

/-
Helper for Lemma G (the X-cut lever; r4w14_double_visit return).  A maximal
alternating walk that visits any vertex `x` of an odd `K`-support `X` in fact
cuts `X`: `x`'s `K`-edges are the two cycle edges (degree exactly 2), whose far
endpoints stay in `X`; at any occurrence of `x` the walk uses one such `K`-edge
— an interior occurrence exposes an even (i.e. `K`) step, the terminal
occurrence in even length is forced by maximality, and in odd length its
incoming step is a `K`-step.  Either way a `K`-edge inside `X` is used.
-/
lemma walkCuts_of_mem_support_oddK
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {X : Finset V} (hX : X ∈ oddCycleSupports K)
    {x : V} (hx : x ∈ X)
    {p y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    (hxsupp : x ∈ w.support) :
    WalkCuts w X := by
  -- By definition of `oddCycleSupports`, there exists an odd cycle `c` in `K` such that `c.support.toFinset = X`.
  obtain ⟨a, c, hc⟩ : ∃ a : V, ∃ c : K.Walk a a, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = X := by
    unfold oddCycleSupports at hX; aesop;
  obtain ⟨j, hj⟩ : ∃ j, w.getVert j = x ∧ j ≤ w.length := by
    rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hxsupp ; aesop;
  have h_closure : ∀ n, K.Adj x n → n ∈ X := by
    intro n hn; have := cycle_support_closed_adj K ( show ∀ v, K.degree v ≤ 2 from hsplit.2.2.2.2.2.1 ) hc.1 ( show x ∈ c.support from by aesop ) hn; aesop;
  by_cases hj_even : j % 2 = 0;
  · by_cases hj_lt : j < w.length;
    · have := hmax.2.1 j hj_lt;
      exact ⟨ s(w.getVert j, w.getVert (j + 1)), edge_getVert_mem w hj_lt, by aesop ⟩;
    · have h_deg : K.degree x = 2 := by
        apply degree_eq_two_of_mem_cycle_support K (hsplit.2.2.2.2.2.1) hc.1;
        exact List.mem_toFinset.mp ( hc.2.2.symm ▸ hx );
      obtain ⟨n, hn⟩ : ∃ n, K.Adj x n := by
        contrapose! h_deg; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      have := hmax.2.2 n; simp_all +decide [ Nat.even_iff ] ;
      have h_y_eq_x : y = x := by
        rw [ ← hj.1, show j = w.length from le_antisymm hj.2 hj_lt ] ; simp +decide [ SimpleGraph.Walk.getVert_length ] ;
      exact ⟨ _, this.1 ( by omega ) ( by simpa [ h_y_eq_x ] using hn ) |> fun h => h, fun v hv => by aesop ⟩;
  · have h_edge : K.Adj (w.getVert (j - 1)) x := by
      have := hmax.2.1 ( j - 1 ) ( by omega ) ; simp_all +decide [ Nat.even_iff ] ;
      grind;
    have h_edge_mem : s(w.getVert (j - 1), x) ∈ w.edges := by
      convert edge_getVert_mem w ( show j - 1 < w.length from _ ) using 1;
      · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by aesop_cat ) ), hj.1 ];
      · omega;
    use s(w.getVert (j - 1), x);
    simp_all +decide [ Sym2.mem_iff ];
    exact h_closure _ h_edge.symm

set_option maxHeartbeats 1000000 in
/-- Helper for Lemma G (double-visit accounting; r4w14_double_visit return).  A
maximal alternating trail that visits a degree-4 vertex `u` (H-adjacent to `x`)
twice uses BOTH of `u`'s two `H`-edges, in particular `s(u, x)`, PROVIDED `u`
is not the walk's start `p`.  Each occurrence in the support other than the
start contributes an incident `H`-step edge (interior occurrences via their odd
step, the terminal occurrence via maximality); two such `H`-edges are distinct
(trail) and exhaust `u`'s two `H`-edges (`H.degree u = 2`). -/
lemma double_visit_uses_H_edge
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {u x : V} (hux : H.Adj u x) (hu4 : G.degree u = 4)
    {p y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    (hup : u ≠ p)
    (hvisit : 2 ≤ w.support.count u) :
    s(u, x) ∈ w.edges := by
  -- By assumption, $u$ appears at least twice in the support of $w$.
  obtain ⟨i₁, i₂, hi₁, hi₂, hlt⟩ : ∃ i₁ i₂, 1 ≤ i₁ ∧ i₁ < i₂ ∧ i₂ ≤ w.length ∧ w.getVert i₁ = u ∧ w.getVert i₂ = u := by
    obtain ⟨i₁, i₂, hi₁, hi₂, hlt⟩ : ∃ i₁ i₂, i₁ < i₂ ∧ i₁ ∈ List.range (w.length + 1) ∧ i₂ ∈ List.range (w.length + 1) ∧ w.getVert i₁ = u ∧ w.getVert i₂ = u := by
      have h_support : List.count u w.support = Finset.card (Finset.filter (fun i => w.getVert i = u) (Finset.range (w.length + 1))) := by
        rw [ show w.support = List.map ( fun i => w.getVert i ) ( List.range ( w.length + 1 ) ) from ?_ ];
        · simp +decide [ List.count, List.filter_eq ];
          rw [ List.countP_eq_length_filter ] ; aesop;
        · refine' List.ext_get _ _ <;> simp +decide [ List.get ];
          grind +suggestions;
      obtain ⟨ i₁, hi₁, i₂, hi₂, hij ⟩ := Finset.one_lt_card.mp ( by linarith ) ; cases lt_trichotomy i₁ i₂ <;> aesop;
    cases i₁ <;> aesop;
  -- By assumption, $u$ has exactly two $H$-neighbors.
  have h_deg_u : (H.neighborFinset u).card = 2 := by
    have := hsplit.2.2.2.2.1 u; have := hsplit.2.2.2.2.2.1 u; have := hsplit.2.2.2.2.2.2 u; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
    linarith;
  -- Let $x'$ be the other $H$-neighbor of $u$.
  obtain ⟨x', hx'⟩ : ∃ x', x' ≠ x ∧ H.Adj u x' ∧ ∀ y, H.Adj u y → y = x ∨ y = x' := by
    obtain ⟨ x', hx' ⟩ := Finset.exists_mem_ne ( by linarith ) x; use x'; simp_all +decide [ SimpleGraph.neighborFinset ] ;
    intro y hy; have := Finset.card_eq_two.mp h_deg_u; obtain ⟨ a, b, hab ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
    grind;
  by_cases h0 : s(u, x) ∉ w.edges <;> simp_all +decide [ IsMaximalAltWalk ];
  -- For each $i$ where $w.getVert i = u$ and $1 \leq i$, there exists a unique $j$ such that $j$ is odd and $s(w.getVert j, w.getVert (j + 1)) = s(u, x')$.
  have h_unique_j : ∀ i, 1 ≤ i → i ≤ w.length → w.getVert i = u → ∃ j, j < w.length ∧ j % 2 = 1 ∧ s(w.getVert j, w.getVert (j + 1)) = s(u, x') ∧ (j = i - 1 ∨ j = i) := by
    intro i hi₁ hi₂ hi₃
    by_cases hi₄ : i < w.length;
    · by_cases hi₅ : i % 2 = 1;
      · have := hmax.2.1 i hi₄; simp_all +decide [ AlternatesKH ] ;
        grind +suggestions;
      · have := hmax.2.1 ( i - 1 ) ( by omega ) ; rcases i with ( _ | i ) <;> simp_all +decide [ Nat.add_mod ] ;
        cases Nat.mod_two_eq_zero_or_one i <;> simp_all +decide only [Nat.mod_mod];
        cases hx'.2.2 _ ( this.2 trivial |> SimpleGraph.Adj.symm ) <;> simp_all +decide [ SimpleGraph.adj_comm ];
        · have := edge_getVert_mem w ( by linarith : i < w.length ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
          exact False.elim ( h0 ( by simpa only [ Sym2.eq_swap ] using this ) );
        · exact ⟨ i, hi₂, by assumption, Or.inr ⟨ by assumption, by assumption ⟩, Or.inl rfl ⟩;
    · cases hi₂.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      rcases Nat.even_or_odd' w.length with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
      have := hmax.2.1 ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, Nat.add_mod, Nat.mul_mod ] ;
      simp_all +decide [ show w.getVert ( 2 * k + 2 ) = u from by { rw [ show w.getVert ( 2 * k + 2 ) = y from by { rw [ show 2 * k + 2 = w.length from by linarith ] ; simp +decide [ SimpleGraph.Walk.getVert_length ] } ] ; simp +decide [ hi₃ ] } ];
      cases hx'.2.2 _ this.symm <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · have := edge_getVert_mem w ( show 2 * k + 1 < w.length from by linarith ) ; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
        grind +suggestions;
      · grind +suggestions;
  obtain ⟨ j₁, hj₁, hj₁', hj₁'', hj₁''' ⟩ := h_unique_j i₁ hi₁ ( by linarith ) hlt.2.1
  obtain ⟨ j₂, hj₂, hj₂', hj₂'', hj₂''' ⟩ := h_unique_j i₂ ( by linarith ) ( by linarith ) hlt.2.2
  have h_distinct : j₁ ≠ j₂ := by
    have h_contradiction : w.getVert (j₁ + 1) ≠ w.getVert (j₁) := by
      intro h; have := hmax.2.1 j₁; simp_all +decide [ AlternatesKH ] ;
    grind +splitIndPred
  have h_contradiction : s(w.getVert j₁, w.getVert (j₁ + 1)) = s(u, x') ∧ s(w.getVert j₂, w.getVert (j₂ + 1)) = s(u, x') := by
    exact ⟨ hj₁'', hj₂'' ⟩
  have h_nodup : List.Nodup w.edges := by
    exact hmax.1.edges_nodup
  have h_contradiction : List.count (s(u, x')) w.edges ≥ 2 := by
    have h_contradiction : List.count (s(u, x')) w.edges ≥ List.count (s(u, x')) (List.map (fun i => s(w.getVert i, w.getVert (i + 1))) (List.range w.length)) := by
      rw [ show w.edges = List.map ( fun i => s(w.getVert i, w.getVert ( i + 1 ) ) ) ( List.range w.length ) from ?_ ];
      refine' List.ext_get _ _ <;> simp +decide [ List.get ];
      grind +suggestions;
    refine' le_trans _ h_contradiction;
    rw [ List.count ] ; simp +decide [ List.count ] ; (
    rw [ List.countP_eq_length_filter ];
    refine' le_trans _ ( List.toFinset_card_le _ );
    refine' Finset.one_lt_card.mpr ⟨ j₁, _, j₂, _, _ ⟩ <;> simp_all +decide [ Function.comp ]);
  exact absurd h_contradiction (by
  grind +revert)

/-- Faithful, sorry-free form of §6.10.5 Lemma G (the interior double-visit that
the informal argument actually describes; r4w14_double_visit return).  Identical
to `double_visit_exhaustion` but stated over `hsplit` alone, with the extra
hypothesis `hup : u ≠ p` ruling out the one corner where the plain statement
fails — namely a double visit anchored at the walk's OWN start, where the start
occurrence consumes a `K`-germ rather than an `H`-germ.  In every application
`u` has degree 4 while the walk starts at a degree-3 endpoint `p`, so `u ≠ p`
is automatic and this is the operative statement. -/
lemma double_visit_exhaustion_of_ne_start
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p : V} {X : Finset V} (hX : X ∈ oddCycleSupports K)
    {u x : V} (hx : x ∈ X) (hux : H.Adj u x) (hu4 : G.degree u = 4)
    {y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    (hup : u ≠ p)
    (hvisit : 2 ≤ w.support.count u) :
    WalkCuts w X := by
  have husupp : u ∈ w.support := List.count_pos_iff.mp (by omega)
  by_cases huX : u ∈ X
  · -- `u` itself is a support vertex that the walk visits: the X-cut lever applies.
    exact walkCuts_of_mem_support_oddK G H K hsplit hX huX w hmax husupp
  · -- The second (interior/terminal) visit forces the H-edge `s(u, x)`, delivering the
    -- walk to `x ∈ X`, whence the X-cut lever again applies.
    have hedge : s(u, x) ∈ w.edges :=
      double_visit_uses_H_edge G H K hsplit hux hu4 w hmax hup hvisit
    exact walkCuts_of_mem_support_oddK G H K hsplit hX hx w hmax
      (w.snd_mem_support_of_mem_edges hedge)

/-- LADDER-PIN 12g (§6.10.5 Lemma G — double-visit exhaustion + the X-cut
lever; round 17).  A second visit to a degree-4 vertex uses all four of its
edges; hence a maximal walk that visits twice a vertex `H`-adjacent to an
uncut odd `K`-support has in fact cut that support (the walk is delivered to
the support vertex in `K`-demand, where only fresh support germs exist).

CORRECTED STATEMENT (r4w14_double_visit gate + pin-correction lane,
2026-07-12).  The original statement is FALSE in the corner `u = p ∧ u ∉ X`:
a maximal alternating trail may revisit its OWN start `p`, consuming both of
`p`'s `K`-germs (the birth step and the even-step return) plus one `H`-edge,
while leaving `s(p, x)` unused and avoiding `X` entirely —
`IsMaximalAltWalk` constrains only the terminal vertex, never the start, and
the start occurrence consumes a `K`-germ rather than an `H`-germ.  The
corrected statement adds `hup : u ≠ p`, which is automatic at the sole live
call site (`reach_of_navchar`: there `G.degree u = 4` while the walk starts
at the degree-3 endpoint `p`, `hp3`).  The original (unprovable) statement is
retained, commented out, immediately below. -/
lemma double_visit_exhaustion
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p : V} {X : Finset V} (hX : X ∈ oddCycleSupports K)
    {u x : V} (hx : x ∈ X) (hux : H.Adj u x) (hu4 : G.degree u = 4)
    {y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    (hup : u ≠ p)
    (hvisit : 2 ≤ w.support.count u) :
    WalkCuts w X :=
  double_visit_exhaustion_of_ne_start G H K hsplit hX hx hux hu4 w hmax hup hvisit

/- ORIGINAL LADDER-PIN 12g STATEMENT — FALSE as literally stated in the corner
`u = p ∧ u ∉ X` (see the correction note on `double_visit_exhaustion` above and
TRIAGE-W12-15.md, r4w14_double_visit addendum); retained verbatim, commented
out, rather than deleted.

lemma double_visit_exhaustion_ORIGINAL
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p : V} {X : Finset V} (hX : X ∈ oddCycleSupports K)
    {u x : V} (hx : x ∈ X) (hux : H.Adj u x) (hu4 : G.degree u = 4)
    {y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    (hvisit : 2 ≤ w.support.count u) :
    WalkCuts w X := by
  sorry
-/

/-- LADDER-PIN 12i (§6.10.6 Lemma I, anchor obstruction analysis; p-side —
the q-side is the same statement in the from-`q` tree).  An `(p, H-demand)`
attainment is necessarily an unforced strict mid-walk anchor return, arriving
via the second `K`-germ: nothing else can host it, and no non-anchor (deg-4)
pair requires such an event (Theorem A(1) accounting). -/
lemma anchor_obstruction_analysis
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {p q : V} (hpq : p ≠ q)
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2)
    (hK2 : ∀ v, K.degree v = 2)
    {y : V} (w : G.Walk p y) (hmax : IsMaximalAltWalk G H K w)
    {i : ℕ} (hi : i ≤ w.length) (hat : w.getVert i = p) (hph : i % 2 = 1) :
    0 < i ∧ i < w.length ∧ K.Adj (w.getVert (i - 1)) p ∧
      s(w.getVert (i - 1), p) ≠ s(p, w.getVert 1) := by
  -- Unpack the maximal-walk structure: a trail, alternating from `K`, maximal.
  obtain ⟨htrail, halt, hend⟩ := hmax
  -- The arrival position is odd, so it is positive (`i = 0` is the `K`-birth).
  have hi0 : 0 < i := by omega
  have hlen0 : 0 < w.length := lt_of_lt_of_le hi0 hi
  -- The birth step is a `K`-edge `p → w.getVert 1`, so `w.getVert 1 ≠ p`.
  have hstep0 : K.Adj (w.getVert 0) (w.getVert 1) := (halt 0 hlen0).1 rfl
  rw [w.getVert_zero] at hstep0
  have hv1 : w.getVert 1 ≠ p := fun h => hstep0.ne h.symm
  -- Hence the return is not at position 1 (that would make `w.getVert 1 = p`).
  have hine1 : i ≠ 1 := by intro h; rw [h] at hat; exact hv1 hat
  -- Theorem A (§6.10.1): a maximal walk of positive length ends at `q`.
  have hy : y = q :=
    (alt_walk_termination G H K hconn hdeg hsplit hpq hp3 hq3 hpH hqH hHfull hK2 w
      ⟨htrail, halt, hend⟩ hlen0).1
  -- So the return at `p` is strictly mid-walk: `p ≠ q` rules out `i = w.length`.
  have hlt : i < w.length := by
    rcases lt_or_eq_of_le hi with h | h
    · exact h
    · exfalso
      have hgv : w.getVert i = y := by rw [h]; exact w.getVert_length
      rw [hat] at hgv
      exact hpq (hgv.trans hy)
  -- The arrival step `i-1` is even, hence a `K`-step landing on `p`: arrival via a `K`-germ.
  have hKadj : K.Adj (w.getVert (i - 1)) p := by
    have hstep : K.Adj (w.getVert (i - 1)) (w.getVert ((i - 1) + 1)) :=
      (halt (i - 1) (by omega)).1 (by omega)
    rwa [show i - 1 + 1 = i from by omega, hat] at hstep
  refine ⟨hi0, hlt, hKadj, ?_⟩
  -- Read walk edges off the darts: `w.edges[n] = s(w.getVert n, w.getVert (n+1))`.
  have edgeval : ∀ n : ℕ, ∀ h : n < w.darts.length,
      w.edges[n]'(by rwa [w.length_edges, ← w.length_darts]) =
        s(w.getVert n, w.getVert (n + 1)) := by
    intro n h
    have hmap : w.edges[n]'(by rwa [w.length_edges, ← w.length_darts]) =
        (w.darts[n]'h).edge := by
      simp only [show w.edges = w.darts.map SimpleGraph.Dart.edge from rfl, List.getElem_map]
    rw [hmap, SimpleGraph.Walk.darts_getElem_eq_getVert n h]; rfl
  -- The arrival `K`-edge is the SECOND `K`-germ `k₂`, distinct from the birth germ `k₀`:
  -- were they equal, the trail would repeat the same edge at positions `0` and `i-1`.
  intro heq
  have hd0 : (0 : ℕ) < w.darts.length := by rw [w.length_darts]; exact hlen0
  have hdI : i - 1 < w.darts.length := by rw [w.length_darts]; omega
  have e0 := edgeval 0 hd0
  have eI := edgeval (i - 1) hdI
  rw [w.getVert_zero] at e0
  rw [show i - 1 + 1 = i from by omega, hat] at eI
  have hee : w.edges[i - 1]'(by rwa [w.length_edges, ← w.length_darts]) =
      w.edges[0]'(by rwa [w.length_edges, ← w.length_darts]) := by
    rw [eI, heq, ← e0]
  have := (List.Nodup.getElem_inj_iff htrail.edges_nodup).mp hee
  omega

/-- Reduction step for the even-`C` law.  For a `2`-regular half `K`, if the
connected component of `p` has EVEN cardinality then no odd `K`-cycle passes
through `p` (an odd `K`-cycle fills its whole component, of odd cardinality). -/
lemma no_odd_Kcycle_of_even_component
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK2 : ∀ v, K.degree v = 2) {p : V}
    (hev : Even (K.connectedComponentMk p).supp.ncard) :
    ∀ (x : V) (c : K.Walk x x), c.IsCycle → Odd c.length → p ∉ c.support := by
  classical
  intro x c hc hodd hp
  have hS : c.support.toFinset ∈ oddCycleSupports K := by
    unfold oddCycleSupports
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, c, hc, hodd, rfl⟩
  obtain ⟨comp, hcomp_odd, hcomp_supp⟩ :=
    oddCycleSupport_fills_oddComponent K (fun v => (hK2 v).le) hS
  have hp_comp : p ∈ comp.supp := by
    rw [← hcomp_supp]
    exact_mod_cast (List.mem_toFinset.mpr hp)
  have hcomp_eq : comp = K.connectedComponentMk p := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hp_comp
    exact hp_comp.symm
  rw [hcomp_eq] at hcomp_odd
  exact (Nat.not_even_iff_odd.mpr hcomp_odd) hev

/-
If the `K`-component of `p` has odd cardinality (`K` `2`-regular), then any
`K`-edge `s(p, z)` at `p` lies on an odd `K`-cycle: the odd component is a single
cycle through `p` using both of `p`'s `K`-edges.
-/
lemma edge_mem_odd_cycle_of_component_odd
    (K : SimpleGraph V) [DecidableRel K.Adj] (hK2 : ∀ v, K.degree v = 2)
    {p z : V} (hpz : K.Adj p z)
    (hodd : Odd (K.connectedComponentMk p).supp.ncard) :
    ∃ (x : V) (c : K.Walk x x), c.IsCycle ∧ Odd c.length ∧ s(p, z) ∈ c.edges := by
  -- The component of p is all-degree-2 (hK2), so by `allDeg2_component_oddCycleSupport K (hdeg2c := fun v _ => hK2 v) hodd` there is S ∈ oddCycleSupports K with (↑S : Set V) = (K.connectedComponentMk p).supp.
  obtain ⟨S, hS⟩ : ∃ S : Finset V, S ∈ oddCycleSupports K ∧ (↑S : Set V) = (K.connectedComponentMk p).supp := by
    apply allDeg2_component_oddCycleSupport K (fun v _ => hK2 v) hodd;
  obtain ⟨x, c, hc⟩ : ∃ x : V, ∃ c : K.Walk x x, c.IsCycle ∧ Odd c.length ∧ c.support.toFinset = S := by
    unfold oddCycleSupports at hS; aesop;
  -- Since p ∈ c.support, we need to show s(p,z) ∈ c.edges.
  have hp_in_c : p ∈ c.support := by
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ]
  have hpz_in_c : s(p, z) ∈ c.edges := by
    have hcyc : K.IsCycles := by
      intro v hv
      rw [Set.ncard_eq_toFinset_card']
      have hnf : (K.neighborSet v).toFinset = K.neighborFinset v := by
        simp [SimpleGraph.neighborFinset]
      rw [hnf, SimpleGraph.card_neighborFinset_eq_degree]; exact hK2 v
    have hv : p ∈ c.toSubgraph.verts := c.mem_verts_toSubgraph.mpr hp_in_c
    have hadj : c.toSubgraph.Adj p z := (hc.1.adj_toSubgraph_iff_of_isCycles hcyc hv z).mpr hpz
    rw [← SimpleGraph.Walk.mem_edges_toSubgraph]
    exact (SimpleGraph.Subgraph.mem_edgeSet).mpr hadj
  use x, c;
  exact ⟨ hc.1, hc.2.1, hpz_in_c ⟩

/-- A vertex of degree `2` on a cycle spends both its edges on that cycle: any
neighbour edge `s(z, z')` at a degree-`2` support vertex `z` lies on the cycle. -/
lemma edge_mem_cycle_of_deg2
    (H : SimpleGraph V) [DecidableRel H.Adj] {x : V} (w : H.Walk x x) (hw : w.IsCycle)
    {z z' : V} (hz : z ∈ w.support) (hdeg : H.degree z = 2) (hadj : H.Adj z z') :
    s(z, z') ∈ w.edges := by
  have h2 : (w.toSubgraph.neighborSet z).ncard = 2 := hw.ncard_neighborSet_toSubgraph_eq_two hz
  have hsub : w.toSubgraph.neighborSet z ⊆ H.neighborSet z := w.toSubgraph.neighborSet_subset z
  have hHcard : (H.neighborSet z).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    have hnf : (H.neighborSet z).toFinset = H.neighborFinset z := by simp [SimpleGraph.neighborFinset]
    rw [hnf, SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have heq : w.toSubgraph.neighborSet z = H.neighborSet z :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hHcard, h2]) (Set.toFinite _)
  have hz' : z' ∈ w.toSubgraph.neighborSet z := by rw [heq]; exact hadj
  rw [← SimpleGraph.Walk.mem_edges_toSubgraph]
  exact (SimpleGraph.Subgraph.mem_edgeSet).mpr hz'

/-
Two-cut separation for the anchor cycle.  Deleting the two poison `K`-edges
of one canonical move separates the two triangle endpoints joined by the third
edge, for AT LEAST ONE of the two available moves `M₁₃`/`M₂₃`.  (If `z₁, z₃`
and `z₂, z₃` were BOTH reachable after their respective cuts, then — pushing each
path off the degree-`1` vertex `p` via `reach_avoid_low_deg` — all three of
`z₁, z₂, z₃` would be mutually reachable degree-`1` vertices of the triply-cut
graph, impossible in a max-degree-`≤ 2` graph by
`three_deg_one_not_all_reachable`.)
-/
lemma cycle_two_cut_sep
    (K : SimpleGraph V) [DecidableRel K.Adj] (hK2 : ∀ v, K.degree v = 2)
    {p q z₁ z₂ z₃ : V}
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hz₁z₂ : z₁ ≠ z₂) (hz₃z₁ : z₃ ≠ z₁) (hz₃z₂ : z₃ ≠ z₂)
    (hpz₃ : p ≠ z₃) (hpq : p ≠ q) (hqz₁ : q ≠ z₁) (hqz₂ : q ≠ z₂) :
    ¬ (K.deleteEdges {s(p, z₁), s(q, z₃)}).Reachable z₁ z₃ ∨
    ¬ (K.deleteEdges {s(p, z₂), s(q, z₃)}).Reachable z₂ z₃ := by
  classical
  by_contra! h
  obtain ⟨R1, R2⟩ := h
  have hz₁p : z₁ ≠ p := hpz₁.ne'
  have hz₂p : z₂ ≠ p := hpz₂.ne'
  have hz₃p : z₃ ≠ p := Ne.symm hpz₃
  have hne_qz3_pz1 : ¬ s(q, z₃) = s(p, z₁) := by
    intro hh; rw [Sym2.eq_iff] at hh
    rcases hh with ⟨h1,_⟩ | ⟨h1,_⟩
    · exact hpq h1.symm
    · exact hqz₁ h1
  have hne_qz3_pz2 : ¬ s(q, z₃) = s(p, z₂) := by
    intro hh; rw [Sym2.eq_iff] at hh
    rcases hh with ⟨h1,_⟩ | ⟨h1,_⟩
    · exact hpq h1.symm
    · exact hqz₂ h1
  have hne_pz2_pz1 : ¬ s(p, z₂) = s(p, z₁) := fun hh => hz₁z₂ (Sym2.congr_right.mp hh).symm
  have hR1eq : K.deleteEdges {s(p, z₁), s(q, z₃)}
      = (K.deleteEdges {s(p,z₁)}).deleteEdges {s(q,z₃)} := by
    rw [SimpleGraph.deleteEdges_deleteEdges, Set.insert_eq]
  have hR2eq : K.deleteEdges {s(p, z₂), s(q, z₃)}
      = (K.deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)} := by
    rw [SimpleGraph.deleteEdges_deleteEdges, Set.insert_eq]
  rw [hR1eq] at R1
  rw [hR2eq] at R2
  have hAdj1_qz3 : (K.deleteEdges {s(p,z₁)}).Adj q z₃ :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨hqz₃, by simpa using fun hh => hne_qz3_pz1 hh⟩
  have hAdj2_qz3 : (K.deleteEdges {s(p,z₂)}).Adj q z₃ :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨hqz₃, by simpa using fun hh => hne_qz3_pz2 hh⟩
  have hdeg_p_M1 : ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(q,z₃)}).degree p ≤ 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdj1_qz3 p, degree_deleteEdges_single K p z₁ hpz₁ p,
        if_pos (Or.inl rfl), if_neg (not_or.mpr ⟨hpq, hpz₃⟩), hK2 p]
  have hdeg_p_M2 : ((K.deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).degree p ≤ 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdj2_qz3 p, degree_deleteEdges_single K p z₂ hpz₂ p,
        if_pos (Or.inl rfl), if_neg (not_or.mpr ⟨hpq, hpz₃⟩), hK2 p]
  have R1' : (((K.deleteEdges {s(p,z₁)}).deleteEdges {s(q,z₃)}).deleteEdges {s(p,z₂)}).Reachable z₁ z₃ :=
    reach_avoid_low_deg _ hdeg_p_M1 hz₁p hz₃p R1 (by simp)
  have R2' : (((K.deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).deleteEdges {s(p,z₁)}).Reachable z₂ z₃ :=
    reach_avoid_low_deg _ hdeg_p_M2 hz₂p hz₃p R2 (by simp)
  have hcanon1 : ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(q,z₃)}).deleteEdges {s(p,z₂)}
      = ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)} := by
    rw [SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_deleteEdges,
        SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_deleteEdges]
    congr 1; ext e; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
  have hcanon2 : ((K.deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).deleteEdges {s(p,z₁)}
      = ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)} := by
    rw [SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_deleteEdges,
        SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_deleteEdges]
    congr 1; ext e; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
  rw [hcanon1] at R1'
  rw [hcanon2] at R2'
  have hAdjA : (K.deleteEdges {s(p,z₁)}).Adj p z₂ :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨hpz₂, by simpa using fun hh => hne_pz2_pz1 hh⟩
  have hAdjB : ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).Adj q z₃ := by
    rw [SimpleGraph.deleteEdges_deleteEdges, SimpleGraph.deleteEdges_adj]
    refine ⟨hqz₃, ?_⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨fun hh => hne_qz3_pz1 hh, fun hh => hne_qz3_pz2 hh⟩
  have hdz₁ : (((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).degree z₁ = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjB z₁, degree_deleteEdges_single _ p z₂ hAdjA z₁,
        degree_deleteEdges_single K p z₁ hpz₁ z₁, if_pos (Or.inr rfl),
        if_neg (not_or.mpr ⟨hz₁p, hz₁z₂⟩), if_neg (not_or.mpr ⟨Ne.symm hqz₁, Ne.symm hz₃z₁⟩), hK2 z₁]
  have hdz₂ : (((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).degree z₂ = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjB z₂, degree_deleteEdges_single _ p z₂ hAdjA z₂,
        degree_deleteEdges_single K p z₁ hpz₁ z₂, if_neg (not_or.mpr ⟨hz₂p, Ne.symm hz₁z₂⟩),
        if_pos (Or.inr rfl), if_neg (not_or.mpr ⟨Ne.symm hqz₂, Ne.symm hz₃z₂⟩), hK2 z₂]
  have hdz₃ : (((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).degree z₃ = 1 := by
    rw [degree_deleteEdges_single _ q z₃ hAdjB z₃, degree_deleteEdges_single _ p z₂ hAdjA z₃,
        degree_deleteEdges_single K p z₁ hpz₁ z₃, if_pos (Or.inr rfl),
        if_neg (not_or.mpr ⟨hz₃p, hz₃z₂⟩), if_neg (not_or.mpr ⟨hz₃p, hz₃z₁⟩), hK2 z₃]
  have hle : ∀ v, (((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)}).degree v ≤ 2 := by
    intro v
    have hchain : ((K.deleteEdges {s(p,z₁)}).deleteEdges {s(p,z₂)}).deleteEdges {s(q,z₃)} ≤ K :=
      le_trans (SimpleGraph.deleteEdges_le _)
        (le_trans (SimpleGraph.deleteEdges_le _) (SimpleGraph.deleteEdges_le _))
    have hh := SimpleGraph.degree_le_of_le hchain (v := v)
    rw [hK2 v] at hh; exact hh
  exact three_deg_one_not_all_reachable _ hle hdz₃ hdz₁ hdz₂ hz₃z₁ hz₃z₂ hz₁z₂ R1'.symm R2'.symm

/-- Degree of `G ⊔ edge u w` at a vertex distinct from both endpoints is
unchanged. -/
lemma degree_sup_edge_of_ne (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (v : V)
    (hvu : v ≠ u) (hvw : v ≠ w) [DecidableRel (G ⊔ SimpleGraph.edge u w).Adj] :
    (G ⊔ SimpleGraph.edge u w).degree v = G.degree v := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.degree]; congr 1; ext t
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | ⟨(⟨rfl,_⟩|⟨rfl,_⟩), _⟩)
    · exact h
    · exact absurd rfl hvu
    · exact absurd rfl hvw
  · exact fun h => Or.inl h

/-- Adding a single edge raises a vertex's degree by at most one. -/
lemma degree_sup_edge_le (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (v : V)
    [DecidableRel (G ⊔ SimpleGraph.edge u w).Adj] :
    (G ⊔ SimpleGraph.edge u w).degree v ≤ G.degree v + 1 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.degree]
  have hsub : (G ⊔ SimpleGraph.edge u w).neighborFinset v
      ⊆ insert (if v = u then w else u) (G.neighborFinset v) := by
    intro t ht
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at ht
    rcases ht with h | ⟨h, hne⟩
    · exact Finset.mem_insert_of_mem (by simp [SimpleGraph.mem_neighborFinset, h])
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [if_pos rfl]; exact Finset.mem_insert_self _ _
      · rw [if_neg hne]; exact Finset.mem_insert_self _ _
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) (by simp))

/-- `H`-side count bound for a canonical 3-move.  Toggling the move on the light
half `H` (delete the triangle edge `s(z, z')`, add the two poison edges
`s(z, p'), s(z', q')`) does not raise the odd-cycle count: deleting the odd
triangle edge drops it by one, the first (non-reclosing) add leaves it unchanged,
and the second add raises it by at most one. -/
lemma toggled_H_le
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hHdeg2 : ∀ v, H.degree v ≤ 2)
    {p' q' z z' : V}
    (hpH : H.degree p' = 1) (hqH : H.degree q' = 1)
    (hzdeg : H.degree z = 2) (hz'deg : H.degree z' = 2)
    (hzz' : H.Adj z z')
    (hzp'nH : ¬ H.Adj z p') (hz'q'nH : ¬ H.Adj z' q')
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hodd : Odd w.length) (hzw : z ∈ w.support)
    (hzp'nr : ¬ H.Reachable z p')
    (hp'z : p' ≠ z) (hp'z' : p' ≠ z') (hq'z : q' ≠ z) (hq'z' : q' ≠ z')
    (hp'q' : p' ≠ q') (hzz'2 : z ≠ z') :
    oddCycleCount (toggled H {s(z, p'), s(z, z'), s(z', q')}) ≤ oddCycleCount H := by
  classical
  have hzp'nH' : ¬ H.Adj p' z := fun h => hzp'nH h.symm
  have hz'q'nH' : ¬ H.Adj q' z' := fun h => hz'q'nH h.symm
  have hTeq : toggled H {s(z, p'), s(z, z'), s(z', q')}
      = (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p') ⊔ SimpleGraph.edge z' q' := by
    ext a b
    simp only [toggled, SimpleGraph.fromEdgeSet_adj, Finset.coe_symmDiff, Set.mem_symmDiff,
      Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj, Sym2.eq_iff]
    by_cases hHab : H.Adj a b
    · have hHba : H.Adj b a := hHab.symm
      by_cases h1 : a = z ∧ b = z' ∨ a = z' ∧ b = z <;> aesop
    · have hHba : ¬ H.Adj b a := fun h => hHab h.symm
      by_cases hne : a = b
      · subst hne; simp
      · aesop
  rw [hTeq]
  have hH1le : ∀ v, (H.deleteEdges {s(z,z')}).degree v ≤ 2 := fun v =>
    le_trans (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)) (hHdeg2 v)
  have hH1z : (H.deleteEdges {s(z,z')}).degree z = 1 := by
    have h := degree_deleteEdges_single H z z' hzz' z; rw [if_pos (Or.inl rfl)] at h; omega
  have hH1p' : (H.deleteEdges {s(z,z')}).degree p' = 1 := by
    have h := degree_deleteEdges_single H z z' hzz' p'
    rw [if_neg (not_or.mpr ⟨hp'z, hp'z'⟩)] at h; omega
  have hstep1 : oddCycleCount (H.deleteEdges {s(z,z')}) < oddCycleCount H :=
    oddCycleCount_deleteEdges_lt H hHdeg2 hw hodd hzz' (edge_mem_cycle_of_deg2 H w hw hzw hzdeg hzz')
  have hnr1 : ¬ (H.deleteEdges {s(z,z')}).Reachable z p' :=
    fun hr => hzp'nr (hr.mono (SimpleGraph.deleteEdges_le _))
  have hM'2 : ∀ a b, (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p').Adj a b
      ↔ ((H.deleteEdges {s(z,z')}).Adj a b ∨ (s(a, b) = s(z, p') ∧ a ≠ b)) := by
    intro a b; simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, Sym2.eq_iff]; try tauto
  have hstep2 : oddCycleCount (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p')
      ≤ oddCycleCount (H.deleteEdges {s(z,z')}) :=
    oddCycleCount_addEdge_le _ _ hnr1 hM'2
  have hH2le : ∀ v, (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p').degree v ≤ 2 := by
    intro v
    by_cases hv : v = z ∨ v = p'
    · have h := degree_sup_edge_le (H.deleteEdges {s(z,z')}) (u := z) (w := p') v
      rcases hv with rfl | rfl <;> omega
    · push_neg at hv
      have h := degree_sup_edge_of_ne (H.deleteEdges {s(z,z')}) v hv.1 hv.2
      have h2 := hH1le v; omega
  have hz'le : (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p').degree z' ≤ 1 := by
    have hh := degree_deleteEdges_single H z z' hzz' z'
    rw [if_pos (Or.inr rfl)] at hh
    have h := degree_sup_edge_of_ne (H.deleteEdges {s(z,z')}) z' (Ne.symm hzz'2) (Ne.symm hp'z')
    omega
  have hq'le : (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p').degree q' ≤ 1 := by
    have hh := degree_deleteEdges_single H z z' hzz' q'
    rw [if_neg (not_or.mpr ⟨hq'z, hq'z'⟩)] at hh
    have h := degree_sup_edge_of_ne (H.deleteEdges {s(z,z')}) q' hq'z (Ne.symm hp'q')
    omega
  have hM'3 : ∀ a b, ((H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p') ⊔ SimpleGraph.edge z' q').Adj a b
      ↔ ((H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p').Adj a b ∨ (s(a, b) = s(z', q') ∧ a ≠ b)) := by
    intro a b; simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, Sym2.eq_iff]; try tauto
  have hstep3 : oddCycleCount ((H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p') ⊔ SimpleGraph.edge z' q')
      ≤ oddCycleCount (H.deleteEdges {s(z,z')} ⊔ SimpleGraph.edge z p') + 1 :=
    oddCycleCount_addEdge_le_succ _ _ hH2le hz'le hq'le (Ne.symm hq'z') hM'3
  omega

/-- A degree-`2` vertex on an odd cycle whose support has exactly three vertices
is adjacent (in the ambient graph) to every other support vertex: the triangle
is genuinely a triangle. -/
lemma triangle_of_support3 (H : SimpleGraph V) [DecidableRel H.Adj]
    {x : V} {w : H.Walk x x} (hw : w.IsCycle)
    {a b : V} (ha : a ∈ w.support) (hb : b ∈ w.support) (hab : a ≠ b)
    (hda : H.degree a = 2)
    (hsupp3 : w.support.toFinset.card = 3) : H.Adj a b := by
  classical
  have hcard_w : (w.toSubgraph.neighborSet a).ncard = 2 := hw.ncard_neighborSet_toSubgraph_eq_two ha
  have hcard_H : (H.neighborSet a).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card']
    have hnf : (H.neighborSet a).toFinset = H.neighborFinset a := by simp [SimpleGraph.neighborFinset]
    rw [hnf, SimpleGraph.card_neighborFinset_eq_degree]; exact hda
  have hsubHw : w.toSubgraph.neighborSet a ⊆ H.neighborSet a := w.toSubgraph.neighborSet_subset a
  have heqHw : w.toSubgraph.neighborSet a = H.neighborSet a :=
    Set.eq_of_subset_of_ncard_le hsubHw (by rw [hcard_H, hcard_w]) (Set.toFinite _)
  have hsub : H.neighborSet a ⊆ (↑(w.support.toFinset \ {a}) : Set V) := by
    rw [← heqHw]
    intro t ht
    have htv : t ∈ w.support := by
      have := w.toSubgraph.edge_vert (SimpleGraph.Subgraph.mem_neighborSet ..|>.mp ht).symm
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
    have htne : t ≠ a := fun h => (SimpleGraph.Subgraph.mem_neighborSet ..|>.mp ht).ne (h ▸ rfl)
    simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff, Finset.mem_coe,
      List.mem_toFinset, Set.mem_singleton_iff]
    exact ⟨htv, htne⟩
  have hcardset : ((w.support.toFinset \ {a} : Finset V)).card = 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (List.mem_toFinset.mpr ha), hsupp3]
  have heq2 : H.neighborSet a = (↑(w.support.toFinset \ {a}) : Set V) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hcardset, hcard_H]) (Set.toFinite _)
  have hbmem : b ∈ (↑(w.support.toFinset \ {a}) : Set V) := by
    simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff, Finset.mem_coe,
      List.mem_toFinset, Set.mem_singleton_iff]
    exact ⟨hb, Ne.symm hab⟩
  have hbn : b ∈ H.neighborSet a := heq2.symm ▸ hbmem
  simpa using hbn

/-- `K`-side count strict-drop for a canonical 3-move.  Toggling the move on `K`
(delete the two poison edges `s(z, p'), s(z', q')`, add the triangle edge
`s(z, z')`) STRICTLY lowers the odd-cycle count, provided the two deletions
already strictly lower it and the added edge does not reconnect (`z, z'`
non-reachable after the cuts). -/
lemma toggled_K_lt (K : SimpleGraph V) [DecidableRel K.Adj]
    {p' q' z z' : V}
    (hzp' : K.Adj z p') (hz'q' : K.Adj z' q') (hzz'nK : ¬ K.Adj z z')
    (hstrictdel : oddCycleCount (K.deleteEdges {s(z,p'), s(z',q')}) < oddCycleCount K)
    (hKnr : ¬ (K.deleteEdges {s(z,p'), s(z',q')}).Reachable z z')
    (hzz'2 : z ≠ z') :
    oddCycleCount (toggled K {s(z, p'), s(z, z'), s(z', q')}) < oddCycleCount K := by
  classical
  have hTeq : toggled K {s(z, p'), s(z, z'), s(z', q')}
      = K.deleteEdges {s(z,p'), s(z',q')} ⊔ SimpleGraph.edge z z' := by
    ext a b
    simp only [toggled, SimpleGraph.fromEdgeSet_adj, Finset.coe_symmDiff, Set.mem_symmDiff,
      Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj, Sym2.eq_iff]
    by_cases hKab : K.Adj a b
    · have hKba : K.Adj b a := hKab.symm
      aesop
    · have hKba : ¬ K.Adj b a := fun h => hKab h.symm
      by_cases hne : a = b
      · subst hne; simp
      · aesop
  rw [hTeq]
  have hM' : ∀ a b, (K.deleteEdges {s(z,p'), s(z',q')} ⊔ SimpleGraph.edge z z').Adj a b
      ↔ ((K.deleteEdges {s(z,p'), s(z',q')}).Adj a b ∨ (s(a, b) = s(z, z') ∧ a ≠ b)) := by
    intro a b; simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, Sym2.eq_iff]; try tauto
  exact lt_of_le_of_lt (oddCycleCount_addEdge_le _ _ hKnr hM') hstrictdel

/-- A single canonical 3-move `M = {s(z,p), s(z,z'), s(z',q)}` cannot exist at a
minimal split once its `H`-side does not raise the odd-cycle count and its
`K`-side strictly lowers it: minimality is contradicted. -/
lemma move_contra
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (hHdeg2 : ∀ v, H.degree v ≤ 2)
    {p q z z' : V}
    (hzz' : H.Adj z z') (hzp : K.Adj z p) (hz'q : K.Adj z' q)
    (hz4 : G.degree z = 4) (hz'4 : G.degree z' = 4)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1) (hpq : p ≠ q)
    (hHz : H.degree z = 2) (hHz' : H.degree z' = 2)
    (hzpnH : ¬ H.Adj z p) (hz'qnH : ¬ H.Adj z' q) (hzz'nK : ¬ K.Adj z z')
    {x : V} {w : H.Walk x x} (hw : w.IsCycle) (hwodd : Odd w.length) (hzw : z ∈ w.support)
    (hzpnr : ¬ H.Reachable z p)
    (hpz : p ≠ z) (hpz' : p ≠ z') (hqz : q ≠ z) (hqz' : q ≠ z') (hzz'2 : z ≠ z')
    (hstrictdel : oddCycleCount (K.deleteEdges {s(z,p), s(z',q)}) < oddCycleCount K)
    (hKnr : ¬ (K.deleteEdges {s(z,p), s(z',q)}).Reachable z z') : False := by
  have hHle := toggled_H_le H hHdeg2 hpH hqH hHz hHz' hzz' hzpnH hz'qnH hw hwodd hzw hzpnr
    hpz hpz' hqz hqz' hpq hzz'2
  have hKlt := toggled_K_lt K hzp hz'q hzz'nK hstrictdel hKnr hzz'2
  have hvalid := three_edge_toggle_valid G H K hdeg hmin.1 hzz' hzp hz'q hz4 hz'4 hpH hqH hpq
  have hmin2 := hmin.2 (toggled H {s(z, p), s(z, z'), s(z', q)})
    (toggled K {s(z, p), s(z, z'), s(z', q)}) _ _ hvalid.2
  omega

/-- Crux of the even-`C` law (§6.2 corollary; the deferred debris-linkage
accounting).  In the blocked world `𝔅`, the two anchor `K`-components are of
EVEN cardinality.  From minimality: the canonical 3-move `M₁₃` (or `M₂₃`/`M₁₂`)
is a valid toggle whose `H`-side leaves the odd-cycle count unchanged (the odd
triangle merges with the even `p`–`q` path into one odd cycle of length
`ℓ_P + 4`), while its `K`-side would strictly LOWER the odd-cycle count if
either anchor `K`-cycle were odd (the poison edges cut the anchor cycle(s) into
arcs with no odd reclosure); minimality forbids the drop, forcing both anchor
components even. -/
lemma anchor_component_even
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    Even (K.connectedComponentMk p).supp.ncard ∧
    Even (K.connectedComponentMk q).supp.ncard := by
  classical
  have hsplit := hmin.1
  have hHdeg2 : ∀ v, H.degree v ≤ 2 := hsplit.2.2.2.2.1
  have hHfull := Hfull_of_t2 G H K hdeg hsplit ht2 hpq hp3 hq3
  have hz1S : z₁ ∈ S := by rw [hSeq]; simp
  have hz2S : z₂ ∈ S := by rw [hSeq]; simp
  have hz3S : z₃ ∈ S := by rw [hSeq]; simp
  have hHz1 : H.degree z₁ = 2 := by
    have h := hsplit.2.2.2.2.2.2 z₁; have := hK2 z₁; have := hz4 z₁ hz1S; omega
  have hHz2 : H.degree z₂ = 2 := by
    have h := hsplit.2.2.2.2.2.2 z₂; have := hK2 z₂; have := hz4 z₂ hz2S; omega
  have hHz3 : H.degree z₃ = 2 := by
    have h := hsplit.2.2.2.2.2.2 z₃; have := hK2 z₃; have := hz4 z₃ hz3S; omega
  obtain ⟨xt, wS, hwS_cyc, hwS_odd, hwS_supp⟩ :
      ∃ (x : V) (wS : H.Walk x x), wS.IsCycle ∧ Odd wS.length ∧ wS.support.toFinset = S := by
    have hS' := hS
    unfold oddCycleSupports at hS'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS'; exact hS'
  have hScard : S.card = 3 := by
    have hge := oddCycleSupports_three_le_card H S hS
    have hle : S.card ≤ 3 := by
      rw [hSeq]
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
      simp
    omega
  have hz12 : z₁ ≠ z₂ := by
    rintro rfl
    have hc : ({z₁, z₁, z₃} : Finset V).card = 3 := by rw [← hSeq]; exact hScard
    simp only [Finset.insert_idem] at hc
    have : ({z₁, z₃} : Finset V).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega
  have hz13 : z₁ ≠ z₃ := by
    rintro rfl
    have hc : ({z₁, z₂, z₁} : Finset V).card = 3 := by rw [← hSeq]; exact hScard
    have hsub : ({z₁, z₂, z₁} : Finset V) ⊆ {z₁, z₂} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto
    have : ({z₁, z₂} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    have := Finset.card_le_card hsub; omega
  have hz23 : z₂ ≠ z₃ := by
    rintro rfl
    have hc : ({z₁, z₂, z₂} : Finset V).card = 3 := by rw [← hSeq]; exact hScard
    have hsub : ({z₁, z₂, z₂} : Finset V) ⊆ {z₁, z₂} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto
    have : ({z₁, z₂} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    have := Finset.card_le_card hsub; omega
  have hz1w : z₁ ∈ wS.support := by
    have : z₁ ∈ wS.support.toFinset := by rw [hwS_supp]; exact hz1S
    exact List.mem_toFinset.mp this
  have hz2w : z₂ ∈ wS.support := by
    have : z₂ ∈ wS.support.toFinset := by rw [hwS_supp]; exact hz2S
    exact List.mem_toFinset.mp this
  have hz3w : z₃ ∈ wS.support := by
    have : z₃ ∈ wS.support.toFinset := by rw [hwS_supp]; exact hz3S
    exact List.mem_toFinset.mp this
  have hwScard : wS.support.toFinset.card = 3 := by rw [hwS_supp]; exact hScard
  have hA13 : H.Adj z₁ z₃ := triangle_of_support3 H hwS_cyc hz1w hz3w hz13 hHz1 hwScard
  have hA23 : H.Adj z₂ z₃ := triangle_of_support3 H hwS_cyc hz2w hz3w hz23 hHz2 hwScard
  have hp_z1 : p ≠ z₁ := by intro h; rw [h] at hpH; omega
  have hp_z2 : p ≠ z₂ := by intro h; rw [h] at hpH; omega
  have hp_z3 : p ≠ z₃ := by intro h; rw [h] at hpH; omega
  have hq_z1 : q ≠ z₁ := by intro h; rw [h] at hqH; omega
  have hq_z2 : q ≠ z₂ := by intro h; rw [h] at hqH; omega
  have hq_z3 : q ≠ z₃ := by intro h; rw [h] at hqH; omega
  have hnHA_z1p : ¬ H.Adj z₁ p := fun h => hsplit.2.1 z₁ p h hpz₁.symm
  have hnHA_z2p : ¬ H.Adj z₂ p := fun h => hsplit.2.1 z₂ p h hpz₂.symm
  have hnHA_z3q : ¬ H.Adj z₃ q := fun h => hsplit.2.1 z₃ q h hqz₃.symm
  have hnKA_z1z3 : ¬ K.Adj z₁ z₃ := hsplit.2.1 z₁ z₃ hA13
  have hnKA_z2z3 : ¬ K.Adj z₂ z₃ := hsplit.2.1 z₂ z₃ hA23
  -- H-side non-reachability via component parity
  obtain ⟨w0, hw0path, hw0odd⟩ := hPodd
  have hspan := path_support_eq_component H hpH hqH hHfull hw0path
  have hPeven : Even (H.connectedComponentMk p).supp.ncard := by
    have hc : (H.connectedComponentMk p).supp.ncard = w0.support.toFinset.card := by
      rw [← hspan, Set.ncard_coe_finset]
    rw [hc, List.toFinset_card_of_nodup hw0path.support_nodup, SimpleGraph.Walk.length_support]
    rcases hw0odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  obtain ⟨cZ, hcZodd, hcZsupp⟩ := oddCycleSupport_fills_oddComponent H hHdeg2 hS
  have hZ1odd : Odd (H.connectedComponentMk z₁).supp.ncard := by
    have hmem : z₁ ∈ cZ.supp := by rw [← hcZsupp]; exact_mod_cast hz1S
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hmem; rw [hmem]; exact hcZodd
  have hZ2odd : Odd (H.connectedComponentMk z₂).supp.ncard := by
    have hmem : z₂ ∈ cZ.supp := by rw [← hcZsupp]; exact_mod_cast hz2S
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hmem; rw [hmem]; exact hcZodd
  have hnr_z1p : ¬ H.Reachable z₁ p := by
    intro hr
    have := SimpleGraph.ConnectedComponent.sound hr
    rw [this] at hZ1odd; exact (Nat.not_even_iff_odd.mpr hZ1odd) hPeven
  have hnr_z2p : ¬ H.Reachable z₂ p := by
    intro hr
    have := SimpleGraph.ConnectedComponent.sound hr
    rw [this] at hZ2odd; exact (Nat.not_even_iff_odd.mpr hZ2odd) hPeven
  -- helper: strict K deletion for a chosen odd anchor edge
  by_cases hcompeq : K.connectedComponentMk p = K.connectedComponentMk q
  · -- p and q share a K-component; prove that component even
    have hkey : Even (K.connectedComponentMk p).supp.ncard := by
      by_contra hoddc
      rw [Nat.not_even_iff_odd] at hoddc
      have hsep := cycle_two_cut_sep K hK2 hpz₁ hpz₂ hqz₃ hz12 (Ne.symm hz13) (Ne.symm hz23)
        hp_z3 hpq hq_z1 hq_z2
      rcases hsep with h13 | h23
      · -- move M₁₃
        have hKnr : ¬ (K.deleteEdges {s(z₁, p), s(z₃, q)}).Reachable z₁ z₃ := by
          rw [show (s(z₁, p) : Sym2 V) = s(p, z₁) from Sym2.eq_swap,
              show (s(z₃, q) : Sym2 V) = s(q, z₃) from Sym2.eq_swap]
          exact h13
        have hstrictdel : oddCycleCount (K.deleteEdges {s(z₁, p), s(z₃, q)}) < oddCycleCount K := by
          obtain ⟨xc, c, hc_cyc, hc_odd, hc_edge⟩ := edge_mem_odd_cycle_of_component_odd K hK2 hpz₁ hoddc
          have he : s(z₁, p) ∈ c.edges := by rw [Sym2.eq_swap]; exact hc_edge
          have hlt : oddCycleCount (K.deleteEdges {s(z₁, p)}) < oddCycleCount K :=
            oddCycleCount_deleteEdges_lt K (fun v => (hK2 v).le) hc_cyc hc_odd hpz₁.symm he
          have hset : K.deleteEdges {s(z₁, p), s(z₃, q)}
              = (K.deleteEdges {s(z₁, p)}).deleteEdges {s(z₃, q)} := by
            rw [SimpleGraph.deleteEdges_deleteEdges, Set.insert_eq]
          rw [hset]; exact lt_of_le_of_lt (oddCycleCount_deleteEdges_le _ _) hlt
        exact move_contra G H K hdeg hmin hHdeg2 hA13 hpz₁.symm hqz₃.symm (hz4 z₁ hz1S)
          (hz4 z₃ hz3S) hpH hqH hpq hHz1 hHz3 hnHA_z1p hnHA_z3q hnKA_z1z3 hwS_cyc hwS_odd hz1w
          hnr_z1p hp_z1 hp_z3 hq_z1 hq_z3 hz13 hstrictdel hKnr
      · -- move M₂₃
        have hKnr : ¬ (K.deleteEdges {s(z₂, p), s(z₃, q)}).Reachable z₂ z₃ := by
          rw [show (s(z₂, p) : Sym2 V) = s(p, z₂) from Sym2.eq_swap,
              show (s(z₃, q) : Sym2 V) = s(q, z₃) from Sym2.eq_swap]
          exact h23
        have hstrictdel : oddCycleCount (K.deleteEdges {s(z₂, p), s(z₃, q)}) < oddCycleCount K := by
          obtain ⟨xc, c, hc_cyc, hc_odd, hc_edge⟩ := edge_mem_odd_cycle_of_component_odd K hK2 hpz₂ hoddc
          have he : s(z₂, p) ∈ c.edges := by rw [Sym2.eq_swap]; exact hc_edge
          have hlt : oddCycleCount (K.deleteEdges {s(z₂, p)}) < oddCycleCount K :=
            oddCycleCount_deleteEdges_lt K (fun v => (hK2 v).le) hc_cyc hc_odd hpz₂.symm he
          have hset : K.deleteEdges {s(z₂, p), s(z₃, q)}
              = (K.deleteEdges {s(z₂, p)}).deleteEdges {s(z₃, q)} := by
            rw [SimpleGraph.deleteEdges_deleteEdges, Set.insert_eq]
          rw [hset]; exact lt_of_le_of_lt (oddCycleCount_deleteEdges_le _ _) hlt
        exact move_contra G H K hdeg hmin hHdeg2 hA23 hpz₂.symm hqz₃.symm (hz4 z₂ hz2S)
          (hz4 z₃ hz3S) hpH hqH hpq hHz2 hHz3 hnHA_z2p hnHA_z3q hnKA_z2z3 hwS_cyc hwS_odd hz2w
          hnr_z2p hp_z2 hp_z3 hq_z2 hq_z3 hz23 hstrictdel hKnr
    exact ⟨hkey, by rw [← hcompeq]; exact hkey⟩
  · -- distinct K-components: each anchor even
    -- shared non-reachability of z₁, z₃ after the M₁₃ cut
    have hKnr : ¬ (K.deleteEdges {s(z₁, p), s(z₃, q)}).Reachable z₁ z₃ := by
      intro hr
      have hK : K.Reachable z₁ z₃ := hr.mono (SimpleGraph.deleteEdges_le _)
      have h1 : K.connectedComponentMk z₁ = K.connectedComponentMk z₃ :=
        SimpleGraph.ConnectedComponent.sound hK
      have hpz1r : K.connectedComponentMk z₁ = K.connectedComponentMk p :=
        SimpleGraph.ConnectedComponent.sound hpz₁.symm.reachable
      have hqz3r : K.connectedComponentMk z₃ = K.connectedComponentMk q :=
        SimpleGraph.ConnectedComponent.sound hqz₃.symm.reachable
      exact hcompeq (hpz1r.symm.trans (h1.trans hqz3r))
    refine ⟨?_, ?_⟩
    · by_contra hoddP; rw [Nat.not_even_iff_odd] at hoddP
      have hstrictdel : oddCycleCount (K.deleteEdges {s(z₁, p), s(z₃, q)}) < oddCycleCount K := by
        obtain ⟨xc, c, hc_cyc, hc_odd, hc_edge⟩ := edge_mem_odd_cycle_of_component_odd K hK2 hpz₁ hoddP
        have he : s(z₁, p) ∈ c.edges := by rw [Sym2.eq_swap]; exact hc_edge
        have hlt : oddCycleCount (K.deleteEdges {s(z₁, p)}) < oddCycleCount K :=
          oddCycleCount_deleteEdges_lt K (fun v => (hK2 v).le) hc_cyc hc_odd hpz₁.symm he
        have hset : K.deleteEdges {s(z₁, p), s(z₃, q)}
            = (K.deleteEdges {s(z₁, p)}).deleteEdges {s(z₃, q)} := by
          rw [SimpleGraph.deleteEdges_deleteEdges, Set.insert_eq]
        rw [hset]; exact lt_of_le_of_lt (oddCycleCount_deleteEdges_le _ _) hlt
      exact move_contra G H K hdeg hmin hHdeg2 hA13 hpz₁.symm hqz₃.symm (hz4 z₁ hz1S)
        (hz4 z₃ hz3S) hpH hqH hpq hHz1 hHz3 hnHA_z1p hnHA_z3q hnKA_z1z3 hwS_cyc hwS_odd hz1w
        hnr_z1p hp_z1 hp_z3 hq_z1 hq_z3 hz13 hstrictdel hKnr
    · by_contra hoddQ; rw [Nat.not_even_iff_odd] at hoddQ
      have hstrictdel : oddCycleCount (K.deleteEdges {s(z₁, p), s(z₃, q)}) < oddCycleCount K := by
        obtain ⟨xc, c, hc_cyc, hc_odd, hc_edge⟩ := edge_mem_odd_cycle_of_component_odd K hK2 hqz₃ hoddQ
        have he : s(z₃, q) ∈ c.edges := by rw [Sym2.eq_swap]; exact hc_edge
        have hlt : oddCycleCount (K.deleteEdges {s(z₃, q)}) < oddCycleCount K :=
          oddCycleCount_deleteEdges_lt K (fun v => (hK2 v).le) hc_cyc hc_odd hqz₃.symm he
        have hset : K.deleteEdges {s(z₁, p), s(z₃, q)}
            = (K.deleteEdges {s(z₃, q)}).deleteEdges {s(z₁, p)} := by
          rw [SimpleGraph.deleteEdges_deleteEdges]; congr 1; ext e
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
        rw [hset]; exact lt_of_le_of_lt (oddCycleCount_deleteEdges_le _ _) hlt
      exact move_contra G H K hdeg hmin hHdeg2 hA13 hpz₁.symm hqz₃.symm (hz4 z₁ hz1S)
        (hz4 z₃ hz3S) hpH hqH hpq hHz1 hHz3 hnHA_z1p hnHA_z3q hnKA_z1z3 hwS_cyc hwS_odd hz1w
        hnr_z1p hp_z1 hp_z3 hq_z1 hq_z3 hz13 hstrictdel hKnr

/-- LADDER-PIN 12j-even (§6.2 corollary; the "even-C" law in the blocked
world `𝔅`).  In `𝔅` — a minimal split of a `t ≤ 2` graph in poisoned
configuration (i): an odd `H`-triangle `S = {z₁, z₂, z₃}` of degree-4
vertices, degree-3 `H`-light path-ends `p, q`, `K` 2-regular, and `ℓ_P` odd —
each anchor's `K`-cycle is EVEN.  Equivalently, no odd `K`-cycle passes
through `p` or through `q`.  (STRIKE-A §6.2 Corollary: were an anchor's
`K`-cycle odd, the `ε_K ≥ d_K` accounting would make a canonical 3-move
strict, contradicting `hmin`.  This is the fact Lemma J(i) cites; it is
separated out here as the direct dependency of `supply_avoids_anchors`.) -/
lemma anchor_Kcycle_even
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    (∀ (x : V) (c : K.Walk x x), c.IsCycle → Odd c.length → p ∉ c.support) ∧
    (∀ (x : V) (c : K.Walk x x), c.IsCycle → Odd c.length → q ∉ c.support) := by
  obtain ⟨hp_even, hq_even⟩ :=
    anchor_component_even G H K hconn hdeg hmin ht2 hpq hp3 hq3 hpH hqH hSeq hS hz4
      hpz₁ hpz₂ hqz₃ hvar hK2 hPodd
  exact ⟨no_odd_Kcycle_of_even_component K hK2 hp_even,
         no_odd_Kcycle_of_even_component K hK2 hq_even⟩

/-- LADDER-PIN 12j (§6.10.6 Lemma J, disjointness of the needed object).  In
the blocked world the supply avoids the anchors: an odd `K`-support contains
neither `p` nor `q` (each anchor's `K`-cycle is EVEN by the §6.2 corollary,
while the supply is odd).  Hence every supply vertex is deg-4 and the needed
visit/second-visit is never an anchor event. -/
lemma supply_avoids_anchors
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    {X : Finset V} (hX : X ∈ oddCycleSupports K) :
    p ∉ X ∧ q ∉ X := by
  -- The §6.2 even-C law: each anchor's `K`-cycle is even, so no odd
  -- `K`-cycle passes through `p` or `q`.
  obtain ⟨heven_p, heven_q⟩ := anchor_Kcycle_even G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hPodd
  -- Unpack the odd `K`-cycle whose support is `X`.
  unfold oddCycleSupports at hX
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
  obtain ⟨x, c, hcyc, hodd, hsupp⟩ := hX
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · rw [← hsupp] at hp
    exact heven_p x c hcyc hodd (List.mem_toFinset.mp hp)
  · rw [← hsupp] at hq
    exact heven_q x c hcyc hodd (List.mem_toFinset.mp hq)

/-- LADDER-PIN 12l (§6.10.6 Lemma L, germ-flip — the cycle-relinearization
core).  For an interior vertex `w` of a cycle and ANY germ `s(v, w)` at `w`,
some first-cut edge at `w₀` linearizes the cycle so that the arc from `w₀`
reaches `w` WITHOUT using `s(v, w)` — leaving it as the forced tip-side germ.
(The two `w₀`-germs give the two opposite linearizations; head/tip sides
exchange at every interior vertex, so no germ is "always forbidden".) -/
lemma germ_flip
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg2 : ∀ u, H.degree u ≤ 2)
    {x w₀ w v : V} {c : H.Walk x x} (hc : c.IsCycle)
    (hw₀ : w₀ ∈ c.support) (hw : w ∈ c.support) (hne : w ≠ w₀)
    (hv : H.Adj v w) :
    ∃ e ∈ c.edges, (w₀ ∈ e) ∧
      ∃ P : (H.deleteEdges {e}).Walk w₀ w, P.IsPath ∧ s(v, w) ∉ P.edges := by
  classical
  -- Rotate the cycle to start at `w₀`.
  have hcyc0 : (c.rotate hw₀).IsCycle := hc.rotate hw₀
  have hwc₀ : w ∈ (c.rotate hw₀).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c hw₀).mpr hw
  have hrot : (c.rotate hw₀).edges ~r c.edges := SimpleGraph.Walk.rotate_edges c hw₀
  set c₀ : H.Walk w₀ w₀ := c.rotate hw₀ with hc₀def
  -- Split `c₀` at `w` into the two arcs `pa` (w₀→w) and `pb` (w→w₀).
  set pa : H.Walk w₀ w := c₀.takeUntil w hwc₀ with hpadef
  set pb : H.Walk w w₀ := c₀.dropUntil w hwc₀ with hpbdef
  have hspec : pa.append pb = c₀ := SimpleGraph.Walk.take_spec c₀ hwc₀
  have hpanil : ¬ pa.Nil := fun h => hne h.eq.symm
  have hpbnil : ¬ pb.Nil := fun h => hne h.eq
  have hcyc' : (pa.append pb).IsCycle := by rw [hspec]; exact hcyc0
  have hpa : pa.IsPath := hcyc'.isPath_of_append_left hpbnil
  have hpb : pb.IsPath := hcyc'.isPath_of_append_right hpanil
  -- `c₀`'s edges split as the two disjoint arc-edge-lists.
  have hedges_c0 : c₀.edges = pa.edges ++ pb.edges := by
    rw [← hspec, SimpleGraph.Walk.edges_append]
  have hnodup : (pa.edges ++ pb.edges).Nodup := by
    rw [← hedges_c0]; exact hcyc0.edges_nodup
  have hdisj : ∀ a ∈ pa.edges, ∀ b ∈ pb.edges, a ≠ b :=
    (List.nodup_append.mp hnodup).2.2
  by_cases hcase : s(v, w) ∈ pa.edges
  · -- `s(v,w)` lies on arc `pa`; use the opposite arc `pb.reverse`,
    -- deleting `pa`'s first edge `s(w₀, pa.snd)` (which lies on `pa`, not `pb`).
    have hepa : s(w₀, pa.snd) ∈ pa.edges :=
      SimpleGraph.Walk.mk_start_snd_mem_edges hpanil
    have hec0 : s(w₀, pa.snd) ∈ c₀.edges := by
      rw [hedges_c0]; exact List.mem_append_left _ hepa
    have hec : s(w₀, pa.snd) ∈ c.edges := hrot.mem_iff.mp hec0
    have hgpb : s(v, w) ∉ pb.edges := fun h => (hdisj _ hcase _ h) rfl
    have hnpb : s(w₀, pa.snd) ∉ pb.edges := fun h => (hdisj _ hepa _ h) rfl
    have hnarcB : s(w₀, pa.snd) ∉ pb.reverse.edges := by
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hnpb
    refine ⟨s(w₀, pa.snd), hec, by simp,
      pb.reverse.toDeleteEdge (s(w₀, pa.snd)) hnarcB, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.toDeleteEdges; exact hpb.reverse
    · have hPe : (pb.reverse.toDeleteEdge (s(w₀, pa.snd)) hnarcB).edges
          = pb.reverse.edges := by
        simp [SimpleGraph.Walk.toDeleteEdge, SimpleGraph.Walk.toDeleteEdges]
      rw [hPe, SimpleGraph.Walk.edges_reverse, List.mem_reverse]; exact hgpb
  · -- `s(v,w)` avoids arc `pa`; use `pa` itself, deleting `pb.reverse`'s first
    -- edge `s(w₀, pb.reverse.snd)` (which lies on `pb`, not `pa`).
    have harcBnil : ¬ pb.reverse.Nil := fun h => hne h.eq.symm
    have heB : s(w₀, pb.reverse.snd) ∈ pb.reverse.edges :=
      SimpleGraph.Walk.mk_start_snd_mem_edges harcBnil
    have hepb : s(w₀, pb.reverse.snd) ∈ pb.edges := by
      rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at heB; exact heB
    have hec0 : s(w₀, pb.reverse.snd) ∈ c₀.edges := by
      rw [hedges_c0]; exact List.mem_append_right _ hepb
    have hec : s(w₀, pb.reverse.snd) ∈ c.edges := hrot.mem_iff.mp hec0
    have hnpa : s(w₀, pb.reverse.snd) ∉ pa.edges := fun h => (hdisj _ h _ hepb) rfl
    refine ⟨s(w₀, pb.reverse.snd), hec, by simp,
      pa.toDeleteEdge (s(w₀, pb.reverse.snd)) hnpa, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.toDeleteEdges; exact hpa
    · have hPe : (pa.toDeleteEdge (s(w₀, pb.reverse.snd)) hnpa).edges = pa.edges := by
        simp [SimpleGraph.Walk.toDeleteEdge, SimpleGraph.Walk.toDeleteEdges]
      rw [hPe]; exact hcase

/-- NAVCHAR-PIN (§6.10.6 pass 5) — PROVED (fresh-strike round 19) modulo the
single classical pin `exists_alternating_euler_trail` (EULER-A).
NAV-CHAR, attainment half, in the needed-instance form (Lemma J(ii): the
needed object is a visit/second-visit, never a phase pair): in the blocked
world some maximal walk visits a supply-`K`-support vertex or twice-visits one
of its `H`-neighbours (deg-4), or — `n` even — cuts or twice-visits a vertex
of a second odd `H`-support.  The Euler route delivers strictly more than the
disjunction asks: the alternating Eulerian trail CUTS the supply outright
(first disjunct of each branch), with the supply manufactured by
`supply_of_blocked` (PROVED) in both parities.  The former "dynamic return
question" (the ONLY open piece of the six walk-dynamics passes) is gone —
an all-edges walk does not navigate. -/
lemma navchar_of_blocked
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    ∃ (y : V) (w : G.Walk p y), IsMaximalAltWalk G H K w ∧
      ((∃ X ∈ oddCycleSupports K,
          WalkCuts w X ∨ (∃ x ∈ X, x ∈ w.support) ∨
          (∃ u, G.degree u = 4 ∧ (∃ x ∈ X, H.Adj u x) ∧
            2 ≤ w.support.count u)) ∨
       (∃ X' ∈ oddCycleSupports H, X' ≠ S ∧
          (WalkCuts w X' ∨ ∃ x ∈ X', 2 ≤ w.support.count x))) := by
  classical
  have hsplit : IsEdgeSplit G H K := hmin.1
  have hHfull : ∀ v, v ≠ p → v ≠ q → H.degree v = 2 :=
    Hfull_of_t2 G H K hdeg hsplit ht2 hpq hp3 hq3
  -- PIN EULER-A: the alternating Eulerian `p → q` trail.
  obtain ⟨w, htrail, halt, hall⟩ :=
    exists_alternating_euler_trail G H K hconn hsplit hpq hpH hqH hHfull hK2
  -- EULER-B: all-edges ⇒ maximal.
  have hmax : IsMaximalAltWalk G H K w :=
    isMaximalAltWalk_of_all_edges G H K hsplit w htrail halt hall
  -- LADDER-PIN 10 (PROVED): the parity supply, in both branches.
  have hsupply :=
    supply_of_blocked G H K hconn hdeg hmin ht2 hpq hpH hqH hHfull hK2 hPodd
      ⟨S, hS⟩
  refine ⟨q, w, hmax, ?_⟩
  rcases Nat.even_or_odd (Fintype.card V) with hn | hn
  · -- `n` even: a second odd `H`-support exists (`2 ≤ oddCycleCount H`);
    -- the Euler trail cuts it via its internal edge (EULER-C).
    have h2 : 1 < (oddCycleSupports H).card := hsupply.2 hn
    obtain ⟨X', hX', hne⟩ := Finset.exists_mem_ne h2 S
    obtain ⟨e, heH, hend⟩ := oddCycleSupport_has_internal_edge H hX'
    exact Or.inr ⟨X', hX', hne,
      Or.inl ⟨e, hall e (SimpleGraph.edgeSet_mono hsplit.2.2.1 heH), hend⟩⟩
  · -- `n` odd: an odd `K`-support exists (`1 ≤ oddCycleCount K`);
    -- the Euler trail cuts it via its internal edge (EULER-C).
    have h1 : 0 < (oddCycleSupports K).card := hsupply.1 hn
    obtain ⟨X, hX⟩ := Finset.card_pos.mp h1
    exact Or.inl ⟨X, hX, Or.inl (by
      obtain ⟨e, heK, hend⟩ := oddCycleSupport_has_internal_edge K hX
      exact ⟨e, hall e (SimpleGraph.edgeSet_mono hsplit.2.2.2.1 heK), hend⟩)⟩

set_option maxHeartbeats 1200000 in
/-- LADDER-PIN 12g′ (`reach_of_navchar`; the §6.10.5/§6.10.6 reduction,
rewired round 18).  The needed instance yields the cut: a visit to a
`K`-support vertex faces only fresh support `K`-germs (Lemma G's arrival-phase
argument); a second visit to a deg-4 `H`-neighbour delivers the walk there
(Lemma G); a second visit to a vertex of an odd `H`-support uses both its
`H`-germs — support edges.  Hence NAV-CHAR's conclusion upgrades to REACH's. -/
lemma reach_of_navchar
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hS : S ∈ oddCycleSupports H)
    (hK2 : ∀ v, K.degree v = 2)
    (hnav : ∃ (y : V) (w : G.Walk p y), IsMaximalAltWalk G H K w ∧
      ((∃ X ∈ oddCycleSupports K,
          WalkCuts w X ∨ (∃ x ∈ X, x ∈ w.support) ∨
          (∃ u, G.degree u = 4 ∧ (∃ x ∈ X, H.Adj u x) ∧
            2 ≤ w.support.count u)) ∨
       (∃ X' ∈ oddCycleSupports H, X' ≠ S ∧
          (WalkCuts w X' ∨ ∃ x ∈ X', 2 ≤ w.support.count x)))) :
    ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w := by
  obtain ⟨ y, w, hw, h | h ⟩ := hnav;
  · obtain ⟨ X, hXmem, hX ⟩ := h;
    refine' ⟨ y, w, hw, Or.inr ⟨ X, hXmem, _ ⟩ ⟩;
    rcases hX with ( hX | ⟨ x, hxX, hxw ⟩ | ⟨ u, hu4, ⟨ x, hxX, hux ⟩, hcnt ⟩ );
    · exact hX;
    · have hclose : ∀ c, K.Adj x c → c ∈ X := by
        have hXmem' := hXmem; unfold oddCycleSupports at hXmem'; simp only [mem_filter] at hXmem'; obtain ⟨-, z, cyc, hcyc, hodd, hsupp⟩ := hXmem';
        intro c hc; have := cycle_support_closed_adj K ( fun v => hK2 v ▸ le_rfl ) hcyc ( show x ∈ cyc.support from by rw [ ← hsupp ] at hxX; exact List.mem_toFinset.mp hxX ) hc; aesop;
      obtain ⟨ i, hgv, hile ⟩ := ( SimpleGraph.Walk.mem_support_iff_exists_getVert ).mp hxw;
      rcases lt_or_eq_of_le hile with hile | hile;
      · rcases Nat.even_or_odd i with ( hi | hi );
        · use s(x, w.getVert (i + 1));
          have := hw.2.1 i hile; simp_all +decide [ Nat.even_iff ] ;
          have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
            intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
            rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
          simpa only [ hgv ] using h_edge w i hile;
        · refine' ⟨ s(w.getVert (i - 1), w.getVert i), _, _ ⟩;
          · have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
              intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
              rcases i with ( _ | i ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
            grind;
          · have := hw.2.1 ( i - 1 ) ( by omega ) ; rcases i with ( _ | i ) <;> simp_all +decide [ Nat.even_add_one ] ;
            cases Nat.mod_two_eq_zero_or_one i <;> simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
            · exact hclose _ this.symm;
            · omega;
      · have hxY : x = y := by
          rw [ ← hgv, hile, SimpleGraph.Walk.getVert_length ];
        rcases Nat.even_or_odd w.length with he | ho;
        · have := hK2 x;
          have := Finset.exists_mem_ne ( show 1 < Finset.card ( K.neighborFinset x ) from by rw [ SimpleGraph.degree ] at this; aesop ) y; obtain ⟨ c, hc, hcy ⟩ := this; use s(y, c); simp_all +decide [ WalkCuts ] ;
          exact hw.2.2 c |>.1 ( Nat.even_iff.mp he ) hc;
        · have := hw.2.1 ( w.length - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) zero_lt_one ) ; simp_all +decide [ Nat.even_iff ] ;
          rcases ho with ⟨ k, hk ⟩ ; simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
          have := w.getVert_length; simp_all +decide [ Nat.add_mod, Nat.mul_mod ] ;
          exact ⟨ s(w.getVert (2 * k), y), by
            have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
              intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
              rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
            simpa [ this ] using h_edge w ( 2 * k ) ( by linarith ), by
            simp_all +decide [ Sym2.mem_iff ];
            exact hclose _ ( by simpa [ SimpleGraph.adj_comm ] using ‹K.Adj ( w.getVert ( 2 * k ) ) y› ) ⟩;
    · -- `u ≠ p`: `u` has degree 4 (`hu4`) while the walk starts at the
      -- degree-3 endpoint `p` (`hp3`) — threads the corrected pin's `hup`.
      apply double_visit_exhaustion G H K hconn hdeg hmin.1 hXmem hxX hux hu4 w hw
        (by rintro rfl; omega) hcnt;
  · obtain ⟨ X', hX', hne, hd | ⟨ x, hxX', hcnt ⟩ ⟩ := h;
    · exact ⟨ y, w, hw, Or.inl ⟨ X', hX', hne, hd ⟩ ⟩;
    · -- By Lemma Hsecond, we know that X' cuts w.
      obtain ⟨c, hc⟩ : ∃ c ∈ w.edges, ∀ v ∈ c, v ∈ X' := by
        have hHsecond : ∀ X' ∈ oddCycleSupports H, ∀ x, x ∈ X' → 2 ≤ w.support.count x → ∃ c ∈ w.edges, ∀ v ∈ c, v ∈ X' := by
          intros X' hX' x hxX' hcnt
          have hdx2 : H.degree x = 2 := by
            have hdx2 : ∀ v ∈ X', H.degree v = 2 := by
              apply oddCycleSupport_Hdeg2 H hmin.1.2.2.2.2.1 hX';
            exact hdx2 x hxX'
          have hxp : x ≠ p := by
            grind
          obtain ⟨i, hgv, hile⟩ : ∃ i, w.getVert i = x ∧ i ≤ w.length := by
            have hxs : x ∈ w.support := by
              exact List.count_pos_iff.mp ( pos_of_gt hcnt );
            exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hxs
          have hi0 : i ≠ 0 := by
            rintro rfl; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
          have hclose' : ∀ c, H.Adj x c → c ∈ X' := by
            have hXmem' := hX'
            unfold oddCycleSupports at hXmem'
            simp only [mem_filter] at hXmem'
            obtain ⟨-, z, cyc, hcyc, hodd, hsupp⟩ := hXmem';
            have hxsupp : x ∈ cyc.support := by
              exact List.mem_toFinset.mp ( hsupp.symm ▸ hxX' );
            exact fun c hac => hsupp ▸ List.mem_toFinset.mpr ( cycle_support_closed_adj H hmin.1.2.2.2.2.1 hcyc hxsupp hac );
          rcases lt_or_eq_of_le hile with hlt | heq;
          · rcases Nat.even_or_odd i with ( ⟨ k, rfl ⟩ | ⟨ k, rfl ⟩ ) <;> simp_all +decide [ Nat.add_mod ];
            · have := hw.2.1 ( k + k - 1 ) ( by omega ) ; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.add_mod ] ;
              simp_all +decide [ add_assoc, Nat.add_mod ];
              use s(w.getVert (k + (1 + k)), x);
              simp_all +decide [ Sym2.mem_iff ];
              exact ⟨ by
                have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
                  intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
                  rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
                grind, hclose' _ this.symm ⟩;
            · have := hw.2.1 ( 2 * k + 1 ) hlt;
              use s(x, w.getVert (2 * k + 2));
              simp_all +decide [ Nat.add_mod ];
              have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
                intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
                rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
              simpa only [ hgv ] using h_edge w ( 2 * k + 1 ) hlt;
          · rcases Nat.even_or_odd w.length with he | ho;
            · have := hw.2.2 ( w.getVert ( w.length - 1 ) ) ; simp_all +decide [ Nat.even_add_one ] ;
              have := hw.2.1 ( w.length - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero hi0 ) zero_lt_one ) ; simp_all +decide [ Nat.even_iff ] ;
              rcases Nat.even_or_odd' w.length with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
              rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, Nat.add_mod ];
              simp_all +decide [ show w.getVert ( 2 * k + 1 + 1 ) = x from by rw [ show 2 * k + 1 + 1 = w.length from by linarith ] ; simp +decide [ hgv ] ];
              exact ⟨ s(x, w.getVert (2 * k + 1)), by
                have h_edge : s(w.getVert (2 * k + 1), w.getVert (2 * k + 2)) ∈ w.edges := by
                  have h_edge : ∀ {a b : V} (v : G.Walk a b) (i : ℕ), i < v.length → s(v.getVert i, v.getVert (i + 1)) ∈ v.edges := by
                    intros a b v i hi; induction' v with a b v ih generalizing i; aesop;
                    rcases i with ( _ | i ) <;> simp_all +decide [ Walk.getVert ];
                  exact h_edge w _ ( by linarith );
                convert h_edge using 1;
                rw [ show w.getVert ( 2 * k + 2 ) = x from by rw [ show 2 * k + 2 = w.length from by linarith ] ; simp +decide [ hgv ] ] ; simp +decide [ Sym2.eq_swap ], by
                simp +decide [ Sym2.mem_iff ];
                exact ⟨ hxX', hclose' _ this.symm ⟩ ⟩;
            · obtain ⟨ c, hc ⟩ := SimpleGraph.degree_pos_iff_exists_adj H x |>.1 ( by linarith );
              have := hw.2.2 c;
              simp_all +decide [ Nat.odd_iff.mp ho ];
              exact ⟨ _, this, fun v hv => by rw [ Sym2.mem_iff ] at hv; rcases hv with ( rfl | rfl ) <;> [ exact hxX'; exact hclose' _ hc ] ⟩;
        exact hHsecond X' hX' x hxX' hcnt;
      exact ⟨ y, w, hw, Or.inl ⟨ X', hX', hne, c, hc ⟩ ⟩

/-- PROVED (round 17) modulo NAVIGATE + the reduction pin: REACH — in the
blocked world some maximal alternating walk from `p` cuts a second odd
component.  (Formerly the held REACH-PIN; §6.10.5 pass 4 sharpened the residual
to NAVIGATE.) -/
lemma reach_of_blocked
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    ∃ (x : V) (w : G.Walk p x),
      IsMaximalAltWalk G H K w ∧ CutsSecondOdd H K S w := by
  have hnav := navchar_of_blocked G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hPodd
  exact reach_of_navchar G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hS hK2 hnav

/-- PROVED (round 18; §6.10.6 Theorem K, conditional closure).  The full
composition NAV-CHAR ⇒ NAVIGATE ⇒ REACH ⇒ strict toggle ⇒ contradiction with
minimality: the blocked world cannot exist.  Realized as the thread
`navchar_of_blocked` → `reach_of_navchar` → `strict_of_reach` → minimality. -/
lemma blocked_world_not_minimal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    False := by
  have hreach := reach_of_blocked G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hPodd
  obtain ⟨T, ⟨-, hKsplit⟩, hstrict'⟩ :=
    strict_of_reach_geo G H K hconn hdeg hmin ht2
      hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hreach
  have hge := hmin.2 (toggled H T) (toggled K T)
    (instDecToggled H T) (instDecToggled K T) hKsplit
  exact absurd hstrict' (not_lt.mpr hge)

/-- PROVED (round 15) modulo the routing-core pins: the former MERGE-PIN, now a
thread `REACH → Theorem D → strict toggle` (§6.10 pass 3 superseding MERGE′). -/
lemma strict_merge_of_blocked
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length) :
    ∃ T : Finset (Sym2 V), IsValidToggle G H K T ∧ IsStrictToggle H K T := by
  have hreach := reach_of_blocked G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hPodd
  exact strict_of_reach_geo G H K hconn hdeg hmin ht2
    hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 hreach

/-- PROVED (ladder item 14, Theorem T2 assembly) modulo the tagged pins: at a
minimal split of a t ≤ 2 graph no odd `H`-cycle is poisoned.  Thread: poisoned
⇒ shape (pin 8) ⇒ the `p`–`q` `H`-path has even or odd length; even ⇒ a
canonical move is strict (pin 9), odd ⇒ a merge toggle is strict (MERGE-PIN);
either strict toggle contradicts minimality directly. -/
lemma no_poisoned_of_minimal_t2
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2) :
    ∀ S ∈ oddCycleSupports H, (cleanSet G K S).Nonempty := by
  intro S hS
  rw [Finset.nonempty_iff_ne_empty]
  intro hpois
  obtain ⟨p, q, z₁, z₂, z₃, hpq, hp3, hq3, hpH, hqH, hSeq, hz4,
    hpz₁, hpz₂, hqz₃, hvar, hK2, w, hwpath⟩ :=
    poisoned_t2_shape G H K hconn hdeg hmin ht2 S hS hpois
  have hstrict : ∃ T : Finset (Sym2 V),
      IsValidToggle G H K T ∧ IsStrictToggle H K T := by
    rcases Nat.even_or_odd w.length with hev | hod
    · exact canonical_strict_of_ellP_even G H K hconn hdeg hmin ht2
        hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2
        ⟨w, hwpath, hev⟩
    · exact strict_merge_of_blocked G H K hconn hdeg hmin ht2
        hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2
        ⟨w, hwpath, hod⟩
  obtain ⟨T, ⟨-, hKsplit⟩, hstrict'⟩ := hstrict
  have hge := hmin.2 (toggled H T) (toggled K T)
    (instDecToggled H T) (instDecToggled K T) hKsplit
  exact absurd hstrict' (not_lt.mpr hge)

namespace AvoidClean

set_option maxHeartbeats 1000000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The dangerous subtype (clean version): sets `t ∈ T` that could conceivably
be covered by a CLEAN transversal of `S` (all vertices in some `D s`, each
clean class met `≤ 1` time). -/
abbrev DangIxC (S T : Finset (Finset V)) (D : Finset V → Finset V) :=
  {t : Finset V // t ∈ T ∧ t ⊆ S.biUnion D ∧ ∀ s ∈ S, (t ∩ D s).card ≤ 1}

/-
Hall counting bound (clean/capacitated sum form).  For any subfamily `I` of
dangerous sets, `|I|` is at most the total clean slack `∑ (|D s| − 1)` over
classes meeting `I`; the budget `∑ (|s| − |D s|) ≤ 4` supplies the deficiency
that the uncapacitated version got for free from `|s| ≥ 3`.
-/
lemma hall_slot_sum_clean
    (S T : Finset (Finset V)) (D : Finset V → Finset V)
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hDsub : ∀ s ∈ S, D s ⊆ s)
    (hDne : ∀ s ∈ S, (D s).Nonempty)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card)
    (hbudget : ∑ s ∈ S, (s.card - (D s).card) ≤ 4)
    (I : Finset (DangIxC S T D)) :
    I.card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty),
      ((D s).card - 1) := by
  have h_card_I : 3 * I.card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (D s).card := by
    have h_card_I : ∑ t ∈ I.image Subtype.val, t.card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (D s).card := by
      have h_card_I : ∀ t ∈ I.image Subtype.val, t.card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (t ∩ D s).card := by
        intro t ht
        have h_subset : t ⊆ Finset.biUnion (S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty)) (fun s => t ∩ D s) := by
          grind +qlia;
        exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_biUnion_le );
      refine' le_trans ( Finset.sum_le_sum h_card_I ) _;
      rw [ Finset.sum_comm ];
      refine' Finset.sum_le_sum fun s hs => _;
      rw [ ← Finset.card_biUnion ];
      · exact Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => Finset.inter_subset_right );
      · intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
        exact fun v hv₁ hv₂ hv₃ => hTdisj x hx.1.1 y hy.1.1 hxy hv₁ hv₃;
    refine' le_trans _ h_card_I;
    rw [ Finset.sum_image ];
    · exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun x hx => hTcard _ <| x.2.1 );
    · exact fun x hx y hy hxy => Subtype.ext hxy;
  have h_card_I : 3 * (S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty)).card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (D s).card + 4 := by
    have h_card_I : ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (s.card - (D s).card) ≤ 4 := by
      exact le_trans ( Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ ) ) hbudget;
    have h_card_I : ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (s.card - (D s).card) + ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (D s).card ≥ 3 * (S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty)).card := by
      rw [ ← Finset.sum_add_distrib ];
      exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun x hx => show #x - #(D x) + #(D x) ≥ 3 from by rw [ tsub_add_cancel_of_le ( Finset.card_le_card ( hDsub x ( Finset.mem_filter.mp hx |>.1 ) ) ) ] ; exact hScard x ( Finset.mem_filter.mp hx |>.1 ) );
    linarith;
  have h_card_I : ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), (D s).card = ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty), ((D s).card - 1) + (S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty)).card := by
    zify;
    rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sub <| Finset.card_pos.mpr <| hDne x <| Finset.mem_filter.mp hx |>.1 ] ; simp +decide [ Finset.sum_add_distrib ];
  omega

/-- Vertex-slot target of a set `t` (clean version): for each clean class
meeting `t`, all its clean vertices except the designated hole. -/
def slotTargetC (S : Finset (Finset V)) (D : Finset V → Finset V)
    (h : Finset V → V) (t : Finset V) : Finset V :=
  (S.filter (fun s => (t ∩ D s).Nonempty)).biUnion (fun s => (D s).erase (h s))

/-
The `slotTargetC`-biUnion over a subfamily `I` collapses to the biUnion over
the clean classes meeting `I`.
-/
lemma biUnion_slotTargetC_eq
    (S T : Finset (Finset V)) (D : Finset V → Finset V) (h : Finset V → V)
    (I : Finset (DangIxC S T D)) :
    I.biUnion (fun t => slotTargetC S D h t.val)
      = (S.filter (fun s => ∃ t ∈ I, (t.val ∩ D s).Nonempty)).biUnion
          (fun s => (D s).erase (h s)) := by
  ext v; simp [slotTargetC];
  grind

/-
Hall matching (clean version): assign to each dangerous set an injective
clean slot vertex.
-/
lemma exists_slot_matching_clean
    (S T : Finset (Finset V)) (D : Finset V → Finset V) (h : Finset V → V)
    (hSdisj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint s₁ s₂)
    (hDsub : ∀ s ∈ S, D s ⊆ s)
    (hDne : ∀ s ∈ S, (D s).Nonempty)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card)
    (hbudget : ∑ s ∈ S, (s.card - (D s).card) ≤ 4)
    (hh : ∀ s ∈ S, h s ∈ D s) :
    ∃ f : DangIxC S T D → V, Function.Injective f ∧
      ∀ t, f t ∈ slotTargetC S D h t.val := by
  convert Finset.all_card_le_biUnion_card_iff_existsInjective' ( fun t : DangIxC S T D => ( slotTargetC S D h t.val ) ) |> Iff.mp <| ?_ using 1;
  intro I;
  convert hall_slot_sum_clean S T D hTdisj hDsub hDne hScard hTcard hbudget I using 1;
  rw [ biUnion_slotTargetC_eq, Finset.card_biUnion ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem ( hh x ( Finset.mem_filter.mp hx |>.1 ) ) ] ;
  · intros s hs t ht hst;
    exact Disjoint.mono ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) ( hSdisj s ( Finset.mem_filter.mp hs |>.1 ) t ( Finset.mem_filter.mp ht |>.1 ) hst |> Disjoint.mono ( hDsub s ( Finset.mem_filter.mp hs |>.1 ) ) ( hDsub t ( Finset.mem_filter.mp ht |>.1 ) ) )

/-
Combinatorial avoidance core (clean/capacitated).  Mirror of
`Avoid.avoidance_core`: given disjoint families with clean subsets `D s ⊆ s`,
nonempty and within the poison budget, there is a CLEAN transversal
(`d s ∈ D s`) avoiding every member of `T`.
-/
lemma avoidance_core_clean
    (S T : Finset (Finset V)) (D : Finset V → Finset V)
    (hSdisj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint s₁ s₂)
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hDsub : ∀ s ∈ S, D s ⊆ s)
    (hDne : ∀ s ∈ S, (D s).Nonempty)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card)
    (hbudget : ∑ s ∈ S, (s.card - (D s).card) ≤ 4) :
    ∃ d : Finset V → V,
      (∀ s ∈ S, d s ∈ D s) ∧ (∀ t ∈ T, ¬ t ⊆ S.image d) := by
  by_contra h_contra;
  -- Choose a hole function `h : Finset V → V` with `∀ s ∈ S, h s ∈ D s` (from `hDne`, via `Classical.choose`; for `s ∉ S` use `Classical.arbitrary V`).
  obtain ⟨h, hh⟩ : ∃ h : Finset V → V, ∀ s ∈ S, h s ∈ D s := by
    exact ⟨ fun s => if hs : s ∈ S then Classical.choose ( hDne s hs ) else Classical.arbitrary V, fun s hs => by simpa [ hs ] using Classical.choose_spec ( hDne s hs ) ⟩;
  obtain ⟨f, hf_inj, hf⟩ := exists_slot_matching_clean S T D h hSdisj hDsub hDne hScard hTdisj hTcard hbudget hh;
  obtain ⟨sc, hscS, hscMeet, hscf⟩ : ∃ sc : DangIxC S T D → Finset V, (∀ t, sc t ∈ S) ∧ (∀ t, (t.val ∩ D (sc t)).Nonempty) ∧ (∀ t, f t ∈ (D (sc t)).erase (h (sc t))) := by
    choose sc hsc using fun t => Finset.mem_biUnion.mp ( hf t );
    exact ⟨ sc, fun t => Finset.mem_filter.mp ( hsc t |>.1 ) |>.1, fun t => Finset.mem_filter.mp ( hsc t |>.1 ) |>.2, fun t => hsc t |>.2 ⟩;
  choose a ha using fun t => hscMeet t;
  -- Set `As s := (univ.filter (fun t => sc t = s)).image a`.
  set As : Finset V → Finset V := fun s => (Finset.univ.filter (fun t : DangIxC S T D => sc t = s)).image a;
  -- KEY CARD BOUND: for `s ∈ S`, `(As s).card ≤ (D s).card - 1`.
  have hAs_card : ∀ s ∈ S, (As s).card ≤ (D s).card - 1 := by
    intro s hs
    have hAs_card_le : (Finset.univ.filter (fun t : DangIxC S T D => sc t = s)).card ≤ ((D s).erase (h s)).card := by
      have hAs_card_le : (Finset.univ.filter (fun t : DangIxC S T D => sc t = s)).card ≤ (Finset.image f (Finset.univ.filter (fun t : DangIxC S T D => sc t = s))).card := by
        rw [ Finset.card_image_of_injective _ hf_inj ];
      exact hAs_card_le.trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun t ht => by aesop );
    exact le_trans ( Finset.card_image_le ) ( hAs_card_le.trans ( by rw [ Finset.card_erase_of_mem ( hh s hs ) ] ) );
  -- Construct `d : Finset V → V` with `∀ s ∈ S, d s ∈ D s ∧ d s ∉ As s`.
  obtain ⟨d, hd⟩ : ∃ d : Finset V → V, (∀ s ∈ S, d s ∈ D s ∧ d s ∉ As s) := by
    have h_exists_d : ∀ s ∈ S, ∃ d_s ∈ D s, d_s ∉ As s := by
      intro s hs;
      exact Finset.not_subset.mp fun h => absurd ( Finset.card_le_card h ) ( by have := hAs_card s hs; have := hScard s hs; have := hDne s hs; have := Finset.card_pos.mpr this; omega );
    choose! d hd using h_exists_d;
    exact ⟨ d, hd ⟩;
  refine' h_contra ⟨ d, fun s hs => ( hd s hs ).1, fun t ht => _ ⟩;
  intro htsup
  have ht_dangerous : t ⊆ S.biUnion D ∧ ∀ s ∈ S, (t ∩ D s).card ≤ 1 := by
    refine' ⟨ _, _ ⟩;
    · exact fun x hx => by rcases Finset.mem_image.mp ( htsup hx ) with ⟨ s, hs, rfl ⟩ ; exact Finset.mem_biUnion.mpr ⟨ s, hs, hd s hs |>.1 ⟩ ;
    · intro s hs
      have h_inter : t ∩ D s ⊆ {d s} := by
        intro x hx; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ a, ha₁, ha₂ ⟩ := htsup hx.1;
        by_cases ha₃ : a = s <;> simp_all +decide [ Finset.disjoint_left ];
        grind;
      exact Finset.card_le_card h_inter;
  have h_not_in_image : a ⟨t, ht, ht_dangerous⟩ ∉ S.image d := by
    intro h;
    obtain ⟨ s, hs, hs' ⟩ := Finset.mem_image.mp h;
    have hsc_eq : sc ⟨t, ht, ht_dangerous⟩ = s := by
      have hsc_eq : d s ∈ D (sc ⟨t, ht, ht_dangerous⟩) := by
        exact hs'.symm ▸ Finset.mem_of_mem_inter_right ( ha ⟨ t, ht, ht_dangerous ⟩ );
      have hsc_eq : d s ∈ sc ⟨t, ht, ht_dangerous⟩ ∧ d s ∈ s := by
        exact ⟨ hDsub _ ( hscS _ ) hsc_eq, hDsub _ hs ( hd _ hs |>.1 ) ⟩;
      exact Classical.not_not.1 fun h => Finset.disjoint_left.mp ( hSdisj _ ( hscS _ ) _ hs h ) hsc_eq.1 hsc_eq.2;
    exact hd s hs |>.2 ( Finset.mem_image.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hsc_eq ⟩, hs'.symm ▸ rfl ⟩ );
  exact h_not_in_image ( htsup ( ha ⟨ t, ht, ht_dangerous ⟩ |> Finset.mem_of_mem_inter_left ) )

end AvoidClean

set_option maxHeartbeats 1000000 in
/-- Strike-B Lemma B0 (global poison budget).  The total number of poisoned
vertices lying on odd `H`-cycles is at most `2 · numDeg3 G`: charge each
poisoned on-cycle vertex to a degree-3 witness (itself, or a degree-3
`K`-neighbour), and each degree-3 vertex receives at most two charges. -/
lemma poison_budget
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) :
    ∑ S ∈ oddCycleSupports H, (S.card - (cleanSet G K S).card)
      ≤ 2 * numDeg3 G := by
  obtain ⟨hdeg2H, hK2, hsum⟩ := hsplit;
  set W := (oddCycleSupports H).biUnion (fun S => S.filter (fun u => ¬ ∀ v, K.Adj u v → cap G u v = 3));
  -- By definition of $W$, we know that for each $u \in W$, there exists a degree-3 vertex $w$ such that $w = u$ or $K.Adj u w$.
  have h_charge : ∀ u ∈ W, ∃ w, G.degree w = 3 ∧ (w = u ∨ K.Adj u w) := by
    intro u hu
    obtain ⟨S, hS, huS⟩ : ∃ S ∈ oddCycleSupports H, u ∈ S.filter (fun u => ¬ ∀ v, K.Adj u v → cap G u v = 3) := by
      aesop;
    simp_all +decide [ cap_eq_three_iff G hdeg ];
    grind;
  -- By definition of $W$, we know that for each $u \in W$, $H.degree u = 2$.
  have h_Hdeg2 : ∀ u ∈ W, H.degree u = 2 := by
    intro u hu
    obtain ⟨S, hS⟩ : ∃ S ∈ oddCycleSupports H, u ∈ S.filter (fun u => ¬ ∀ v, K.Adj u v → cap G u v = 3) := by
      grind +qlia;
    obtain ⟨x, w, hw⟩ : ∃ x : V, ∃ w : H.Walk x x, w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = S := by
      unfold oddCycleSupports at hS; aesop;
    apply degree_eq_two_of_mem_cycle_support H hsum.2.2.1 hw.1;
    aesop;
  -- By definition of $W$, we know that for each $w \in D3$, the number of $u \in W$ such that $\phi(u) = w$ is at most 2.
  have h_fib : ∀ w ∈ Finset.univ.filter (fun w => G.degree w = 3), (Finset.filter (fun u => w = u ∨ K.Adj u w) W).card ≤ 2 := by
    intro w hw
    by_cases hwW : w ∈ W;
    · have h_card : (Finset.filter (fun u => w = u ∨ K.Adj u w) W).card ≤ (insert w (K.neighborFinset w)).card := by
        refine Finset.card_le_card ?_;
        intro u hu; by_cases hu' : w = u <;> simp_all +decide [ SimpleGraph.mem_neighborFinset ] ;
        exact Or.inr ( hu.2.symm );
      grind +suggestions;
    · refine' le_trans ( Finset.card_le_card _ ) _;
      exact K.neighborFinset w;
      · simp +contextual [ Finset.subset_iff, SimpleGraph.adj_comm ];
        lia;
      · exact hsum.2.2.2.1 w;
  -- By definition of $W$, we know that $W.card \leq 2 * numDeg3 G$.
  have h_Wcard : W.card ≤ 2 * numDeg3 G := by
    have h_Wcard : W.card ≤ ∑ w ∈ Finset.univ.filter (fun w => G.degree w = 3), (Finset.filter (fun u => w = u ∨ K.Adj u w) W).card := by
      have h_card_W : W ⊆ Finset.biUnion (Finset.univ.filter (fun w => G.degree w = 3)) (fun w => Finset.filter (fun u => w = u ∨ K.Adj u w) W) := by
        intro u hu; specialize h_charge u hu; aesop;
      exact le_trans ( Finset.card_le_card h_card_W ) ( Finset.card_biUnion_le );
    exact h_Wcard.trans ( le_trans ( Finset.sum_le_sum h_fib ) ( by simp +decide [ mul_comm, numDeg3 ] ) );
  convert h_Wcard using 1;
  rw [ Finset.card_biUnion ];
  · refine' Finset.sum_congr rfl fun S hS => _;
    rw [ tsub_eq_of_eq_add_rev ];
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with u ; by_cases hu : ∀ v, K.Adj u v → cap G u v = 3 <;> simp +decide [ hu ]; all_goals unfold cleanSet; aesop;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₂ |>.2 <| Finset.mem_filter.mp hx₁ |>.2;
  · intro S hS T hT hST; simp_all +decide [ Finset.disjoint_left ] ;
    intro u hu v hv hv' huT; have := oddCycleSupports_pairwise_disjoint H hsum.2.2.1; simp_all +decide [ Finset.disjoint_left ] ;
    exact this S hS T hT hST hu huT

/-- LADDER-PIN 15 (Strike-B B2; `nonbip_void_t2`).  At a minimal split of a
t ≤ 2 graph with all clean domains nonempty, a clean transversal exists
(capacitated Hall with poison budget `2t ≤ 4`; the NON-BIPARTITE-FORCED branch
is void). -/
lemma nonbip_void_t2
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    (hne : ∀ S ∈ oddCycleSupports H, (cleanSet G K S).Nonempty) :
    ∃ d : Finset V → V,
      (∀ S ∈ oddCycleSupports H, d S ∈ S ∧ CleanVertex G K (d S)) ∧
      (∀ S' ∈ oddCycleSupports K,
        ¬ (S' ⊆ (oddCycleSupports H).image d)) := by
  haveI : Nonempty V := hconn.nonempty
  have hdeg2H : ∀ v, H.degree v ≤ 2 := hmin.1.2.2.2.2.1
  have hdeg2K : ∀ v, K.degree v ≤ 2 := hmin.1.2.2.2.2.2.1
  have hbudget : ∑ S ∈ oddCycleSupports H, (S.card - (cleanSet G K S).card) ≤ 4 := by
    have hb := poison_budget G H K hdeg hmin.1
    omega
  obtain ⟨d, hdmem, hdavoid⟩ :=
    AvoidClean.avoidance_core_clean (oddCycleSupports H) (oddCycleSupports K)
      (cleanSet G K)
      (oddCycleSupports_pairwise_disjoint H hdeg2H)
      (oddCycleSupports_pairwise_disjoint K hdeg2K)
      (fun s _ => Finset.filter_subset _ _)
      hne
      (oddCycleSupports_three_le_card H)
      (oddCycleSupports_three_le_card K)
      hbudget
  refine ⟨d, ?_, hdavoid⟩
  intro S hS
  have hmem := hdmem S hS
  rw [mem_cleanSet] at hmem
  exact hmem

/-- PROVED (ladder item 16) modulo the tagged pins: the descent core
`strict_descent_of_no_clean_transversal` restricted to t ≤ 2, threaded through
items 2, 14, 15. -/
lemma strict_descent_of_no_clean_transversal_t2
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (ht2 : numDeg3 G ≤ 2)
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hbad :
      ¬ ∃ d : Finset V → V,
        (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
        (∀ S' ∈ oddCycleSupports H₁,
          ¬ (S' ⊆ (oddCycleSupports H₀).image d))) :
    ∃ (K₀ K₁ : SimpleGraph V)
      (_ : DecidableRel K₀.Adj) (_ : DecidableRel K₁.Adj),
      IsEdgeSplit G K₀ K₁ ∧
      oddCycleCount K₀ + oddCycleCount K₁ <
        oddCycleCount H₀ + oddCycleCount H₁ := by
  refine descent_of_no_bad_minimal G hdeg ?_ H₀ H₁ hsplit hbad
  intro M₀ M₁ j₀ j₁ hmin
  letI : DecidableRel M₀.Adj := j₀
  letI : DecidableRel M₁.Adj := j₁
  exact nonbip_void_t2 G M₀ M₁ hconn hdeg hmin ht2
    (no_poisoned_of_minimal_t2 G M₀ M₁ hconn hdeg hmin ht2)

/-! ## MIGRATION ROUTE (fresh-strike LENS-NONEXISTENCE §2–§3; authored 2026-07-12)

The Δω = 0 migration: at a minimal split carrying a poisoned support (the
blocked world `𝔅`), the pairing-B canonical toggle
`T* = {s(a,p), s(a,z₃), s(z₃,q)}` — with `a ∈ {z₁, z₂}` selected by the
PROVED `k_arc_separation` — yields ANOTHER minimal split that is entirely
unpoisoned, where `nonbip_void_t2` fires directly.  Validation (fresh-strike,
2026-07-12): 2843/2843 toggles for the H-side ledger, 128/128 blocked
instances for the migration proper, 733/733 for the existential form; the 8
pairing-A counter-cases make `mig_unpoisons`'s separation hypothesis `hR`
load-bearing.

Δ-ledger status (LENS §2, pins (a)/(b)):
* H-side (A1): PROVED — `toggled_H_le` (transplanted with the W16 anchor-even
  return) is exactly the `≤` form the composition needs.
* K-side (A2): PROVED — `canonical_K_count_le` under `k_arc_separation`'s
  non-reachability gives Δoc_K ≤ 0.  `anchor_Kcycle_even` is NOT consumed:
  the exact Δω = 0 identity is recovered from minimality inside
  `migration_step`, not assumed.
* Poison-exit (LENS §3 Derivation B, pin (c)): `mig_unpoisons` — the ONE open
  migration pin.

CONSUMER AUDIT (LENS §3 caveat (b), resolved 2026-07-12).  The migration does
NOT re-prove `strict_descent_of_no_clean_transversal_t2`: that statement's
proof consumes `hgood` at the GIVEN split when the given split is itself
minimal, and at a minimal+poisoned given split the migration produces neither
a strictly smaller split (Δω = 0 exactly) nor a transversal AT that split.
The existing descent chain (euler/reach_geo pins) is left fully intact.  The
Pins2-side top consumer, however, is EXISTENTIAL
(`exists_safe_split_placement` — per its docstring "exactly — and no more
than — what `strongMajority_of_safe_defects` consumes"): its t ≤ 2 analog is
wired below as `migration_safe_split_placement_t2`, whose sole sorry source
is `mig_unpoisons`.  This is an ALTERNATIVE route alongside the navigation
chain — whichever pin set closes first wins. -/

/-- Reduction: at `t ≤ 2` with `p ≠ q` the two only degree-3 vertices, a
`cap` equals `3` exactly when both endpoints avoid `{p, q}` (i.e. are
degree-4). -/
lemma mig_cap3_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2)
    {p q : V} (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3) :
    ∀ u v : V, cap G u v = 3 ↔ (u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q) := by
  have hnum : numDeg3 G = 2 := by
    have hsub : ({p, q} : Finset V) ⊆ Finset.univ.filter (fun v => G.degree v = 3) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl <;> assumption
    have hcard : 2 ≤ numDeg3 G := by
      unfold numDeg3
      calc 2 = ({p,q} : Finset V).card := by rw [Finset.card_pair hpq]
        _ ≤ _ := Finset.card_le_card hsub
    omega
  have hpair : ∀ v, G.degree v = 3 → v = p ∨ v = q := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    have hsub : ({p, q, v} : Finset V) ⊆ Finset.univ.filter (fun w => G.degree w = 3) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3 : ({p, q, v} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq, Ne.symm hcon.1]),
          Finset.card_pair (Ne.symm hcon.2)]
    have := Finset.card_le_card hsub
    unfold numDeg3 at hnum; omega
  have hdeg4_iff : ∀ v, G.degree v = 4 ↔ (v ≠ p ∧ v ≠ q) := by
    intro v
    constructor
    · intro h4 ; refine ⟨?_, ?_⟩ <;> (rintro rfl; omega)
    · intro ⟨hvp, hvq⟩
      rcases hdeg v with h3 | h4
      · rcases hpair v h3 with rfl | rfl <;> simp_all
      · exact h4
  intro u v
  rw [cap_eq_three_iff G hdeg u v, hdeg4_iff u, hdeg4_iff v]
  tauto

/-- Local structural facts of the poisoned pairing-B configuration: the support
is a genuine `H`-triangle of degree-4 vertices with `H`-degree 2, the anchors
`p, q` sit off it, and the exposed cross edges are absent on the light side. -/
lemma mig_local_facts
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {p q z₁ z₂ z₃ : V} {S : Finset V}
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hK2 : ∀ v, K.degree v = 2) :
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧
    H.Adj z₁ z₂ ∧ H.Adj z₁ z₃ ∧ H.Adj z₂ z₃ ∧
    H.degree z₁ = 2 ∧ H.degree z₂ = 2 ∧ H.degree z₃ = 2 ∧
    p ≠ z₁ ∧ p ≠ z₂ ∧ p ≠ z₃ ∧ q ≠ z₁ ∧ q ≠ z₂ ∧ q ≠ z₃ ∧
    ¬ H.Adj z₁ p ∧ ¬ H.Adj z₂ p ∧ ¬ H.Adj z₃ q ∧
    ¬ K.Adj z₁ z₃ ∧ ¬ K.Adj z₂ z₃ := by
  have htri := triangle_of_oddSupport H (hSeq ▸ hS)
  obtain ⟨h12, h13, h23, hA12, hA23, hA13⟩ := htri
  have hz1S : z₁ ∈ S := by rw [hSeq]; simp
  have hz2S : z₂ ∈ S := by rw [hSeq]; simp
  have hz3S : z₃ ∈ S := by rw [hSeq]; simp
  have hHz : ∀ z ∈ S, H.degree z = 2 := by
    intro z hz
    have := hsplit.2.2.2.2.2.2 z; have := hK2 z; have := hz4 z hz; omega
  have hpz1 : p ≠ z₁ := by intro h; rw [h] at hp3; rw [hz4 z₁ hz1S] at hp3; omega
  have hpz2 : p ≠ z₂ := by intro h; rw [h] at hp3; rw [hz4 z₂ hz2S] at hp3; omega
  have hpz3 : p ≠ z₃ := by intro h; rw [h] at hp3; rw [hz4 z₃ hz3S] at hp3; omega
  have hqz1 : q ≠ z₁ := by intro h; rw [h] at hq3; rw [hz4 z₁ hz1S] at hq3; omega
  have hqz2 : q ≠ z₂ := by intro h; rw [h] at hq3; rw [hz4 z₂ hz2S] at hq3; omega
  have hqz3' : q ≠ z₃ := by intro h; rw [h] at hq3; rw [hz4 z₃ hz3S] at hq3; omega
  refine ⟨h12, h13, h23, hA12, hA13, hA23, hHz z₁ hz1S, hHz z₂ hz2S, hHz z₃ hz3S,
    hpz1, hpz2, hpz3, hqz1, hqz2, hqz3', ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hsplit.2.1 z₁ p h hpz₁.symm
  · exact fun h => hsplit.2.1 z₂ p h hpz₂.symm
  · exact fun h => hsplit.2.1 z₃ q h hqz₃.symm
  · exact hsplit.2.1 z₁ z₃ hA13
  · exact hsplit.2.1 z₂ z₃ hA23

set_option maxHeartbeats 2000000 in
/-- Conjunct 1 of the poison-exit: every odd support of the toggled `H` has a
clean vertex for the toggled `K`. -/
lemma mig_unpoisons_H
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ a cm : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    (hsel : (a = z₁ ∧ cm = z₂) ∨ (a = z₂ ∧ cm = z₁))
    (hR : ¬ (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃) :
    ∀ S' ∈ oddCycleSupports (toggled H {s(a, p), s(a, z₃), s(z₃, q)}),
      (cleanSet G (toggled K {s(a, p), s(a, z₃), s(z₃, q)}) S').Nonempty := by
  classical
  have hlf := mig_local_facts G H K hmin.1 hp3 hq3 hSeq hS hz4 hpz₁ hpz₂ hqz₃ hK2
  obtain ⟨h12,h13,h23,hA12,hA13,hA23,hHz1,hHz2,hHz3,hpz1,hpz2,hpz3,
    hqz1,hqz2,hqz3,hnHz1p,hnHz2p,hnHz3q,hnKz1z3,hnKz2z3⟩ := hlf
  have hz1S : z₁ ∈ S := by rw [hSeq]; simp
  have hz2S : z₂ ∈ S := by rw [hSeq]; simp
  have hz3S : z₃ ∈ S := by rw [hSeq]; simp
  have hcfg : K.Adj p a ∧ K.Adj p cm ∧ a ≠ cm ∧ a ≠ z₃ ∧ cm ≠ z₃ ∧
      H.Adj a z₃ ∧ H.Adj cm z₃ ∧ H.Adj a cm ∧ ¬ K.Adj a z₃ ∧
      p ≠ a ∧ p ≠ cm ∧ q ≠ a ∧ q ≠ cm ∧ ¬ H.Adj a p ∧ a ∈ S := by
    rcases hsel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hpz₁,hpz₂,h12,h13,h23,hA13,hA23,hA12,hnKz1z3,hpz1,hpz2,hqz1,hqz2,hnHz1p,hz1S⟩
    · exact ⟨hpz₂,hpz₁,h12.symm,h23,h13,hA23,hA13,hA12.symm,hnKz2z3,hpz2,hpz1,hqz2,hqz1,hnHz2p,hz2S⟩
  obtain ⟨hKpa,hKpcm,hacm,haz3,hcmz3,hHaz3,hHcmz3,hHacm,hnKaz3,hpa,hpcm,hqa,hqcm,hnHap,haS⟩ := hcfg
  have hvalid := three_edge_toggle_valid G H K hdeg hmin.1 hHaz3 hKpa.symm hqz₃.symm
    (hz4 a haS) (hz4 z₃ hz3S) hpH hqH hpq
  obtain ⟨-, hsplitTog⟩ := hvalid
  have hHle2 : ∀ v, (toggled H {s(a, p), s(a, z₃), s(z₃, q)}).degree v ≤ 2 :=
    hsplitTog.2.2.2.2.1
  obtain ⟨q2, hqq2, hq2z3⟩ : ∃ q2, K.Adj q q2 ∧ q2 ≠ z₃ := by
    rcases hvar with ⟨y,hyS,hqy⟩ | hqz2'
    · exact ⟨y, hqy, by rintro rfl; exact hyS hz3S⟩
    · exact ⟨z₂, hqz2', h23⟩
  have hqq2ne : q ≠ q2 := hqq2.ne
  have hMp : ∀ w, (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).Adj p w ↔ w = cm := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hpw, ⟨hK,hnT⟩ | ⟨hnK,hT⟩⟩
      · rcases adj_eq_of_deg2 K (hK2 p) hKpa hKpcm hacm hK with rfl | rfl
        · exact absurd (by simp) hnT
        · rfl
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro rfl
      refine ⟨hpcm, Or.inl ⟨hKpcm, ?_⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
        subst_vars <;> simp_all [SimpleGraph.adj_comm]
  have hMq : ∀ w, (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).Adj q w ↔ w = q2 := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hqw, ⟨hK,hnT⟩ | ⟨hnK,hT⟩⟩
      · rcases adj_eq_of_deg2 K (hK2 q) hqz₃ hqq2 hq2z3.symm hK with rfl | rfl
        · exact absurd (by simp) hnT
        · rfl
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro rfl
      refine ⟨hqq2ne, Or.inl ⟨hqq2, ?_⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
        subst_vars <;> simp_all [SimpleGraph.adj_comm]
  have hHtq : ∀ w, (toggled H {s(a, p), s(a, z₃), s(z₃, q)}).Adj q w ↔ (H.Adj q w ∨ w = z₃) := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hqw, ⟨hH,hnT⟩ | ⟨hnH,hT⟩⟩
      · exact Or.inl hH
      · right
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro (hH | rfl)
      · refine ⟨hH.ne, Or.inl ⟨hH, ?_⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
      · exact ⟨hqz3, Or.inr ⟨fun h => hnHz3q h.symm, by simp⟩⟩
  have hcmz3adj : (toggled H {s(a, p), s(a, z₃), s(z₃, q)}).Adj cm z₃ := by
    rw [toggled_adj_iff]
    refine ⟨hcmz3, Or.inl ⟨hHcmz3, ?_⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
      subst_vars <;> simp_all [SimpleGraph.adj_comm]
  intro S' hS'
  have h3 : 3 ≤ S'.card := oddCycleSupports_three_le_card _ S' hS'
  simp only [oddCycleSupports, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
  obtain ⟨x, c, hc, hcodd, hcsupp⟩ := hS'
  have hz3U : z₃ ∉ ({p,q,cm,q2}:Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hpz3, Ne.symm hqz3, Ne.symm hcmz3, Ne.symm hq2z3⟩
  have hexists : ∃ u ∈ S', u ∉ ({p,q,cm,q2}:Finset V) := by
    by_contra hcon
    push_neg at hcon
    have hsub : S' ⊆ ({p,q,cm,q2}:Finset V) := fun u hu => hcon u hu
    have hqc : q ∉ c.support := by
      intro hq
      have hz3 : z₃ ∈ c.support := cycle_support_closed_adj _ hHle2 hc hq ((hHtq z₃).mpr (Or.inr rfl))
      have : z₃ ∈ S' := by rw [← hcsupp]; exact List.mem_toFinset.mpr hz3
      exact hz3U (hsub this)
    have hcmc : cm ∉ c.support := by
      intro hcm
      have hz3 : z₃ ∈ c.support := cycle_support_closed_adj _ hHle2 hc hcm hcmz3adj
      have : z₃ ∈ S' := by rw [← hcsupp]; exact List.mem_toFinset.mpr hz3
      exact hz3U (hsub this)
    have hsub2 : S' ⊆ ({p, q2}:Finset V) := by
      intro u hu
      have huc : u ∈ c.support := by rw [← List.mem_toFinset, hcsupp]; exact hu
      have hmem := hsub hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with h|h|h|h
      · exact Or.inl h
      · exact absurd (h ▸ huc) hqc
      · exact absurd (h ▸ huc) hcmc
      · exact Or.inr h
    have hcard : S'.card ≤ 2 :=
      le_trans (Finset.card_le_card hsub2) ((Finset.card_insert_le _ _).trans (by simp))
    omega
  obtain ⟨u, huS', huU⟩ := hexists
  refine ⟨u, (mem_cleanSet G _).mpr ⟨huS', ?_⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huU
  obtain ⟨hup, huq, hucm, huq2⟩ := huU
  intro v hv
  rw [mig_cap3_iff G hdeg ht2 hpq hp3 hq3 u v]
  refine ⟨hup, huq, ?_, ?_⟩
  · intro hvp; subst hvp
    rw [SimpleGraph.adj_comm, hMp u] at hv
    exact hucm hv
  · intro hvq; subst hvq
    rw [SimpleGraph.adj_comm, hMq u] at hv
    exact huq2 hv

set_option maxHeartbeats 2000000 in
/-- Conjunct 2 of the poison-exit: every odd support of the toggled `K` has a
clean vertex for the toggled `H`. -/
lemma mig_unpoisons_K
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ a cm : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    (hsel : (a = z₁ ∧ cm = z₂) ∨ (a = z₂ ∧ cm = z₁))
    (hR : ¬ (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃) :
    ∀ S' ∈ oddCycleSupports (toggled K {s(a, p), s(a, z₃), s(z₃, q)}),
      (cleanSet G (toggled H {s(a, p), s(a, z₃), s(z₃, q)}) S').Nonempty := by
  classical
  have hlf := mig_local_facts G H K hmin.1 hp3 hq3 hSeq hS hz4 hpz₁ hpz₂ hqz₃ hK2
  obtain ⟨h12,h13,h23,hA12,hA13,hA23,hHz1,hHz2,hHz3,hpz1,hpz2,hpz3,
    hqz1,hqz2,hqz3,hnHz1p,hnHz2p,hnHz3q,hnKz1z3,hnKz2z3⟩ := hlf
  have hz1S : z₁ ∈ S := by rw [hSeq]; simp
  have hz2S : z₂ ∈ S := by rw [hSeq]; simp
  have hz3S : z₃ ∈ S := by rw [hSeq]; simp
  have hcfg : K.Adj p a ∧ K.Adj p cm ∧ a ≠ cm ∧ a ≠ z₃ ∧ cm ≠ z₃ ∧
      H.Adj a z₃ ∧ H.Adj cm z₃ ∧ H.Adj a cm ∧ ¬ K.Adj a z₃ ∧
      p ≠ a ∧ p ≠ cm ∧ q ≠ a ∧ q ≠ cm ∧ ¬ H.Adj a p ∧ a ∈ S := by
    rcases hsel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hpz₁,hpz₂,h12,h13,h23,hA13,hA23,hA12,hnKz1z3,hpz1,hpz2,hqz1,hqz2,hnHz1p,hz1S⟩
    · exact ⟨hpz₂,hpz₁,h12.symm,h23,h13,hA23,hA13,hA12.symm,hnKz2z3,hpz2,hpz1,hqz2,hqz1,hnHz2p,hz2S⟩
  obtain ⟨hKpa,hKpcm,hacm,haz3,hcmz3,hHaz3,hHcmz3,hHacm,hnKaz3,hpa,hpcm,hqa,hqcm,hnHap,haS⟩ := hcfg
  have hvalid := three_edge_toggle_valid G H K hdeg hmin.1 hHaz3 hKpa.symm hqz₃.symm
    (hz4 a haS) (hz4 z₃ hz3S) hpH hqH hpq
  obtain ⟨-, hsplitTog⟩ := hvalid
  have hKle2 : ∀ v, (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).degree v ≤ 2 :=
    hsplitTog.2.2.2.2.2.1
  obtain ⟨q2, hqq2, hq2z3⟩ : ∃ q2, K.Adj q q2 ∧ q2 ≠ z₃ := by
    rcases hvar with ⟨y,hyS,hqy⟩ | hqz2'
    · exact ⟨y, hqy, by rintro rfl; exact hyS hz3S⟩
    · exact ⟨z₂, hqz2', h23⟩
  have hqq2ne : q ≠ q2 := hqq2.ne
  have hMp : ∀ w, (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).Adj p w ↔ w = cm := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hpw, ⟨hK,hnT⟩ | ⟨hnK,hT⟩⟩
      · rcases adj_eq_of_deg2 K (hK2 p) hKpa hKpcm hacm hK with rfl | rfl
        · exact absurd (by simp) hnT
        · rfl
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro rfl
      refine ⟨hpcm, Or.inl ⟨hKpcm, ?_⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
        subst_vars <;> simp_all [SimpleGraph.adj_comm]
  have hMq : ∀ w, (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).Adj q w ↔ w = q2 := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hqw, ⟨hK,hnT⟩ | ⟨hnK,hT⟩⟩
      · rcases adj_eq_of_deg2 K (hK2 q) hqz₃ hqq2 hq2z3.symm hK with rfl | rfl
        · exact absurd (by simp) hnT
        · rfl
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro rfl
      refine ⟨hqq2ne, Or.inl ⟨hqq2, ?_⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
        subst_vars <;> simp_all [SimpleGraph.adj_comm]
  have hdegp : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).degree p = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).neighborFinset p = {cm} := by
      ext w; rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]; exact hMp w
    rw [this, Finset.card_singleton]
  have hdegq : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).degree q = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).neighborFinset q = {q2} := by
      ext w; rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]; exact hMq w
    rw [this, Finset.card_singleton]
  have hMaz3 : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).Adj a z₃ := by
    rw [toggled_adj_iff]
    exact ⟨haz3, Or.inr ⟨hnKaz3, by simp⟩⟩
  have hdel : (toggled K {s(a, p), s(a, z₃), s(z₃, q)}).deleteEdges {s(a,z₃)}
      = K.deleteEdges {s(a,p), s(z₃,q)} := by
    rw [toggled_K_repr K hKpa.symm hqz₃.symm hnKaz3 haz3
      (by simp; tauto) (by simp; tauto) (by simp; tauto)]
    ext u v
    simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN | ⟨hf,_⟩, hne⟩
      · exact hN
      · exact absurd hf hne
    · intro hN
      refine ⟨Or.inl hN, ?_⟩
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnKaz3 hN.1
      · exact hnKaz3 hN.1.symm
  have hpHcard : (H.neighborFinset p).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hpH
  have hqHcard : (H.neighborFinset q).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hqH
  obtain ⟨pH, hpHset⟩ := Finset.card_eq_one.mp hpHcard
  obtain ⟨qH, hqHset⟩ := Finset.card_eq_one.mp hqHcard
  have hpHuniq : ∀ w, H.Adj p w → w = pH := by
    intro w hw
    have : w ∈ H.neighborFinset p := by rw [SimpleGraph.mem_neighborFinset]; exact hw
    rw [hpHset, Finset.mem_singleton] at this; exact this
  have hqHuniq : ∀ w, H.Adj q w → w = qH := by
    intro w hw
    have : w ∈ H.neighborFinset q := by rw [SimpleGraph.mem_neighborFinset]; exact hw
    rw [hqHset, Finset.mem_singleton] at this; exact this
  have hHtp : ∀ w, (toggled H {s(a, p), s(a, z₃), s(z₃, q)}).Adj p w ↔ (H.Adj p w ∨ w = a) := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hpw, ⟨hH,hnT⟩ | ⟨hnH,hT⟩⟩
      · exact Or.inl hH
      · right
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro (hH | rfl)
      · refine ⟨hH.ne, Or.inl ⟨hH, ?_⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
      · exact ⟨hpa, Or.inr ⟨fun h => hnHap h.symm, by simp⟩⟩
  have hHtq : ∀ w, (toggled H {s(a, p), s(a, z₃), s(z₃, q)}).Adj q w ↔ (H.Adj q w ∨ w = z₃) := by
    intro w
    rw [toggled_adj_iff]
    constructor
    · rintro ⟨hqw, ⟨hH,hnT⟩ | ⟨hnH,hT⟩⟩
      · exact Or.inl hH
      · right
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hT
        rcases hT with (⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
    · rintro (hH | rfl)
      · refine ⟨hH.ne, Or.inl ⟨hH, ?_⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        rintro ((⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)|(⟨h1,h2⟩|⟨h1,h2⟩)) <;>
          subst_vars <;> simp_all [SimpleGraph.adj_comm]
      · exact ⟨hqz3, Or.inr ⟨fun h => hnHz3q h.symm, by simp⟩⟩
  intro S' hS'
  have h3 : 3 ≤ S'.card := oddCycleSupports_three_le_card _ S' hS'
  simp only [oddCycleSupports, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
  obtain ⟨x, c, hc, hcodd, hcsupp⟩ := hS'
  have hpc : p ∉ c.support := not_mem_cycle_of_degree_one _ hdegp c hc
  have hqc : q ∉ c.support := not_mem_cycle_of_degree_one _ hdegq c hc
  have hac : a ∉ c.support := by
    intro ha
    have hedge := cycle_edge_mem_of_adj _ hKle2 hc ha hMaz3
    have hedge' : s(a,z₃) ∈ (c.rotate ha).edges :=
      ((SimpleGraph.Walk.rotate_edges c ha).mem_iff).mpr hedge
    have hreach := reachable_deleteEdges_of_cycle_edge _ (c.rotate ha) (hc.rotate ha) hedge'
    rw [hdel] at hreach
    exact hR hreach
  have hzc : z₃ ∉ c.support := by
    intro hz
    have hedge := cycle_edge_mem_of_adj _ hKle2 hc hz hMaz3.symm
    have hedge' : s(z₃,a) ∈ (c.rotate hz).edges :=
      ((SimpleGraph.Walk.rotate_edges c hz).mem_iff).mpr hedge
    have hreach := reachable_deleteEdges_of_cycle_edge _ (c.rotate hz) (hc.rotate hz) hedge'
    rw [show (s(z₃,a):Sym2 V) = s(a,z₃) from Sym2.eq_swap, hdel] at hreach
    exact hR hreach.symm
  have hne : (S' \ {pH, qH}).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have h1 := Finset.card_le_card hsub
    have h2 : ({pH, qH} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  obtain ⟨u, hu⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨huS', hunpH, hunqH⟩ := hu
  have huc : u ∈ c.support := by rw [← List.mem_toFinset, hcsupp]; exact huS'
  have hup : u ≠ p := fun h => hpc (h ▸ huc)
  have huq : u ≠ q := fun h => hqc (h ▸ huc)
  have hua : u ≠ a := fun h => hac (h ▸ huc)
  have huz : u ≠ z₃ := fun h => hzc (h ▸ huc)
  refine ⟨u, (mem_cleanSet G _).mpr ⟨huS', ?_⟩⟩
  intro v hv
  rw [(mig_cap3_iff G hdeg ht2 hpq hp3 hq3) u v]
  refine ⟨hup, huq, ?_, ?_⟩
  · intro hvp; subst hvp
    rw [SimpleGraph.adj_comm, hHtp u] at hv
    rcases hv with hH | rfl
    · exact hunpH (hpHuniq u hH)
    · exact hua rfl
  · intro hvq; subst hvq
    rw [SimpleGraph.adj_comm, hHtq u] at hv
    rcases hv with hH | rfl
    · exact hunqH (hqHuniq u hH)
    · exact huz rfl

/-- MIGRATION-PIN (LENS-NONEXISTENCE §3 Derivation B — poison-exit; the ONE
open pin of the migration route).  After the pairing-B canonical toggle
`{s(a,p), s(a,z₃), s(z₃,q)}` (selection `hsel`; separation `hR` supplied by
`k_arc_separation`), EVERY odd support of the toggled split has a clean
vertex, in both cross-directions.  Informal proof (local adjacency checking):
after the toggle each anchor keeps exactly ONE cross-germ, so at most two
vertices of `V` are cross-adjacent to a degree-3 vertex while a poisoned
support needs three unclean vertices; the one new odd component carries the
explicit clean witness (`a`'s second old `K`-germ lies off `{p, q} ∪ S`).
Validated 2843/2843 on the 2-regular side and 128/128 blocked instances on
both sides under pairing-B; the 8 pairing-A counter-cases in the fresh-strike
data show `hR` is load-bearing, not cosmetic. -/
lemma mig_unpoisons
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {p q z₁ z₂ z₃ a cm : V} {S : Finset V}
    (hpq : p ≠ q) (hp3 : G.degree p = 3) (hq3 : G.degree q = 3)
    (hpH : H.degree p = 1) (hqH : H.degree q = 1)
    (hSeq : S = {z₁, z₂, z₃}) (hS : S ∈ oddCycleSupports H)
    (hz4 : ∀ z ∈ S, G.degree z = 4)
    (hpz₁ : K.Adj p z₁) (hpz₂ : K.Adj p z₂) (hqz₃ : K.Adj q z₃)
    (hvar : (∃ y, y ∉ S ∧ K.Adj q y) ∨ K.Adj q z₂)
    (hK2 : ∀ v, K.degree v = 2)
    (hPodd : ∃ w : H.Walk p q, w.IsPath ∧ Odd w.length)
    (hsel : (a = z₁ ∧ cm = z₂) ∨ (a = z₂ ∧ cm = z₁))
    (hR : ¬ (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃) :
    (∀ S' ∈ oddCycleSupports (toggled H {s(a, p), s(a, z₃), s(z₃, q)}),
      (cleanSet G (toggled K {s(a, p), s(a, z₃), s(z₃, q)}) S').Nonempty) ∧
    (∀ S' ∈ oddCycleSupports (toggled K {s(a, p), s(a, z₃), s(z₃, q)}),
      (cleanSet G (toggled H {s(a, p), s(a, z₃), s(z₃, q)}) S').Nonempty) := by
  exact ⟨mig_unpoisons_H G H K hconn hdeg hmin ht2 hpq hp3 hq3 hpH hqH hSeq hS hz4
      hpz₁ hpz₂ hqz₃ hvar hK2 hPodd hsel hR,
    mig_unpoisons_K G H K hconn hdeg hmin ht2 hpq hp3 hq3 hpH hqH hSeq hS hz4
      hpz₁ hpz₂ hqz₃ hvar hK2 hPodd hsel hR⟩

set_option maxHeartbeats 4000000 in
/-- MIGRATION STEP (LENS §2 Consequence 3 + §3; PROVED modulo the single pin
`mig_unpoisons`).  From a minimal split with a poisoned support, produce a
minimal split ALL of whose odd supports — in both cross-directions — have
clean vertices.  Even `ℓ_P` is impossible outright
(`canonical_strict_of_ellP_even` yields a strict toggle against minimality);
odd `ℓ_P` migrates: the H-side count cannot rise (`toggled_H_le`), the K-side
count cannot rise (`canonical_K_count_le` + `k_arc_separation`), so
minimality forces Δω = 0 — the toggled split is minimal again — and
`mig_unpoisons` gives the poison-exit.  NOTE: `anchor_Kcycle_even` is not
consumed anywhere in this thread. -/
lemma migration_step
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht2 : numDeg3 G ≤ 2)
    {S : Finset V} (hS : S ∈ oddCycleSupports H)
    (hpois : cleanSet G K S = ∅) :
    ∃ (H' K' : SimpleGraph V)
      (_ : DecidableRel H'.Adj) (_ : DecidableRel K'.Adj),
      IsOddCycleMinimalSplit G H' K' ∧
      (∀ S' ∈ oddCycleSupports H', (cleanSet G K' S').Nonempty) ∧
      (∀ S' ∈ oddCycleSupports K', (cleanSet G H' S').Nonempty) := by
  classical
  obtain ⟨p, q, z₁, z₂, z₃, hpq, hp3, hq3, hpH, hqH, hSeq, hz4,
    hpz₁, hpz₂, hqz₃, hvar, hK2, w, hwpath⟩ :=
    poisoned_t2_shape G H K hconn hdeg hmin ht2 S hS hpois
  rcases Nat.even_or_odd w.length with hev | hod
  · -- ℓ_P even: a canonical move is strict, contradicting minimality.
    exfalso
    obtain ⟨T, ⟨-, hKsplit⟩, hstrict⟩ :=
      canonical_strict_of_ellP_even G H K hconn hdeg hmin ht2
        hpq hp3 hq3 hpH hqH hSeq hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2 ⟨w, hwpath, hev⟩
    exact absurd hstrict (not_lt.mpr (hmin.2 (toggled H T) (toggled K T)
      (instDecToggled H T) (instDecToggled K T) hKsplit))
  · -- ℓ_P odd: migrate via the pairing-B canonical toggle.
    have hsplit : IsEdgeSplit G H K := hmin.1
    have hHmax : ∀ v, H.degree v ≤ 2 := hsplit.2.2.2.2.1
    have hsum := hsplit.2.2.2.2.2.2
    subst hSeq
    obtain ⟨hz12, hz13, hz23, hHz12, hHz23, hHz13⟩ := triangle_of_oddSupport H hS
    have hGz₁ : G.degree z₁ = 4 := hz4 z₁ (by simp)
    have hGz₂ : G.degree z₂ = 4 := hz4 z₂ (by simp)
    have hGz₃ : G.degree z₃ = 4 := hz4 z₃ (by simp)
    have hHz₁ : H.degree z₁ = 2 := by have := hsum z₁; rw [hGz₁, hK2 z₁] at this; omega
    have hHz₂ : H.degree z₂ = 2 := by have := hsum z₂; rw [hGz₂, hK2 z₂] at this; omega
    have hHz₃ : H.degree z₃ = 2 := by have := hsum z₃; rw [hGz₃, hK2 z₃] at this; omega
    have hpz₃' : p ≠ z₃ := fun h => by rw [h, hHz₃] at hpH; omega
    have hqz₁' : q ≠ z₁ := fun h => by rw [h, hHz₁] at hqH; omega
    have hqz₂' : q ≠ z₂ := fun h => by rw [h, hHz₂] at hqH; omega
    have hqz₃' : q ≠ z₃ := fun h => by rw [h, hHz₃] at hqH; omega
    obtain ⟨x0, wS, hwS_cyc, hwS_odd, hwS_supp⟩ :
        ∃ (x0 : V) (wS : H.Walk x0 x0),
          wS.IsCycle ∧ Odd wS.length ∧ wS.support.toFinset = {z₁, z₂, z₃} := by
      unfold oddCycleSupports at hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact hS
    have mig_move : ∀ a cm : V,
        ((a = z₁ ∧ cm = z₂) ∨ (a = z₂ ∧ cm = z₁)) →
        H.Adj a cm → H.Adj a z₃ → H.Adj cm z₃ →
        H.degree a = 2 → H.degree cm = 2 → G.degree a = 4 → K.Adj a p →
        ¬ (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃ →
        ∃ (H' K' : SimpleGraph V)
          (_ : DecidableRel H'.Adj) (_ : DecidableRel K'.Adj),
          IsOddCycleMinimalSplit G H' K' ∧
          (∀ S' ∈ oddCycleSupports H', (cleanSet G K' S').Nonempty) ∧
          (∀ S' ∈ oddCycleSupports K', (cleanSet G H' S').Nonempty) := by
      intro a cm hsel hac haz hcz hda hdcm hGa hKap hR
      have hacne : a ≠ cm := hac.ne
      have hazne : a ≠ z₃ := haz.ne
      have hcmz : cm ≠ z₃ := hcz.ne
      have hpa : p ≠ a := fun h => by rw [h, hda] at hpH; omega
      have hpcm : p ≠ cm := fun h => by rw [h, hdcm] at hpH; omega
      have hqa : q ≠ a := fun h => by rw [h, hda] at hqH; omega
      have hnHap : ¬ H.Adj a p := fun hH => (hsplit.2.1 a p hH) hKap
      have hnHzq : ¬ H.Adj z₃ q := fun hH => (hsplit.2.1 z₃ q hH) hqz₃.symm
      have hnKaz : ¬ K.Adj a z₃ := hsplit.2.1 a z₃ haz
      have e1 : s(a, p) ≠ s(a, z₃) := by
        rw [Ne, Sym2.eq_iff, not_or]
        exact ⟨fun h => hpz₃' h.2, fun h => hazne h.1⟩
      have e2 : s(a, p) ≠ s(z₃, q) := by
        rw [Ne, Sym2.eq_iff, not_or]
        exact ⟨fun h => hazne h.1, fun h => hqa h.1.symm⟩
      have e3 : s(a, z₃) ≠ s(z₃, q) := by
        rw [Ne, Sym2.eq_iff, not_or]
        exact ⟨fun h => hazne h.1, fun h => hqa h.1.symm⟩
      -- the triangle is `a`'s whole `H`-component, so `p` is unreachable
      have hnrap : ¬ H.Reachable a p := by
        apply not_reachable_of_closed (A := ({a, cm, z₃} : Finset V))
        · intro u hu v hadj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
          rcases hu with rfl | rfl | rfl
          · rcases adj_eq_of_deg2 H hda hac haz hcmz hadj with h | h <;> tauto
          · rcases adj_eq_of_deg2 H hdcm hac.symm hcz hazne hadj with h | h <;> tauto
          · rcases adj_eq_of_deg2 H hHz₃ haz.symm hcz.symm hacne hadj with h | h <;> tauto
        · simp
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hpa, hpcm, hpz₃'⟩
      have haw : a ∈ wS.support := by
        have ha' : a ∈ wS.support.toFinset := by
          rw [hwS_supp]
          rcases hsel with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
        simpa using ha'
      have hvalid := three_edge_toggle_valid G H K hdeg hsplit haz hKap hqz₃.symm
        hGa hGz₃ hpH hqH hpq
      -- H-side Δ-ledger (LENS A1, ≤ form): count does not rise.
      have hH_le := toggled_H_le H hHmax hpH hqH hda hHz₃ haz hnHap hnHzq
        hwS_cyc hwS_odd haw hnrap hpa hpz₃' hqa hqz₃' hpq hazne
      -- K-side Δ-ledger (LENS A2, pairing-B): count does not rise.
      have hK_le := canonical_K_count_le K {s(a, p), s(a, z₃), s(z₃, q)}
        (toggled_K_repr K hKap hqz₃.symm hnKaz hazne e1 e2 e3)
        (fun w' _ => absurd
          (⟨w'⟩ : (K.deleteEdges {s(a, p), s(z₃, q)}).Reachable a z₃) hR)
        hazne
      -- minimality forces Δω = 0: the toggled split is minimal again.
      have hmin' : IsOddCycleMinimalSplit G
          (toggled H {s(a, p), s(a, z₃), s(z₃, q)})
          (toggled K {s(a, p), s(a, z₃), s(z₃, q)}) := by
        refine ⟨hvalid.2, ?_⟩
        intro K₀ K₁ k₀ k₁ hKs
        have h := hmin.2 K₀ K₁ k₀ k₁ hKs
        omega
      have hunp := mig_unpoisons G H K hconn hdeg hmin ht2
        hpq hp3 hq3 hpH hqH rfl hS hz4 hpz₁ hpz₂ hqz₃ hvar hK2
        ⟨w, hwpath, hod⟩ hsel hR
      exact ⟨toggled H {s(a, p), s(a, z₃), s(z₃, q)},
        toggled K {s(a, p), s(a, z₃), s(z₃, q)},
        instDecToggled H _, instDecToggled K _, hmin', hunp.1, hunp.2⟩
    have harc := k_arc_separation K hK2 hpz₁ hpz₂ hqz₃ hz12 hpq hz13 hz23
      hpz₃' hqz₁' hqz₂'
    rcases harc with hR1 | hR2
    · exact mig_move z₁ z₂ (Or.inl ⟨rfl, rfl⟩) hHz12 hHz13 hHz23 hHz₁ hHz₂ hGz₁
        hpz₁.symm hR1
    · exact mig_move z₂ z₁ (Or.inr ⟨rfl, rfl⟩) hHz12.symm hHz23 hHz13 hHz₂ hHz₁ hGz₂
        hpz₂.symm hR2

/-- MIGRATION DESCENT (PROVED modulo `mig_unpoisons`): some minimal split of a
t ≤ 2 graph is entirely unpoisoned, in both cross-directions.  At most one
side of a split can carry the poisoned shape (it needs `H`-light anchors and a
2-regular cross half), so one `migration_step` — applied to whichever ordered
half is poisoned — suffices. -/
lemma migration_descent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ (M₀ M₁ : SimpleGraph V)
      (_ : DecidableRel M₀.Adj) (_ : DecidableRel M₁.Adj),
      IsOddCycleMinimalSplit G M₀ M₁ ∧
      (∀ S ∈ oddCycleSupports M₀, (cleanSet G M₁ S).Nonempty) ∧
      (∀ S' ∈ oddCycleSupports M₁, (cleanSet G M₀ S').Nonempty) := by
  classical
  obtain ⟨H, K, i₀, i₁, hmin⟩ := exists_oddCycleMinimal_split G hdeg
  letI : DecidableRel H.Adj := i₀
  letI : DecidableRel K.Adj := i₁
  by_cases hHp : ∃ S ∈ oddCycleSupports H, cleanSet G K S = ∅
  · obtain ⟨S, hS, hpois⟩ := hHp
    exact migration_step G H K hconn hdeg hmin ht2 hS hpois
  · by_cases hKp : ∃ S' ∈ oddCycleSupports K, cleanSet G H S' = ∅
    · obtain ⟨S', hS', hpois'⟩ := hKp
      exact migration_step G K H hconn hdeg
        (IsOddCycleMinimalSplit.swap G H K hmin) ht2 hS' hpois'
    · push_neg at hHp hKp
      refine ⟨H, K, i₀, i₁, hmin, ?_, ?_⟩
      · intro S hS
        exact hHp S hS
      · intro S' hS'
        exact hKp S' hS'

/-- MIGRATION ⇒ EXISTENTIAL PLACEMENT at t ≤ 2 (PROVED modulo `mig_unpoisons`;
the t ≤ 2 analog of Pins2's `exists_safe_split_placement`, which is "exactly —
and no more than — what `strongMajority_of_safe_defects` consumes").  The
migrated minimal split feeds `nonbip_void_t2` in both ordered directions, and
each clean transversal feeds `placement_of_clean_transversal`.  No `hII`, no
navigation chain: `exists_alternating_euler_trail`, `strict_of_reach_geo`,
`crossing_selection_geo` and `strict_descent_of_no_clean_transversal_t2`
itself are all bypassed on this route. -/
lemma migration_safe_split_placement_t2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ (H₀ H₁ : SimpleGraph V)
      (_ : DecidableRel H₀.Adj) (_ : DecidableRel H₁.Adj),
      IsEdgeSplit G H₀ H₁ ∧
      ∃ (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool) (b₀ b₁ : Sym2 V → Bool),
        IsMinAlternating H₀ b₀ D₀ σ₀ ∧ DefectSafe G H₀ H₁ b₀ D₀ σ₀ ∧
        IsMinAlternating H₁ b₁ D₁ σ₁ ∧ DefectSafe G H₁ H₀ b₁ D₁ σ₁ := by
  classical
  obtain ⟨M₀, M₁, j₀, j₁, hmin, hc₀, hc₁⟩ := migration_descent G hconn hdeg ht2
  letI : DecidableRel M₀.Adj := j₀
  letI : DecidableRel M₁.Adj := j₁
  obtain ⟨d₀, hd₀, havoid₀⟩ := nonbip_void_t2 G M₀ M₁ hconn hdeg hmin ht2 hc₀
  obtain ⟨d₁, hd₁, havoid₁⟩ := nonbip_void_t2 G M₁ M₀ hconn hdeg
    (IsOddCycleMinimalSplit.swap G M₀ M₁ hmin) ht2 hc₁
  obtain ⟨D₀, σ₀, b₀, halt₀, hsafe₀⟩ :=
    placement_of_clean_transversal G M₀ M₁ hdeg hmin.1 d₀ hd₀ havoid₀
  obtain ⟨D₁, σ₁, b₁, halt₁, hsafe₁⟩ :=
    placement_of_clean_transversal G M₁ M₀ hdeg
      (IsEdgeSplit.swap G M₀ M₁ hmin.1) d₁ hd₁ havoid₁
  exact ⟨M₀, M₁, j₀, j₁, hmin.1,
    D₀, D₁, σ₀, σ₁, b₀, b₁, halt₀, hsafe₀, halt₁, hsafe₁⟩



/-! ### Route-A validity/composition sublock (Fable TOGGLE lane, 2026-07-13)

Relocated from the free-stop section above (see the note there): these are
consumed by no in-file declaration; keeping them after every fragile
`grind +suggestions` proof insulates those searches from the new lemmas. -/

/-- ALTERNATING-CIRCUIT VALIDITY (fresh-strike/LENS-B3-INVARIANT.md §4's
second witness family).  An alternating closed trail of EVEN length is
germ-neutral at every vertex, hence a valid toggle of ANY split of a
(3,4)-regular `G` — no anchor or degree-profile hypotheses at all. -/
lemma alt_circuit_toggle_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {r : V} (w : G.Walk r r) (htrail : w.IsTrail) (halt : AlternatesKH H K w)
    (heven : w.length % 2 = 0) :
    IsValidToggle G H K w.edges.toFinset := by
  have hT : ↑w.edges.toFinset ⊆ G.edgeSet := by
    intro e he
    exact w.edges_subset_edgeSet (List.mem_toFinset.mp (Finset.mem_coe.mp he))
  rw [toggle_valid_iff G H K hdeg hsplit _ hT]
  intro v
  have hcnt := alt_trail_incidence_count H K hsplit.2.1 w htrail halt v
  rw [if_pos heven, if_neg (by omega : ¬ w.length % 2 = 1)] at hcnt
  have hEq : #{e ∈ w.edges.toFinset | e ∈ K.incidenceFinset v}
      = #{e ∈ w.edges.toFinset | e ∈ H.incidenceFinset v} := by
    by_cases hvr : v = r
    · rw [if_pos hvr] at hcnt; omega
    · rw [if_neg hvr] at hcnt; omega
  exact ⟨fun _ => hEq.symm, fun _ => Or.inl hEq.symm, fun _ => Or.inl hEq⟩

/-- (Fable TOGGLE lane, 2026-07-13.)  The edge finset of a toggled graph is
the symmetric difference itself, provided the toggle set carries no diagonal
elements (automatic for subsets of `G.edgeSet`). -/
private lemma toggled_edgeFinset (H : SimpleGraph V) [DecidableRel H.Adj]
    (T : Finset (Sym2 V)) (hT : ∀ e ∈ T, ¬ e.IsDiag) :
    (toggled H T).edgeFinset = symmDiff H.edgeFinset T := by
  have key : (toggled H T).edgeSet
      = ↑(symmDiff H.edgeFinset T) \ {e' : Sym2 V | e'.IsDiag} :=
    SimpleGraph.edgeSet_fromEdgeSet _
  ext e
  rw [SimpleGraph.mem_edgeFinset, key, Set.mem_diff]
  constructor
  · rintro ⟨h1, _⟩
    exact Finset.mem_coe.mp h1
  · intro he
    refine ⟨Finset.mem_coe.mpr he, ?_⟩
    rcases Finset.mem_symmDiff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact H.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp h1)
    · exact hT e h1

/-- TOGGLE COMPOSITION: toggling by `T` and then by `Z` is toggling by
`T ∆ Z` (symmetric-difference associativity through `fromEdgeSet`). -/
lemma toggled_toggled (H : SimpleGraph V) [DecidableRel H.Adj]
    (T Z : Finset (Sym2 V)) (hT : ∀ e ∈ T, ¬ e.IsDiag) :
    toggled (toggled H T) Z = toggled H (symmDiff T Z) := by
  have key : ∀ (M : SimpleGraph V) (_ : DecidableRel M.Adj) (S : Finset (Sym2 V)),
      toggled M S = SimpleGraph.fromEdgeSet ↑(symmDiff M.edgeFinset S) :=
    fun _ _ _ => rfl
  rw [key, toggled_edgeFinset H T hT, key, symmDiff_assoc]

/-- Degrees are stable under graph equality across different decidability
instances (the `rw`-motive obstruction for dependent `Decidable` arguments,
discharged once). -/
private lemma degree_eq_of_graph_eq {A A' : SimpleGraph V}
    [DecidableRel A.Adj] [DecidableRel A'.Adj] (h : A = A') (v : V) :
    A.degree v = A'.degree v := by
  have hnb : A.neighborFinset v = A'.neighborFinset v := by
    ext u
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset, h]
  show (A.neighborFinset v).card = (A'.neighborFinset v).card
  rw [hnb]

/-- `IsEdgeSplit` transfers along graph equalities (instance-robust form;
plain `rw` fails on the dependent `DecidableRel` arguments). -/
private lemma isEdgeSplit_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A' B' : SimpleGraph V}
    [DecidableRel A.Adj] [DecidableRel B.Adj]
    [DecidableRel A'.Adj] [DecidableRel B'.Adj]
    (hA : A = A') (hB : B = B')
    (h : IsEdgeSplit G A B) : IsEdgeSplit G A' B' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [← hA, ← hB]
    exact h1 u v
  · intro u v hu hv
    rw [← hA] at hu
    rw [← hB] at hv
    exact h2 u v hu hv
  · rw [← hA]; exact h3
  · rw [← hB]; exact h4
  · intro v
    rw [← degree_eq_of_graph_eq hA v]
    exact h5 v
  · intro v
    rw [← degree_eq_of_graph_eq hB v]
    exact h6 v
  · intro v
    rw [← degree_eq_of_graph_eq hA v, ← degree_eq_of_graph_eq hB v]
    exact h7 v

/-- VALID TOGGLES COMPOSE: a valid toggle `Z` of the `T`-toggled split
composes with `T` into the valid toggle `T ∆ Z` of the original split.
Route A's quad exchange (and any staged surgery) lives at this composite
level. -/
lemma toggle_compose
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    {T Z : Finset (Sym2 V)}
    (hT : IsValidToggle G H K T)
    (hZ : IsValidToggle G (toggled H T) (toggled K T) Z) :
    IsValidToggle G H K (symmDiff T Z) := by
  have hTnd : ∀ e ∈ T, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (hT.1 (Finset.mem_coe.mpr he))
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_symmDiff.mp (Finset.mem_coe.mp he) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hT.1 (Finset.mem_coe.mpr h1)
    · exact hZ.1 (Finset.mem_coe.mpr h1)
  · exact isEdgeSplit_congr G (toggled_toggled H T Z hTnd)
      (toggled_toggled K T Z hTnd) hZ.2

/-- QUAD VALIDITY (fresh-strike/LENS-B3-SURGERY.md §4, exchange lemma (1)).
An alternating quad `a–b–c–d` (`ab, cd ∈ H`; `bc, da ∈ K`; the two
diagonally-opposite corner pairs distinct) is a valid toggle: it is an even
alternating closed trail, so `alt_circuit_toggle_valid` applies.  Composed
with a walk toggle via `toggle_compose`, this is route A's repair
primitive. -/
lemma quad_valid
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : H.Adj a b) (hbc : K.Adj b c) (hcd : H.Adj c d) (hda : K.Adj d a) :
    IsValidToggle G H K ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) := by
  have hGda : G.Adj d a := hsplit.2.2.2.1 hda
  have hGab : G.Adj a b := hsplit.2.2.1 hab
  have hGbc : G.Adj b c := hsplit.2.2.2.1 hbc
  have hGcd : G.Adj c d := hsplit.2.2.1 hcd
  have hnab : a ≠ b := hGab.ne
  have hnbc : b ≠ c := hGbc.ne
  have hncd : c ≠ d := hGcd.ne
  have hnda : d ≠ a := hGda.ne
  let w : G.Walk d d :=
    SimpleGraph.Walk.cons hGda (SimpleGraph.Walk.cons hGab
      (SimpleGraph.Walk.cons hGbc (SimpleGraph.Walk.cons hGcd
        SimpleGraph.Walk.nil)))
  have hedges : w.edges = [s(d, a), s(a, b), s(b, c), s(c, d)] := rfl
  have key : ∀ x y u v : V, (x ≠ u ∧ x ≠ v) ∨ (y ≠ u ∧ y ≠ v) →
      s(x, y) ≠ s(u, v) := by
    intro x y u v h heq
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hm : x ∈ s(u, v) := heq ▸ Sym2.mem_mk_left x y
      rw [Sym2.mem_iff] at hm
      tauto
    · have hm : y ∈ s(u, v) := heq ▸ Sym2.mem_mk_right x y
      rw [Sym2.mem_iff] at hm
      tauto
  have htrail : w.IsTrail := by
    constructor
    rw [hedges]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨key d a a b (Or.inl ⟨hnda, Ne.symm hbd⟩),
             key d a b c (Or.inl ⟨Ne.symm hbd, Ne.symm hncd⟩),
             key d a c d (Or.inr ⟨hac, Ne.symm hnda⟩)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨key a b b c (Or.inl ⟨hnab, hac⟩),
             key a b c d (Or.inl ⟨hac, Ne.symm hnda⟩)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact key b c c d (Or.inl ⟨hnbc, hbd⟩)
  have halt : AlternatesKH H K w := by
    intro i hi
    have hi4 : i < 4 := hi
    match i, hi4 with
    | 0, _ => exact ⟨fun _ => hda, fun h => absurd h (by decide)⟩
    | 1, _ => exact ⟨fun h => absurd h (by decide), fun _ => hab⟩
    | 2, _ => exact ⟨fun _ => hbc, fun h => absurd h (by decide)⟩
    | 3, _ => exact ⟨fun h => absurd h (by decide), fun _ => hcd⟩
  have hset : w.edges.toFinset
      = ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) := by
    rw [hedges]
    ext e
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have heven : w.length % 2 = 0 := by
    have h1 : w.edges.length = w.length := SimpleGraph.Walk.length_edges w
    rw [hedges] at h1
    simp only [List.length_cons, List.length_nil] at h1
    omega
  rw [← hset]
  exact alt_circuit_toggle_valid G H K hdeg hsplit w htrail halt heven

/-! ## GENERAL-t LADDER (STRIKE-C §7; authored 2026-07-13)

The road from the t ≤ 2 machinery to the GENERAL descent
(`strict_descent_of_no_clean_transversal`, Pins2 L2932 — the paper's sole
condition).  Source: STRIKE-C.md (§3 Theorem MT / Theorem GL, §4
architecture, §7 ladder), referee-adjudicated by
fresh-strike/STRIKE-C-REFEREE.md + fresh-strike/GL-CENSUS-AUDIT.md (all
three referee flags — AP1 merge-to-single, AP3(a) self-touching trails,
AP6(b) union shared components — HOLD against brute-force adjudication:
0 violations across 4654 self-touch trails / 13128 unions / 1572
bridge-heavy merges up to t = 26).

Status of the nine §7 items:
* item 1  `slot_profile_parity` (+ `numDeg3_even`)       — PROVED below.
* item 2  `exists_mt_decomposition`                       — PIN (Theorem MT).
* item 3  `mt_trail_valid_toggle`, `mt_union_valid_toggle`— PROVED below via
          the `SlotBalanced` engine (t-uniform; subsumes the witness family
          of `freestop_toggle_valid`, its (K-first, odd, t ≤ 2) instance).
* item 4  `general_splice_ledger`                         — FUSED into
          `genxsel_general`'s ledger conclusion (see its docstring; the
          Pins3-header item-11 precedent).
* item 5  `cut_supports_die_general`                      — PROVED below
          (t-free, walk-free death engine).
* item 6  `anchored_cut_of_poisoned`                      — PIN (ANCHOR §4.2).
* item 7  `genxsel_general`                               — PIN.  THE HELD
          PIN (§4.4).
* item 8  `nonbip_pierced_general`                        — PIN (§5).
* item 9  `strict_descent_of_no_clean_transversal_general`— PROVED below
          modulo the pins (t ≤ 2 via the existing chain, t ≥ 4 via 5/7/8).

Appended at end-of-file per the environment-order insulation rule (see the
Route-A sublock note above). -/

/-- STRIKE-C §7 vocabulary.  A light SLOT: a degree-3 vertex typed by its
light side (`side = true`: `H`-light, `H`-degree 1; `side = false`:
`K`-light, `K`-degree 1).  At a split of a degree-{3,4} graph every degree-3
vertex is exactly one of the two (`slot_profile_parity`). -/
def LightSlot (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (v : V) (side : Bool) : Prop :=
  G.degree v = 3 ∧ (side = true → H.degree v = 1) ∧
    (side = false → K.degree v = 1)

set_option maxHeartbeats 400000 in
/-- PROVED (STRIKE-C §7 item 1; the §2.1.2 profile lattice at degree level,
generalizing `deg3_lightness_parity`).  The slot profile of any split:
(i) the `H`-light and `K`-light slots partition the degree-3 vertices
(`t = 2h + 2k`); (ii) handshake in `H`: `2·|E_H| + #H-light = 2n` — the
degree-level content of `|E_H| = n − h`, `#H-light = 2h` (the path-component
count itself belongs to the decomposition lane); (iii) `#H-light` is even
(PROVED-BY-REUSE from `deg3_lightness_parity`). -/
lemma slot_profile_parity
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) :
    #{v : V | H.degree v = 1} + #{v : V | K.degree v = 1} = numDeg3 G ∧
    2 * H.edgeFinset.card + #{v : V | H.degree v = 1} = 2 * Fintype.card V ∧
    Even #{v : V | H.degree v = 1} := by
  have hbH : ∀ v : V, 1 ≤ H.degree v ∧ H.degree v ≤ 2 :=
    fun v => half_degree_bounds G H K hdeg hsplit v
  have hbK : ∀ v : V, 1 ≤ K.degree v ∧ K.degree v ≤ 2 :=
    fun v => half_degree_bounds G K H hdeg (IsEdgeSplit.swap G H K hsplit) v
  have hsum : ∀ v : V, H.degree v + K.degree v = G.degree v :=
    hsplit.2.2.2.2.2.2
  refine ⟨?_, ?_, deg3_lightness_parity G H K hdeg hsplit⟩
  · have hdisj : Disjoint ({v : V | H.degree v = 1} : Finset V)
        ({v : V | K.degree v = 1} : Finset V) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      have := hsum v
      have := hdeg v
      omega
    unfold numDeg3
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hbH v
    have h2 := hbK v
    have h3 := hsum v
    have h4 := hdeg v
    constructor
    · rintro (h | h) <;> omega
    · intro h
      by_cases hH : H.degree v = 1
      · exact Or.inl hH
      · right; omega
  · have key : ∀ v : V, H.degree v + (if H.degree v = 1 then 1 else 0) = 2 := by
      intro v
      have := hbH v
      by_cases h : H.degree v = 1 <;> simp [h] <;> omega
    have hsum2 : (∑ v : V, H.degree v)
        + (∑ v : V, (if H.degree v = 1 then 1 else 0)) = 2 * Fintype.card V := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun v _ => key v)]
      simp [Finset.card_univ, mul_comm]
    have hhs : ∑ v : V, H.degree v = 2 * H.edgeFinset.card :=
      SimpleGraph.sum_degrees_eq_twice_card_edges H
    have hcf : #{v : V | H.degree v = 1}
        = ∑ v : V, (if H.degree v = 1 then 1 else 0) := by
      rw [Finset.card_filter]
    omega

/-- PROVED (item 1 corollary; STRIKE-C §2.1.2, `t = 2h + 2k`).  The number of
degree-3 vertices of a split degree-{3,4} graph is even — supplies the
`3 ≤ t ⇒ 4 ≤ t` step of the general assembly. -/
lemma numDeg3_even
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) :
    Even (numDeg3 G) := by
  obtain ⟨ha, -, -⟩ := slot_profile_parity G H K hdeg hsplit
  rw [← ha]
  exact (deg3_lightness_parity G H K hdeg hsplit).add
    (deg3_lightness_parity G K H hdeg (IsEdgeSplit.swap G H K hsplit))

/-- STRIKE-C §7 vocabulary: an alternating SLOT TRAIL — a trail of positive
length, side-alternating in either starting phase (`AlternatesKH H K` is
`K`-first; the `H`-first phase is `AlternatesKH K H`), whose two ends are
light slots typed by their loose germ: a `K`-first trail starts at an
`H`-light slot and ends `H`-light (odd length, final edge in `K`) or
`K`-light (even length, final edge in `H`); mirror for `H`-first.  These are
exactly the pieces of an MT decomposition (STRIKE-C §3.1) and the general-t
widening of the t ≤ 2 free-stop family. -/
def IsAltTrailToggle (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    {a b : V} (w : G.Walk a b) : Prop :=
  w.IsTrail ∧ 0 < w.length ∧
  ((AlternatesKH H K w ∧ LightSlot G H K a true ∧
      (w.length % 2 = 1 → LightSlot G H K b true) ∧
      (w.length % 2 = 0 → LightSlot G H K b false)) ∨
   (AlternatesKH K H w ∧ LightSlot G H K a false ∧
      (w.length % 2 = 1 → LightSlot G H K b false) ∧
      (w.length % 2 = 0 → LightSlot G H K b true)))

/-- The SLOT-BALANCED profile (STRIKE-C §3.2/§4.4; the t-uniform form of the
balanced-cocircuit hypotheses of `maximal_walk_of_balanced_cocircuit`): a
set of `G`-edges germ-balanced at every non-anchor vertex, with one
side-typed `±1` imbalance at each anchor slot (`σ v = true`, `H`-light: one
extra `K`-germ; `σ v = false`, `K`-light: one extra `H`-germ).  Validity is
`slotBalanced_valid_toggle`; single slot trails and unions of slot trails
with distinct end slots carry this profile (`mt_trail_valid_toggle` /
`mt_union_valid_toggle`). -/
def SlotBalanced (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T : Finset (Sym2 V)) (A : Finset V) (σ : V → Bool) : Prop :=
  ↑T ⊆ G.edgeSet ∧
  (∀ v ∉ A,
    #{e ∈ T | e ∈ K.incidenceFinset v} = #{e ∈ T | e ∈ H.incidenceFinset v}) ∧
  (∀ v ∈ A, LightSlot G H K v (σ v) ∧
    (σ v = true →
      #{e ∈ T | e ∈ K.incidenceFinset v}
        = #{e ∈ T | e ∈ H.incidenceFinset v} + 1) ∧
    (σ v = false →
      #{e ∈ T | e ∈ H.incidenceFinset v}
        = #{e ∈ T | e ∈ K.incidenceFinset v} + 1))

set_option maxHeartbeats 800000 in
/-- PROVED (the general-t validity engine; STRIKE-C §3.1: "interior passes
consume one germ of each side per vertex; each slot hosts exactly one
trail-end, contributing the one-sided slack ±1 of `toggle_valid_iff`").  A
slot-balanced edge set is a valid toggle — t-FREE: no `numDeg3` hypothesis
anywhere. -/
lemma slotBalanced_valid_toggle
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {T : Finset (Sym2 V)} {A : Finset V} {σ : V → Bool}
    (h : SlotBalanced G H K T A σ) :
    IsValidToggle G H K T := by
  obtain ⟨hT, hbal, hanc⟩ := h
  rw [toggle_valid_iff G H K hdeg hsplit T hT]
  intro v
  by_cases hv : v ∈ A
  · obtain ⟨⟨hd3, hsl1, hsl0⟩, him1, him0⟩ := hanc v hv
    refine ⟨fun h4 => by omega, fun hHK => ?_, fun hHK => ?_⟩
    · rcases Bool.eq_false_or_eq_true (σ v) with hb | hb
      · exact absurd hHK.1 (by have := hsl1 hb; omega)
      · exact Or.inr (him0 hb)
    · rcases Bool.eq_false_or_eq_true (σ v) with hb | hb
      · exact Or.inr (him1 hb)
      · exact absurd hHK.2 (by have := hsl0 hb; omega)
  · have heq := hbal v hv
    exact ⟨fun _ => heq.symm, fun _ => Or.inl heq.symm, fun _ => Or.inl heq⟩

/-- PROVED.  `SlotBalanced` reads `σ` only on the anchor set. -/
lemma slotBalanced_congr
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    {T : Finset (Sym2 V)} {A : Finset V} {σ σ' : V → Bool}
    (hσ : ∀ v ∈ A, σ v = σ' v)
    (h : SlotBalanced G H K T A σ) :
    SlotBalanced G H K T A σ' := by
  obtain ⟨hT, hbal, hanc⟩ := h
  refine ⟨hT, hbal, fun v hv => ?_⟩
  obtain ⟨hsl, h1, h0⟩ := hanc v hv
  rw [← hσ v hv]
  exact ⟨hsl, h1, h0⟩

set_option maxHeartbeats 800000 in
/-- PROVED (STRIKE-C §3.1 union clause, engine form): slot-balanced sets with
disjoint edges and disjoint anchor sets union to a slot-balanced set — "a
union of trails sums balanced contributions and at most one slack per deg-3
vertex".  Folding this gives validity of arbitrary unions of MT trails
(§5 consumes unions of ≤ 3). -/
lemma slotBalanced_union
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    {T₁ T₂ : Finset (Sym2 V)} {A₁ A₂ : Finset V} {σ : V → Bool}
    (hT : Disjoint T₁ T₂) (hA : Disjoint A₁ A₂)
    (h₁ : SlotBalanced G H K T₁ A₁ σ) (h₂ : SlotBalanced G H K T₂ A₂ σ) :
    SlotBalanced G H K (T₁ ∪ T₂) (A₁ ∪ A₂) σ := by
  obtain ⟨hT1, hbal1, hanc1⟩ := h₁
  obtain ⟨hT2, hbal2, hanc2⟩ := h₂
  have haddK : ∀ v : V,
      #{e ∈ T₁ ∪ T₂ | e ∈ K.incidenceFinset v}
        = #{e ∈ T₁ | e ∈ K.incidenceFinset v}
          + #{e ∈ T₂ | e ∈ K.incidenceFinset v} := by
    intro v
    rw [Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hT)]
  have haddH : ∀ v : V,
      #{e ∈ T₁ ∪ T₂ | e ∈ H.incidenceFinset v}
        = #{e ∈ T₁ | e ∈ H.incidenceFinset v}
          + #{e ∈ T₂ | e ∈ H.incidenceFinset v} := by
    intro v
    rw [Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hT)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.coe_union]
    exact Set.union_subset hT1 hT2
  · intro v hv
    rw [Finset.mem_union] at hv
    push_neg at hv
    rw [haddK v, haddH v, hbal1 v hv.1, hbal2 v hv.2]
  · intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨hsl, h1, h0⟩ := hanc1 v hv
      have hv2 : v ∉ A₂ := Finset.disjoint_left.mp hA hv
      have hb2 := hbal2 v hv2
      refine ⟨hsl, fun hb => ?_, fun hb => ?_⟩
      · have := h1 hb
        rw [haddK v, haddH v]
        omega
      · have := h0 hb
        rw [haddH v, haddK v]
        omega
    · obtain ⟨hsl, h1, h0⟩ := hanc2 v hv
      have hv1 : v ∉ A₁ := Finset.disjoint_right.mp hA hv
      have hb1 := hbal1 v hv1
      refine ⟨hsl, fun hb => ?_, fun hb => ?_⟩
      · have := h1 hb
        rw [haddK v, haddH v]
        omega
      · have := h0 hb
        rw [haddH v, haddK v]
        omega

set_option maxHeartbeats 1000000 in
/-- PROVED (item 3 engine; STRIKE-C §3.1 per-trail validity, via the exact
germ ledger `alt_trail_incidence_count_aux`).  An alternating slot trail
with distinct ends carries the slot-balanced profile on its end pair, with
the anchor sides forced by phase and parity. -/
lemma mt_trail_slotBalanced
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {a b : V} (hab : a ≠ b) (w : G.Walk a b)
    (hw : IsAltTrailToggle G H K w) :
    ∃ σ : V → Bool,
      SlotBalanced G H K w.edges.toFinset ({a, b} : Finset V) σ := by
  obtain ⟨htrail, hlen, hcase⟩ := hw
  have hT : ↑w.edges.toFinset ⊆ G.edgeSet := by
    intro e he
    exact w.edges_subset_edgeSet (List.mem_toFinset.mp (Finset.mem_coe.mp he))
  have hba : ¬ b = a := fun h => hab h.symm
  have eaa : (if a = a then (1 : ℕ) else 0) = 1 := if_pos rfl
  have eab : (if a = b then (1 : ℕ) else 0) = 0 := if_neg hab
  have eba : (if b = a then (1 : ℕ) else 0) = 0 := if_neg hba
  have ebb : (if b = b then (1 : ℕ) else 0) = 1 := if_pos rfl
  rcases hcase with ⟨halt, hsa, hsb1, hsb0⟩ | ⟨halt, hsa, hsb1, hsb0⟩
  · -- K-first phase: ledger  #K + (even → [v=b]) = #H + [v=a] + (odd → [v=b])
    have hcnt := fun v =>
      (alt_trail_incidence_count_aux H K hsplit.2.1 w htrail).1 halt v
    by_cases hpar : w.length % 2 = 1
    · -- odd: both ends H-light
      refine ⟨fun _ => true, hT, ?_, ?_⟩
      · intro v hv
        have hva : ¬ v = a := fun h => hv (by rw [h]; exact Finset.mem_insert_self a {b})
        have hvb : ¬ v = b := fun h =>
          hv (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        have hcv := hcnt v
        rw [if_neg (show ¬ w.length % 2 = 0 by omega), if_pos hpar,
          if_neg hva, if_neg hvb] at hcv
        omega
      · intro v hv
        have hcv := hcnt v
        rw [if_neg (show ¬ w.length % 2 = 0 by omega), if_pos hpar] at hcv
        refine ⟨?_, fun _ => ?_,
          fun hff => absurd (show (true : Bool) = false from hff) (by decide)⟩
        · rcases Finset.mem_insert.mp hv with h | h
          · subst h; exact hsa
          · rw [Finset.mem_singleton] at h; subst h; exact hsb1 hpar
        · rcases Finset.mem_insert.mp hv with h | h
          · subst h
            rw [eaa, eab] at hcv
            omega
          · rw [Finset.mem_singleton] at h; subst h
            rw [eba, ebb] at hcv
            omega
    · -- even: a H-light, b K-light
      have hpar0 : w.length % 2 = 0 := by omega
      refine ⟨fun v => if v = b then false else true, hT, ?_, ?_⟩
      · intro v hv
        have hva : ¬ v = a := fun h => hv (by rw [h]; exact Finset.mem_insert_self a {b})
        have hvb : ¬ v = b := fun h =>
          hv (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        have hcv := hcnt v
        rw [if_pos hpar0, if_neg (show ¬ w.length % 2 = 1 by omega),
          if_neg hva, if_neg hvb] at hcv
        omega
      · intro v hv
        have hcv := hcnt v
        rw [if_pos hpar0, if_neg (show ¬ w.length % 2 = 1 by omega)] at hcv
        rcases Finset.mem_insert.mp hv with h | h
        · -- v = a (no subst; v ≠ b via hab)
          have hvb : ¬ v = b := by rw [h]; exact hab
          rw [if_pos h, if_neg hvb] at hcv
          refine ⟨?_, fun _ => by omega, fun hff => ?_⟩
          · show LightSlot G H K v (if v = b then false else true)
            rw [if_neg hvb, h]
            exact hsa
          · have hff' : ((if v = b then false else true) : Bool) = false := hff
            rw [if_neg hvb] at hff'
            exact absurd hff' (by decide)
        · rw [Finset.mem_singleton] at h
          have hva : ¬ v = a := by rw [h]; exact hba
          rw [if_neg hva, if_pos h] at hcv
          refine ⟨?_, fun htt => ?_, fun _ => by omega⟩
          · show LightSlot G H K v (if v = b then false else true)
            rw [if_pos h, h]
            exact hsb0 hpar0
          · have htt' : ((if v = b then false else true) : Bool) = true := htt
            rw [if_pos h] at htt'
            exact absurd htt' (by decide)
  · -- H-first phase: ledger  #H + (even → [v=b]) = #K + [v=a] + (odd → [v=b])
    have hcnt := fun v =>
      (alt_trail_incidence_count_aux H K hsplit.2.1 w htrail).2 halt v
    by_cases hpar : w.length % 2 = 1
    · -- odd: both ends K-light
      refine ⟨fun _ => false, hT, ?_, ?_⟩
      · intro v hv
        have hva : ¬ v = a := fun h => hv (by rw [h]; exact Finset.mem_insert_self a {b})
        have hvb : ¬ v = b := fun h =>
          hv (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        have hcv := hcnt v
        rw [if_neg (show ¬ w.length % 2 = 0 by omega), if_pos hpar,
          if_neg hva, if_neg hvb] at hcv
        omega
      · intro v hv
        have hcv := hcnt v
        rw [if_neg (show ¬ w.length % 2 = 0 by omega), if_pos hpar] at hcv
        refine ⟨?_,
          fun htt => absurd (show (false : Bool) = true from htt) (by decide),
          fun _ => ?_⟩
        · rcases Finset.mem_insert.mp hv with h | h
          · subst h; exact hsa
          · rw [Finset.mem_singleton] at h; subst h; exact hsb1 hpar
        · rcases Finset.mem_insert.mp hv with h | h
          · subst h
            rw [eaa, eab] at hcv
            omega
          · rw [Finset.mem_singleton] at h; subst h
            rw [eba, ebb] at hcv
            omega
    · -- even: a K-light, b H-light
      have hpar0 : w.length % 2 = 0 := by omega
      refine ⟨fun v => if v = b then true else false, hT, ?_, ?_⟩
      · intro v hv
        have hva : ¬ v = a := fun h => hv (by rw [h]; exact Finset.mem_insert_self a {b})
        have hvb : ¬ v = b := fun h =>
          hv (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
        have hcv := hcnt v
        rw [if_pos hpar0, if_neg (show ¬ w.length % 2 = 1 by omega),
          if_neg hva, if_neg hvb] at hcv
        omega
      · intro v hv
        have hcv := hcnt v
        rw [if_pos hpar0, if_neg (show ¬ w.length % 2 = 1 by omega)] at hcv
        rcases Finset.mem_insert.mp hv with h | h
        · -- v = a (no subst; v ≠ b via hab)
          have hvb : ¬ v = b := by rw [h]; exact hab
          rw [if_pos h, if_neg hvb] at hcv
          refine ⟨?_, fun htt => ?_, fun _ => by omega⟩
          · show LightSlot G H K v (if v = b then true else false)
            rw [if_neg hvb, h]
            exact hsa
          · have htt' : ((if v = b then true else false) : Bool) = true := htt
            rw [if_neg hvb] at htt'
            exact absurd htt' (by decide)
        · rw [Finset.mem_singleton] at h
          have hva : ¬ v = a := by rw [h]; exact hba
          rw [if_neg hva, if_pos h] at hcv
          refine ⟨?_, fun _ => by omega, fun hff => ?_⟩
          · show LightSlot G H K v (if v = b then true else false)
            rw [if_pos h, h]
            exact hsb0 hpar0
          · have hff' : ((if v = b then true else false) : Bool) = false := hff
            rw [if_pos h] at hff'
            exact absurd hff' (by decide)

/-- PROVED (STRIKE-C §7 item 3, single-trail clause; t-uniform — subsumes
the witness family of `freestop_toggle_valid`, which is its (K-first, odd,
t ≤ 2) instance).  Every alternating slot trail with distinct ends is a
valid toggle. -/
lemma mt_trail_valid_toggle
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {a b : V} (hab : a ≠ b) (w : G.Walk a b)
    (hw : IsAltTrailToggle G H K w) :
    IsValidToggle G H K w.edges.toFinset := by
  obtain ⟨σ, hσ⟩ := mt_trail_slotBalanced G H K hsplit hab w hw
  exact slotBalanced_valid_toggle G H K hdeg hsplit hσ

/-- PROVED (STRIKE-C §7 item 3, union clause, pairwise instance; the §5
branch consumes unions of ≤ 3 trails — fold `slotBalanced_union` once more
for the triple).  Two edge-disjoint slot trails with disjoint end pairs
union to a valid toggle. -/
lemma mt_union_valid_toggle
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    {a₁ b₁ a₂ b₂ : V} (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (w₁ : G.Walk a₁ b₁) (w₂ : G.Walk a₂ b₂)
    (h₁ : IsAltTrailToggle G H K w₁) (h₂ : IsAltTrailToggle G H K w₂)
    (hE : Disjoint w₁.edges.toFinset w₂.edges.toFinset)
    (hA : Disjoint ({a₁, b₁} : Finset V) ({a₂, b₂} : Finset V)) :
    IsValidToggle G H K (w₁.edges.toFinset ∪ w₂.edges.toFinset) := by
  obtain ⟨σ₁, hσ₁⟩ := mt_trail_slotBalanced G H K hsplit hab₁ w₁ h₁
  obtain ⟨σ₂, hσ₂⟩ := mt_trail_slotBalanced G H K hsplit hab₂ w₂ h₂
  set σ : V → Bool :=
    fun v => if v ∈ ({a₁, b₁} : Finset V) then σ₁ v else σ₂ v with hσdef
  have hσ₁' : SlotBalanced G H K w₁.edges.toFinset ({a₁, b₁} : Finset V) σ := by
    refine slotBalanced_congr G H K (fun v hv => ?_) hσ₁
    simp only [hσdef, if_pos hv]
  have hσ₂' : SlotBalanced G H K w₂.edges.toFinset ({a₂, b₂} : Finset V) σ := by
    refine slotBalanced_congr G H K (fun v hv => ?_) hσ₂
    have hv1 : v ∉ ({a₁, b₁} : Finset V) := Finset.disjoint_right.mp hA hv
    simp only [hσdef, if_neg hv1]
  exact slotBalanced_valid_toggle G H K hdeg hsplit
    (slotBalanced_union G H K hE hA hσ₁' hσ₂')

/-- PROVED.  Incidence counting for a cocircuit complement `E∖F`: the
filtered incidence count equals the `\ F` incidence count — the two forms of
the balance conjuncts (`SlotBalanced` here;
`exists_low_birth_freestop_cocircuit` / `genxsel_general` there) coincide. -/
lemma filter_sdiff_incidence_card
    (G M : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel M.Adj]
    (hle : M ≤ G) (F : Finset (Sym2 V)) (v : V) :
    #{e ∈ G.edgeFinset \ F | e ∈ M.incidenceFinset v}
      = (M.incidenceFinset v \ F).card := by
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨-, hF⟩, hM⟩
    exact ⟨hM, hF⟩
  · rintro ⟨hM, hF⟩
    exact ⟨⟨SimpleGraph.edgeSet_mono hle hM.1, hF⟩, hM⟩

/-- PROVED.  The balance-profile conjuncts of a cocircuit pin (stated over
`(·.incidenceFinset v \ F).card` — the `exists_low_birth_freestop_cocircuit`
shape) make the complement `E∖F` slot-balanced — hence, via
`slotBalanced_valid_toggle`, a VALID toggle, with no trail realization and
no parity bookkeeping.  t-FREE: this is what makes the walk-free GEN-XSEL
form assembly-ready at every t. -/
lemma slotBalanced_of_cocircuit
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hsplit : IsEdgeSplit G H K)
    {A : Finset V} {σ : V → Bool} (F : Finset (Sym2 V))
    (hbal : ∀ v ∉ A,
      (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card)
    (hanc : ∀ v ∈ A, LightSlot G H K v (σ v) ∧
      (σ v = true →
        (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card + 1) ∧
      (σ v = false →
        (H.incidenceFinset v \ F).card = (K.incidenceFinset v \ F).card + 1)) :
    SlotBalanced G H K (G.edgeFinset \ F) A σ := by
  have hH := filter_sdiff_incidence_card G H hsplit.2.2.1 F
  have hK := filter_sdiff_incidence_card G K hsplit.2.2.2.1 F
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mp
      (Finset.mem_sdiff.mp (Finset.mem_coe.mp he)).1
  · intro v hv
    rw [hK v, hH v]
    exact hbal v hv
  · intro v hv
    obtain ⟨hsl, h1, h0⟩ := hanc v hv
    refine ⟨hsl, fun hb => ?_, fun hb => ?_⟩
    · rw [hK v, hH v]; exact h1 hb
    · rw [hH v, hK v]; exact h0 hb

set_option maxHeartbeats 1000000 in
/-- PROVED (STRIKE-C §7 item 5; the walk-free generalization of
`strict_of_reach_deathH`/`deathK` — those statements' walk, anchor, and
`K`-2-regularity hypotheses were vestigial: a cut support dies under ANY
degree-≤-2-preserving toggle carrying a boundary edge.  Stated for one half
`M` and used for both; the "some end slot outside S″" slack of the §7 note
is replaced by the boundary edge itself, which any cut with an outside
vertex supplies).  If the toggle contains an edge from `S'` to the outside,
`S'` cannot survive as an odd-cycle support of the toggled half: its inside
endpoint would carry a third neighbour. -/
lemma cut_supports_die_general
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg2 : ∀ v, M.degree v ≤ 2)
    (T : Finset (Sym2 V))
    (hdeg2' : ∀ v, (toggled M T).degree v ≤ 2)
    {S' : Finset V} (hS' : S' ∈ oddCycleSupports M)
    {u pr : V} (hu : u ∈ S') (hpr : pr ∉ S') (hTe : s(u, pr) ∈ T) :
    S' ∉ oddCycleSupports (toggled M T) := by
  have hupr : u ≠ pr := fun h => hpr (h ▸ hu)
  obtain ⟨z, c, hc, -, hsupp⟩ :
      ∃ z, ∃ c : M.Walk z z, c.IsCycle ∧ Odd c.length ∧
        c.support.toFinset = S' := by
    unfold oddCycleSupports at hS'
    aesop
  have huc : u ∈ c.support := List.mem_toFinset.mp (by rw [hsupp]; exact hu)
  obtain ⟨y, y', hyy', hy, hy', hMy, hMy'⟩ := cycle_two_distinct_nbrs c hc huc
  have hyS : y ∈ S' := by rw [← hsupp]; exact List.mem_toFinset.mpr hy
  have hy'S : y' ∈ S' := by rw [← hsupp]; exact List.mem_toFinset.mpr hy'
  have hnadj : ¬ M.Adj u pr := by
    intro hadj
    have hy'pr : y' ∉ ({pr} : Finset V) := by
      rw [Finset.mem_singleton]
      exact fun h => hpr (by rw [← h]; exact hy'S)
    have hyrest : y ∉ ({y', pr} : Finset V) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hyy', fun h => hpr (by rw [← h]; exact hyS)⟩
    have hsub : ({y, y', pr} : Finset V) ⊆ M.neighborFinset u := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rw [SimpleGraph.mem_neighborFinset]; exact hMy
      · rcases Finset.mem_insert.mp hx' with rfl | hx''
        · rw [SimpleGraph.mem_neighborFinset]; exact hMy'
        · rw [Finset.mem_singleton] at hx''
          subst hx''
          rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hcard3 : ({y, y', pr} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem hyrest,
        Finset.card_insert_of_notMem hy'pr, Finset.card_singleton]
    have h3 : 3 ≤ M.degree u := by
      calc (3 : ℕ) = ({y, y', pr} : Finset V).card := hcard3.symm
        _ ≤ (M.neighborFinset u).card := Finset.card_le_card hsub
        _ = M.degree u := rfl
    have := hdeg2 u
    omega
  have hadj' : (toggled M T).Adj u pr := by
    rw [toggled_adj]
    exact ⟨hupr, ⟨fun h => absurd h hnadj, fun h => absurd hTe h⟩⟩
  intro hcon
  obtain ⟨z', c', hc', -, hsupp'⟩ :
      ∃ z', ∃ c' : (toggled M T).Walk z' z', c'.IsCycle ∧ Odd c'.length ∧
        c'.support.toFinset = S' := by
    unfold oddCycleSupports at hcon
    aesop
  have huc' : u ∈ c'.support := List.mem_toFinset.mp (by rw [hsupp']; exact hu)
  obtain ⟨w₁, w₂, hww, hw₁, hw₂, hadj₁, hadj₂⟩ :=
    cycle_two_distinct_nbrs c' hc' huc'
  have hw₁S : w₁ ∈ S' := by rw [← hsupp']; exact List.mem_toFinset.mpr hw₁
  have hw₂S : w₂ ∈ S' := by rw [← hsupp']; exact List.mem_toFinset.mpr hw₂
  have hprw : pr ∉ ({w₁, w₂} : Finset V) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    constructor
    · exact fun h => hpr (by rw [h]; exact hw₁S)
    · exact fun h => hpr (by rw [h]; exact hw₂S)
  have hw₁w₂ : w₁ ∉ ({w₂} : Finset V) := by
    rw [Finset.mem_singleton]
    exact hww
  have hsub : ({pr, w₁, w₂} : Finset V) ⊆ (toggled M T).neighborFinset u := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · rw [SimpleGraph.mem_neighborFinset]; exact hadj'
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · rw [SimpleGraph.mem_neighborFinset]; exact hadj₁
      · rw [Finset.mem_singleton] at hx''
        subst hx''
        rw [SimpleGraph.mem_neighborFinset]; exact hadj₂
  have hcard3 : ({pr, w₁, w₂} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem hprw,
      Finset.card_insert_of_notMem hw₁w₂, Finset.card_singleton]
  have h3 : 3 ≤ (toggled M T).degree u := by
    calc (3 : ℕ) = ({pr, w₁, w₂} : Finset V).card := hcard3.symm
      _ ≤ ((toggled M T).neighborFinset u).card := Finset.card_le_card hsub
      _ = (toggled M T).degree u := rfl
  have := hdeg2' u
  omega

/-- PIN — STRIKE-C §7 item 2 (Theorem MT, §3.1): the multi-trail
decomposition.  QUOTE (§3.1): "`G` connected, degrees {3,4}, `(H,K)` any
split, t ≥ 2 ... E(G) decomposes into exactly t/2 edge-disjoint open
alternating trails, jointly covering every edge exactly once, whose end
multiset is exactly the t slots, with correct end-edge sides.  Moreover
every single trail, and every union of trails, is a valid toggle."  The
validity clauses are NOT pinned — they are PROVED above
(`mt_trail_valid_toggle`, `mt_union_valid_toggle`) from the slot-typed ends
this statement provides.  The μ-genericity clause ("choose any perfect
pairing μ of the t slots") is deliberately dropped: consumers use only
existence; the proving lane may strengthen.

EXPLICIT CONSTRUCTIVE SUB-OBLIGATION (STRIKE-C-REFEREE AP1, adjudicated in
GL-CENSUS-AUDIT): the proof MUST make merge-to-single-circuit explicit — a
transition system on the tag-augmented germ populations can leave ≥ 2
alternating circuits, and a leftover circuit containing no virtual edge
would break both the t/2 count and coverage; the Hierholzer
phase-consistent splice loop (LENS-MECHANISM step 3, t-free) is the
constructive discharge, verified adversarially on bridge-heavy K4-chains to
t = 26 (1572/1572 merges, 0 failures).  Lean route (§3.2): generalize the
kernel-proved AltTransitionSystem layer — `anchorTagsAt` becomes one tag
per light slot typed by the light side; the transition permutation, orbit
machinery, reversal conjugation, and transposition-merge maximizer transfer
verbatim (none inspect the tag set's size); the single genuinely new lemma
is circuit-cut-at-virtual-edges.  Empirics (§6): 2600/2600 random
decompositions, t ∈ {4..10}, n ≤ 16 (`general-t-scripts/mt_run1/5.py`);
per-trail validity 8685/8685; union validity 300/300 + 13128/13128. -/
lemma exists_mt_decomposition
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (ht : 2 ≤ numDeg3 G) :
    ∃ L : List (Σ (a : V) (b : V), G.Walk a b),
      L.length = numDeg3 G / 2 ∧
      (∀ P ∈ L, P.1 ≠ P.2.1 ∧ IsAltTrailToggle G H K P.2.2) ∧
      List.Pairwise
        (fun P Q => Disjoint P.2.2.edges.toFinset Q.2.2.edges.toFinset) L ∧
      (∀ e ∈ G.edgeFinset, ∃ P ∈ L, e ∈ P.2.2.edges.toFinset) ∧
      ((L.flatMap fun P => [P.1, P.2.1] : List V) : Multiset V)
        = (Finset.univ.filter (fun v => G.degree v = 3)).val := by
  sorry

/-- PIN — STRIKE-C §7 item 6 (Proposition ANCHOR, §4.2): what poison buys.
QUOTE (§4.2): "Every vertex of poisoned Z is deg-3 (an A-vertex: a K-light
slot whose BOTH H-germs are Z-edges) or deg-4 with a deg-3 K-neighbour
(exposed poisoner p′ ... or shielded poisoner p″ ...).  Hence ... (ii)
there EXIST decompositions in which a Z-cutting trail is *anchored* — one
end at a poison slot with its final one or two edges pinned into Z
(A-vertex: the end H-edge IS a Z-edge; exposed: choose the tag-pairing at
p′ to end with the poison K-edge, the penultimate H-edge a Z-edge)."  Read
from the anchored end: the trail's first step lands in `S`, and either the
start itself lies in `S` (A-vertex) or the second step does too (exposed
poisoner).  "Any correct proof of the residual pin must consume the
anchor" (§4.2).  Empirics: anchored Z-cutting trail attainable 120/120
poisoned instances within ≤ 60 sampled decompositions (`mt_run4.py`);
negative control 0/60 false strikes on clean-Z minimal splits (B3(K₃,₃)
all-minimal).  KNOWN SOFT SPOT for the proving lane (this lane's referee
note, beyond AP4): §4.2 exhibits anchor hosts only at A-vertices and
exposed poisoners; an all-shielded poisoned `Z` (every witness a K-light
poisoner whose unique `K`-edge is the poison edge) is not explicitly
covered by the §4.2 construction — re-derive or refute that corner FIRST. -/
lemma anchored_cut_of_poisoned
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht4 : 4 ≤ numDeg3 G)
    {S : Finset V} (hS : S ∈ oddCycleSupports H)
    (hpois : cleanSet G K S = ∅) :
    ∃ (a b : V) (w : G.Walk a b), a ≠ b ∧ IsAltTrailToggle G H K w ∧
      WalkCuts w S ∧
      w.getVert 1 ∈ S ∧ (a ∈ S ∨ (1 < w.length ∧ w.getVert 2 ∈ S)) := by
  sorry

/-- **PIN — STRIKE-C §7 item 7: GEN-XSEL (§4.4).  THE HELD PIN.**

QUOTE (§4.4): "`(H,K)` minimal, Z a poisoned odd H-cycle, t ≥ 4.  Then some
toggle U that is a single trail — or, for the §5 branch, a union of ≤ 3
trails — of an MT decomposition (light-slot ends, anchored per 4.2) cuts Z
and satisfies  #(new odd supports of both halves under U) ≤ a + b − 1,
where a, b are the odd components cut."

FORMALISM (the STRIKE-C §0.5 route preference): stated WALK-FREE in the
balanced-cocircuit / transition-system form, SHARING SHAPE with the t ≤ 2
SELECT-pin `exists_low_birth_freestop_cocircuit` (wave-21's target): the
toggle is a complement `E∖F`; the balance conjuncts are verbatim the same
(`(·.incidenceFinset v \ F).card`); the two `+1`-`K`-imbalance anchors
generalize to two side-typed slot anchors (`LightSlot` — an `H`-light
anchor carries the `+1` `K`-imbalance, a `K`-light anchor the `+1`
`H`-imbalance; at t = 2 in the blocked shape both anchors are forced
`H`-light at `{p, q}`, recovering that pin's profile); complement
reachability from the first anchor is verbatim; the ledger is the sum-card
form.  Validity of `E∖F` is NOT part of the pin: it is PROVED from the
balance conjuncts alone (`slotBalanced_of_cocircuit` +
`slotBalanced_valid_toggle`) — no trail realization, no parity bookkeeping,
at every t.

SUBSUMPTION — HONEST STATUS (do NOT let the two pins silently diverge):
this t-uniform statement does NOT literally subsume
`exists_low_birth_freestop_cocircuit`.  Differences: (i) anchors here are
existentially chosen slots; the t ≤ 2 pin fixes them at the given `p, q`;
(ii) the ledger here is `born + 1 ≤ dead` (STRIKE-C's `new ≤ (a+b) − 1`
with the deaths folded in — at t ≥ 4 a Z-only cut with one death and zero
births is a legitimate winner), while the t ≤ 2 pin demands the stronger
`2 ≤ dead ∧ born ≤ 1`; (iii) the t ≤ 2 pin carries the blocked-shape
hypotheses, `hreach`, and an odd-card conjunct (parity here is
anchor-side-dependent and omitted).  A closure of the t ≤ 2 pin in the
transition formalism is expected to LIFT: the selection/exchange calculus
(germ-pairing transpositions; the AltTransitionSystem merge-monotonicity is
kernel-proved) is t-uniform and its t = 2 instance must produce exactly
that pin's witness.  Any statement change on either pin MUST be mirrored on
the other in the same commit.

FUSED ITEM 4 (`general_splice_ledger`, GL(a)–(e), §3.5): the debris-linkage
vocabulary (touched components, chains/loops, the F1/F2/F3 free-end census)
is NOT formalized this round — per the Pins3-header item-11 precedent it is
fused into this pin's ledger conclusion, exactly as Lemma MERGE′ was fused
until the routing core existed.  GL's empirical base: GL(a) 4680 connected
sides, 0 violations; MAIN-LEDGER 769/769; exact free-end census 2773/2773
with 190 closure witnesses (`mt_run5/6.py`); post-referee adversarial
adjudication (GL-CENSUS-AUDIT): self-touching trails 4654/4654,
shared-component unions 13128/13128, 0 violations anywhere.

EMPIRICS for the pin (§6): 455/455 poisoned instances (400 random
t ∈ {4,6,8}, n ≤ 16, + 25 B3(prism) + 30 B3(cubic8) gap-1) admit a strict
single Z-cutting MT-trail within ≤ 40 RANDOM decompositions, 0 hard cases;
anchored attainability 120/120; negative control 0/60 false strikes on
clean-Z minimal splits.  Winning-mechanism histogram: mixed-end
connected-debris ≈ 40%; ~35% of winners have j ≥ 2 on a side — the
inequality form (≤ a + b − 1), not bare connectivity, is the right target.
CORPUS HONESTY (§6): the poisoned instances are random/gap-1, NOT verified
minimal (verified-minimal poisoned instances are conjecturally empty); as
at t = 2, the empirics support the MECHANISM, not the blocked world's
consistency.

Per §7 item 7: do NOT dispatch to Aristotle as stated — close
`exists_low_birth_freestop_cocircuit` first and lift its proof. -/
lemma genxsel_general
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht4 : 4 ≤ numDeg3 G)
    {S : Finset V} (hS : S ∈ oddCycleSupports H)
    (hpois : cleanSet G K S = ∅) :
    ∃ (s₁ s₂ : V) (σ₁ σ₂ : Bool) (F : Finset (Sym2 V)),
      s₁ ≠ s₂ ∧
      LightSlot G H K s₁ σ₁ ∧ LightSlot G H K s₂ σ₂ ∧
      (∀ v, v ≠ s₁ → v ≠ s₂ →
        (K.incidenceFinset v \ F).card = (H.incidenceFinset v \ F).card) ∧
      ((σ₁ = true →
        (K.incidenceFinset s₁ \ F).card
          = (H.incidenceFinset s₁ \ F).card + 1) ∧
       (σ₁ = false →
        (H.incidenceFinset s₁ \ F).card
          = (K.incidenceFinset s₁ \ F).card + 1)) ∧
      ((σ₂ = true →
        (K.incidenceFinset s₂ \ F).card
          = (H.incidenceFinset s₂ \ F).card + 1) ∧
       (σ₂ = false →
        (H.incidenceFinset s₂ \ F).card
          = (K.incidenceFinset s₂ \ F).card + 1)) ∧
      (∀ e ∈ G.edgeSet, e ∉ F → ∀ v ∈ e,
        (G.deleteEdges (↑F : Set (Sym2 V))).Reachable s₁ v) ∧
      (∃ e ∈ G.edgeFinset \ F, ∀ v ∈ e, v ∈ S) ∧
      (oddCycleSupports (toggled H (G.edgeFinset \ F))
            \ oddCycleSupports H).card
        + (oddCycleSupports (toggled K (G.edgeFinset \ F))
            \ oddCycleSupports K).card + 1
        ≤ (oddCycleSupports H
            \ oddCycleSupports (toggled H (G.edgeFinset \ F))).card
          + (oddCycleSupports K
            \ oddCycleSupports (toggled K (G.edgeFinset \ F))).card := by
  sorry

/-- PIN — STRIKE-C §7 item 8 (§5, NON-BIPARTITE-FORCED at general t): at a
minimal split with all clean domains nonempty a clean transversal exists —
`nonbip_void_t2` with the t ≤ 2 hypothesis replaced by t ≥ 4.  QUOTE (§5):
the §4 Hall reduction is stated for all t — any obstruction yields ≥ 2
pierced supports with the B2′ density bound (< 4t/3 cycles, poison mass
> 3/2 each) and CODEX-DESCENT-2 §12.4's sharpened arithmetic
(`s ≥ |J| + 2 + 2f`) giving a collision pair on one dangerous cycle;
Theorem 7.1 (all t) kills the double-poisoner piercing; cutting {Z₁, Z₂, C}
gives a + b ≥ 3, so GEN-XSEL's inequality tolerates TWO odd closures — the
branch consumes `genxsel_general` with the union-of-≤ 3-trails enrichment
(§4.4 note; union validity is PROVED here: `mt_union_valid_toggle` /
`slotBalanced_union`) plus finite Hall bookkeeping.  FORMAL CAVEAT quoted
from §5: "`nonbip_void_t2`'s Hall lemma (`hall_slot_sum_clean`) hard-codes
4; the general statement must re-derive the deficiency form with the
|X₀| ≥ 3 average-degree argument of B2 §6 — same proof shape, new
constants."  The t-free budget input is PROVED: `poison_budget` gives
`Σ (|S| − |cleanSet S|) ≤ 2·numDeg3 G` at every t. -/
lemma nonbip_pierced_general
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (ht4 : 4 ≤ numDeg3 G)
    (hne : ∀ S ∈ oddCycleSupports H, (cleanSet G K S).Nonempty) :
    ∃ d : Finset V → V,
      (∀ S ∈ oddCycleSupports H, d S ∈ S ∧ CleanVertex G K (d S)) ∧
      (∀ S' ∈ oddCycleSupports K,
        ¬ (S' ⊆ (oddCycleSupports H).image d)) := by
  sorry

set_option maxHeartbeats 1000000 in
/-- PROVED modulo `genxsel_general` (STRIKE-C §4 EMPTY-DOMAIN branch): at a
minimal split no odd `H`-support is poisoned, at EVERY t — t ≤ 2 via the
existing chain (`no_poisoned_of_minimal_t2`), t ≥ 4 via GEN-XSEL: the
balance conjuncts alone make `E∖F` a valid toggle
(`slotBalanced_of_cocircuit` + `slotBalanced_valid_toggle`), and the
sum-card ledger `born + 1 ≤ dead` gives `Δω < 0` by the partition
identities — contradiction with minimality.  No B1-analogue, no shape
classification, no supply at t ≥ 4 (§7 item 9's promise); the parity step
`3 ≤ t ⇒ 4 ≤ t` is `numDeg3_even`. -/
lemma no_poisoned_of_minimal_general
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K) :
    ∀ S ∈ oddCycleSupports H, (cleanSet G K S).Nonempty := by
  intro S hS
  by_cases ht2 : numDeg3 G ≤ 2
  · exact no_poisoned_of_minimal_t2 G H K hconn hdeg hmin ht2 S hS
  · rw [Finset.nonempty_iff_ne_empty]
    intro hpois
    have ht4 : 4 ≤ numDeg3 G := by
      obtain ⟨k, hk⟩ := numDeg3_even G H K hdeg hmin.1
      omega
    obtain ⟨s₁, s₂, σ₁, σ₂, F, hs12, hsl₁, hsl₂, hbal, hb₁, hb₂, hpre,
      hcut, hled⟩ :=
      genxsel_general G H K hconn hdeg hmin ht4 hS hpois
    have hns : ¬ (s₂ = s₁) := fun h => hs12 h.symm
    have hbase : SlotBalanced G H K (G.edgeFinset \ F) ({s₁, s₂} : Finset V)
        (fun v => if v = s₁ then σ₁ else σ₂) := by
      apply slotBalanced_of_cocircuit G H K hmin.1 F
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        push_neg at hv
        exact hbal v hv.1 hv.2
      · intro v hv
        rcases Finset.mem_insert.mp hv with h | h
        · subst h
          exact ⟨by simpa using hsl₁, fun hb => hb₁.1 (by simpa using hb),
            fun hb => hb₁.2 (by simpa using hb)⟩
        · rw [Finset.mem_singleton] at h
          subst h
          exact ⟨by simpa [hns] using hsl₂,
            fun hb => hb₂.1 (by simpa [hns] using hb),
            fun hb => hb₂.2 (by simpa [hns] using hb)⟩
    have hvalid : IsValidToggle G H K (G.edgeFinset \ F) :=
      slotBalanced_valid_toggle G H K hdeg hmin.1 hbase
    have hstrict : IsStrictToggle H K (G.edgeFinset \ F) := by
      unfold IsStrictToggle
      simp only [oddCycleCount]
      have h1 := Finset.card_inter_add_card_sdiff
        (oddCycleSupports (toggled H (G.edgeFinset \ F))) (oddCycleSupports H)
      have h2 := Finset.card_inter_add_card_sdiff
        (oddCycleSupports (toggled K (G.edgeFinset \ F))) (oddCycleSupports K)
      have h3 := Finset.card_inter_add_card_sdiff
        (oddCycleSupports H) (oddCycleSupports (toggled H (G.edgeFinset \ F)))
      have h4 := Finset.card_inter_add_card_sdiff
        (oddCycleSupports K) (oddCycleSupports (toggled K (G.edgeFinset \ F)))
      have hc1 : (oddCycleSupports (toggled H (G.edgeFinset \ F))
            ∩ oddCycleSupports H).card
          = (oddCycleSupports H
            ∩ oddCycleSupports (toggled H (G.edgeFinset \ F))).card := by
        rw [Finset.inter_comm]
      have hc2 : (oddCycleSupports (toggled K (G.edgeFinset \ F))
            ∩ oddCycleSupports K).card
          = (oddCycleSupports K
            ∩ oddCycleSupports (toggled K (G.edgeFinset \ F))).card := by
        rw [Finset.inter_comm]
      omega
    have hge := hmin.2 (toggled H (G.edgeFinset \ F))
      (toggled K (G.edgeFinset \ F))
      (instDecToggled H (G.edgeFinset \ F))
      (instDecToggled K (G.edgeFinset \ F)) hvalid.2
    exact absurd hstrict (not_lt.mpr hge)

/-- PROVED modulo `nonbip_pierced_general`: the NON-BIP branch at every t
(t ≤ 2 leg: `nonbip_void_t2`; parity step: `numDeg3_even`). -/
lemma nonbip_void_general
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hmin : IsOddCycleMinimalSplit G H K)
    (hne : ∀ S ∈ oddCycleSupports H, (cleanSet G K S).Nonempty) :
    ∃ d : Finset V → V,
      (∀ S ∈ oddCycleSupports H, d S ∈ S ∧ CleanVertex G K (d S)) ∧
      (∀ S' ∈ oddCycleSupports K,
        ¬ (S' ⊆ (oddCycleSupports H).image d)) := by
  by_cases ht2 : numDeg3 G ≤ 2
  · exact nonbip_void_t2 G H K hconn hdeg hmin ht2 hne
  · have ht4 : 4 ≤ numDeg3 G := by
      obtain ⟨k, hk⟩ := numDeg3_even G H K hdeg hmin.1
      omega
    exact nonbip_pierced_general G H K hconn hdeg hmin ht4 hne

/-- PROVED modulo the general-t pins (STRIKE-C §7 item 9, the assembly): the
descent core at EVERY t — statement-congruent with Pins2's
`strict_descent_of_no_clean_transversal` (L2932, the paper's sole
condition; same hypothesis list, NO hypothesis gap — the bridge is
`exact`-shaped once the pins close; Pins2 is deliberately left untouched).
Thread: `descent_of_no_bad_minimal` + per-minimal-split
(`nonbip_void_general` ∘ `no_poisoned_of_minimal_general`); t = 0 and t = 2
land in the t ≤ 2 leg (the existing kernel chain), t ≥ 4 in the pinned leg.
OPEN-PIN SOURCES by branch: t ≤ 2 leg — exactly the current chain's
(`exists_low_birth_freestop_cocircuit` via `crossing_selection_toggle_sum`,
plus the §2/§6 shape pins feeding `poisoned_t2_shape` /
`canonical_strict_of_ellP_even`); t ≥ 4 leg — `genxsel_general` +
`nonbip_pierced_general`.  (`exists_mt_decomposition` and
`anchored_cut_of_poisoned` are NOT consumed by this assembly: they are the
proving lane's tools for `genxsel_general`, pinned so the ladder is
statement-complete.) -/
lemma strict_descent_of_no_clean_transversal_general
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hbad :
      ¬ ∃ d : Finset V → V,
        (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
        (∀ S' ∈ oddCycleSupports H₁,
          ¬ (S' ⊆ (oddCycleSupports H₀).image d))) :
    ∃ (K₀ K₁ : SimpleGraph V)
      (_ : DecidableRel K₀.Adj) (_ : DecidableRel K₁.Adj),
      IsEdgeSplit G K₀ K₁ ∧
      oddCycleCount K₀ + oddCycleCount K₁ <
        oddCycleCount H₀ + oddCycleCount H₁ := by
  refine descent_of_no_bad_minimal G hdeg ?_ H₀ H₁ hsplit hbad
  intro M₀ M₁ j₀ j₁ hmin
  letI : DecidableRel M₀.Adj := j₀
  letI : DecidableRel M₁.Adj := j₁
  exact nonbip_void_general G M₀ M₁ hconn hdeg hmin
    (no_poisoned_of_minimal_general G M₀ M₁ hconn hdeg hmin)

/-! ## The t ≤ 2 top theorem (CONSUMER-REWIRE lane, 2026-07-13)

CONSUMER-MAP FACT (verified on Pins2's bytes): the top-level chain
`R4_three_four` → `R4_three_four_connected` → `classII_arm` →
`exists_safe_split_placement` consumes `clean_transversal_of_minimal` — and
hence the descent pin `strict_descent_of_no_clean_transversal` — at exactly
ONE existentially chosen minimal split (`exists_oddCycleMinimal_split`, Pins2
L3253; both orientations applied inside `placement_on_oddCycleMinimal_split`,
L3217/3219).  The ∀-minimal-splits strength of the descent chain is NOT
needed by the final theorem: "∃ a minimal split admitting a clean transversal
in both orientations" suffices.  `migration_safe_split_placement_t2` above
delivers exactly that existential shape at t ≤ 2 — and with `mig_unpoisons`
CLOSED (W20 direct transplant, same day) it is now UNCONDITIONAL — so the
whole PROVED Pins2 downstream (placement engine, coloring assembly, component
lift) re-assembles here into an unconditional t ≤ 2 top theorem that bypasses
`strict_descent_of_no_clean_transversal`, the navigation chain, AND the
class-I/class-II split (the migration route needs no `hII`).
Pins2 stays byte-untouched (house rule); its lift infrastructure (`glue`,
`cnt_glue_eq`, `nColor_glue_eq`, `induce_supp_degree`) is consumed from there.

SCOPE (binding): this is an UNCONDITIONAL strong majority 4-coloring theorem
for mixed degree-{3,4} graphs WITH AT MOST TWO degree-3 vertices — but NOT
the full mixed class: general t stays open, the paper's Pins2-L2932 condition
is undischarged, and `R4_three_four` itself is unchanged. -/

open scoped Classical

/-- CONNECTED t ≤ 2 THEOREM (UNCONDITIONAL): every connected degree-{3,4}
graph with at most two degree-3 vertices has a strong majority 4-coloring.
Mirrors Pins2's `classII_arm` + `R4_three_four_connected`, with the
transversal source rewired from `clean_transversal_of_minimal` (the descent
pin) to `migration_safe_split_placement_t2`; no `hII`, no case split. -/
theorem R4_three_four_connected_t2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  obtain ⟨H₀, H₁, i₀, i₁, hsplit, D₀, D₁, σ₀, σ₁, b₀, b₁,
    halt₀, hsafe₀, halt₁, hsafe₁⟩ :=
    migration_safe_split_placement_t2 G hconn hdeg ht2
  letI : DecidableRel H₀.Adj := i₀
  letI : DecidableRel H₁.Adj := i₁
  exact ⟨combine H₀ b₀ b₁,
    strongMajority_of_safe_defects G H₀ H₁ hdeg hsplit b₀ b₁ D₀ D₁ σ₀ σ₁
      halt₀.2 halt₁.2 hsafe₀ hsafe₁⟩

/-- The degree-3 count does not grow under restriction to a connected
component: `induce_supp_degree` transfers degrees vertexwise, so the filtered
set injects into `G`'s via the subtype projection. -/
lemma numDeg3_induce_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : G.ConnectedComponent) :
    numDeg3 (G.induce K.supp) ≤ numDeg3 G := by
  unfold numDeg3
  apply Finset.card_le_card_of_injOn (fun v => v.1)
  · intro v hv
    have hv' : (G.induce K.supp).degree v = 3 := by simpa using hv
    have hG : G.degree v.1 = 3 := by
      rw [← induce_supp_degree G K v]
      exact hv'
    simpa using hG
  · intro a _ b _ h
    exact Subtype.ext h

/-- t ≤ 2 TOP THEOREM (UNCONDITIONAL; the first unconditional mixed-class
statement): every finite simple graph with all degrees in `{3, 4}` and at
most two degree-3 vertices has a strong majority 4-coloring.  Component lift
verbatim from Pins2's `R4_three_four` (the per-component `numDeg3` bound
transfers by `numDeg3_induce_le`). -/
theorem R4_three_four_t2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  have hcol : ∀ K : G.ConnectedComponent, ∃ c : Sym2 K.supp → Fin 4,
      SMaj.IsStrongMajority (G.induce K.supp) c := by
    intro K
    apply R4_three_four_connected_t2 _ (K.maximal_connected_induce_supp).1
    · intro v
      rw [induce_supp_degree G K v]
      exact hdeg v.1
    · exact le_trans (numDeg3_induce_le G K) ht2
  choose col hcolp using hcol
  refine ⟨glue G col, ?_⟩
  intro u v huv α
  have hu : u ∈ (G.connectedComponentMk u).supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ (G.connectedComponentMk u).supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
  have hadj : (G.induce (G.connectedComponentMk u).supp).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    rw [induce_adj]; exact huv
  have hb := hcolp (G.connectedComponentMk u) ⟨u, hu⟩ ⟨v, hv⟩ hadj α
  rw [nColor_glue_eq G col huv hu hv α]
  rw [induce_supp_degree G _ ⟨u, hu⟩, induce_supp_degree G _ ⟨v, hv⟩] at hb
  exact hb

end Rung4Moonshot
