/-
SMKernel/EdgeColoring/DFamily.lean — the clause-(d) coloring family 𝒫
(TR DMF-2006-10-003 Thm 7.2(d) proof, pp. 26–28, with repair F-R1).

SM kernel campaign, tranche smk4.  Shape AUDITED before pinning
(gpt-5.6-sol second round, 2026-07-11, thread 019f4fc0-b777-74b3-846c-
031f485c8f74): the draft family was REJECTED and repaired — three
additional load-bearing fields (`delta_mem`, `alpha_mem`, `missing_v2`)
beyond the reconstruction's F-R1 field (`missing_v0`).  Path geometry
(adjacency, distinctness) is deliberately NOT in the family: it is static
data, passed to the step/endgame lemmas separately.

Binding (d)-trap list from the audit (for every smk4+ payload):
* Γ is FIXED by the initial coloring; never re-derived from the current π.
* δ ∈ Γ and α ∈ Γ \ {δ} are load-bearing for step S / Claim 1.
* δ ∉ φ̄π(v0) comes from `missing_v0` for the CURRENT π, never from the
  initial Lemma A silently reused.
* v3 is not an endpoint of the deleted edge: |φ̄(v3)| = n − d_G(v3) (the
  interior formula, not the endpoint n − d + 1).
* Endgame: e₃ ∈ P via Kempe-adjacency of v3, v2 and reach-set membership;
  the explicit `kempeSwap` value gives π'(e₃) = δ; β ≠ α by properness at
  v2 on the distinct edges e₂, e₃; β ≠ δ because e₃ ∋ v3 misses δ.
* `2 ≤ card` vs `card ≤ 1`: keep the contradiction in ℕ arithmetic.
-/
import SMKernel.EdgeColoring.Linkage

namespace SimpleGraph

variable {V : Type*}

/-- The clause-(d) coloring family 𝒫 (TR p. 27 + repair F-R1).  Parameters:
`α` the fixed color of `e₂ = s(v1,v2)`, `δ` the unique color missing at
`v1`, `Γ` the union of the two endpoint missing sets OF THE INITIAL
coloring (fixed once, a parameter).  `missing_v0` is the F-R1 invariant —
the TR omits it and uses it silently three times; it holds initially by
Lemma A + counting and is preserved by every step-S swap. -/
structure IsDFamilyMember [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (v0 v1 v2 v3 : V) (α δ : Fin n)
    (Γ : Finset (Fin n)) (π : Sym2 V → Fin n) : Prop where
  proper :
    (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring π
  delta_mem :
    δ ∈ Γ
  alpha_mem :
    α ∈ Γ \ {δ}
  e2_eq :
    π s(v1, v2) = α
  missing_v1 :
    (G.deleteEdges {s(v0, v1)}).missingColors π v1 = {δ}
  missing_v2 :
    (G.deleteEdges {s(v0, v1)}).missingColors π v2 = ∅
  e3_mem :
    π s(v2, v3) ∈ Γ
  card_ge :
    2 ≤
      ((G.deleteEdges {s(v0, v1)}).missingColors π v3 ∩ Γ).card
  missing_v0 :
    (G.deleteEdges {s(v0, v1)}).missingColors π v0 = Γ \ {δ}

/-! ### Step S (kernel-returned, tranche smk4_step, Aristotle audited
2026-07-11, 3/3 with linkage/separation cross-confirms) -/

set_option maxHeartbeats 1600000 in
/-- **Step S** (the explicit family-preserving swap).  Swapping the
(c1,δ)-chain through v₃ keeps the family and toggles {c1,δ}-membership
at v₃. -/
theorem IsDFamilyMember.step
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {v0 v1 v2 v3 : V}
    {α δ c1 : Fin n} {Γ : Finset (Fin n)}
    {π : Sym2 V → Fin n}
    (hG : ¬G.EdgeColorable n)
    (hnodup : (v0 :: v1 :: [v2, v3]).Nodup)
    (hchain : (v0 :: v1 :: [v2, v3]).IsChain G.Adj)
    (hmem : IsDFamilyMember G v0 v1 v2 v3 α δ Γ π)
    (hc1 : c1 ∈ Γ \ {δ})
    (hxor :
      Xor'
        (c1 ∈ (G.deleteEdges {s(v0, v1)}).missingColors π v3)
        (δ ∈ (G.deleteEdges {s(v0, v1)}).missingColors π v3)) :
    IsDFamilyMember G v0 v1 v2 v3 α δ Γ
      (kempeSwap π c1 δ
        (((G.deleteEdges {s(v0, v1)}).kempeGraph π c1 δ).reachFinset v3)) ∧
    (c1 ∈ (G.deleteEdges {s(v0, v1)}).missingColors
        (kempeSwap π c1 δ
          (((G.deleteEdges {s(v0, v1)}).kempeGraph π c1 δ).reachFinset v3))
        v3 ↔
      δ ∈ (G.deleteEdges {s(v0, v1)}).missingColors π v3) ∧
    (δ ∈ (G.deleteEdges {s(v0, v1)}).missingColors
        (kempeSwap π c1 δ
          (((G.deleteEdges {s(v0, v1)}).kempeGraph π c1 δ).reachFinset v3))
        v3 ↔
      c1 ∈ (G.deleteEdges {s(v0, v1)}).missingColors π v3) := by
  obtain ⟨hproper, hdelta_mem, halpha_mem, he2_eq, hmissing_v1, hmissing_v2, he3_mem, hcard_ge, hmissing_v0⟩ := hmem;
  simp_all +decide [ List.isChain_cons ];
  set H := G.deleteEdges {s(v0, v1)}
  set K := (H.kempeGraph π c1 δ).reachFinset v3;
  have hv0 : v0 ∉ K := by
    have h_not_reachable : ¬(H.kempeGraph π c1 δ).Reachable v0 v3 := by
      apply not_reachable_kempeGraph_of_missing_of_ne;
      all_goals try tauto;
      · grind;
      · exact hmissing_v1.symm ▸ Finset.mem_singleton_self _;
      · exact hxor.elim ( fun h => Or.inl h.1 ) fun h => Or.inr h.1;
    exact fun h => h_not_reachable <| mem_reachFinset.mp h |> fun h => h.symm
  have hv1 : v1 ∉ K := by
    have := @not_reachable_kempeGraph_of_missing_of_ne;
    specialize @this V _ _ G _ n π v1 v0 v3 δ c1;
    simp_all +decide [ SimpleGraph.adj_comm, Sym2.eq_swap ];
    contrapose! this;
    exact ⟨ hproper, by tauto, by tauto, by cases hxor <;> tauto, by simpa only [ SimpleGraph.kempeGraph_comm ] using mem_reachFinset.mp this |> SimpleGraph.Reachable.symm ⟩
  have hv3 : v3 ∈ K := by
    exact self_mem_reachFinset _ _;
  have hproper' : H.IsProperEdgeColoring (kempeSwap π c1 δ K) := by
    apply SimpleGraph.IsProperEdgeColoring.kempeSwap_of_isKempeClosed;
    · exact hproper;
    · exact isKempeClosed_reachFinset H π c1 δ v3
  have hmissing_v1' : H.missingColors (kempeSwap π c1 δ K) v1 = {δ} := by
    rw [ SimpleGraph.missingColors_kempeSwap_of_not_mem ] <;> aesop
  have hmissing_v2' : H.missingColors (kempeSwap π c1 δ K) v2 = ∅ := by
    by_cases hv2 : v2 ∈ K <;> simp_all +decide [ SimpleGraph.missingColors_kempeSwap_of_not_mem ];
    · convert missingColors_kempeSwap_of_mem H ( isKempeClosed_reachFinset H π c1 δ v3 ) hv2 using 1;
      grind;
    · exact hmissing_v2
  have he3_mem' : kempeSwap π c1 δ K s(v2, v3) ∈ Γ := by
    by_cases hv2 : v2 ∈ K;
    · rw [ SimpleGraph.kempeSwap_apply_eq_kempeSwapColor_of_mem ];
      any_goals assumption;
      · grind +suggestions;
      · exact isKempeClosed_reachFinset H π c1 δ v3;
      · simp +zetaDelta at *;
        grind;
    · rw [ kempeSwap_apply_eq_of_not_mem hv2 ] ; aesop
  have hcard_ge' : 2 ≤ (H.missingColors (kempeSwap π c1 δ K) v3 ∩ Γ).card := by
    have hmissing_v3' : H.missingColors (kempeSwap π c1 δ K) v3 = (H.missingColors π v3).image (kempeSwapColor c1 δ) := by
      apply missingColors_kempeSwap_of_mem;
      · exact isKempeClosed_reachFinset H π c1 δ v3;
      · exact hv3;
    refine' le_trans hcard_ge _;
    refine' le_trans _ ( Finset.card_mono _ );
    rotate_left;
    exact Finset.image ( kempeSwapColor c1 δ ) ( H.missingColors π v3 ∩ Γ );
    · simp +decide [ Finset.subset_iff, hmissing_v3' ];
      grind +suggestions;
    · rw [ Finset.card_image_of_injective _ ( SimpleGraph.kempeSwapColor_injective _ _ ) ]
  have hmissing_v0' : H.missingColors (kempeSwap π c1 δ K) v0 = Γ \ {δ} := by
    rw [ ← hmissing_v0, missingColors_kempeSwap_of_not_mem ] ; aesop;
  refine' ⟨ _, _ ⟩;
  · use hproper', hdelta_mem, by aesop, by
      rw [ kempeSwap_apply_eq_of_not_mem ] <;> aesop, hmissing_v1', hmissing_v2', he3_mem', hcard_ge', hmissing_v0';
  · have hmissing_v3' : H.missingColors (kempeSwap π c1 δ K) v3 = (H.missingColors π v3).image (kempeSwapColor c1 δ) := by
      apply missingColors_kempeSwap_of_mem;
      · exact isKempeClosed_reachFinset H π c1 δ v3;
      · exact hv3;
    grind +suggestions

/-! ### Reading-kit validation demos (small-n, kernel-checked)

The family is a strong invariant: its fields are individually pinned by
`decide` on the C₅ configuration, where the entry condition `card_ge`
correctly FAILS (|φ̄(v₃) ∩ Γ| ≥ 2 is exactly what Theorem A refutes —
on C₅, φ̄(3) = ∅). -/

section Demos

set_option maxRecDepth 8000

private def C5 : SimpleGraph (Fin 5) where
  Adj x y := y = x + 1 ∨ x = y + 1
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

private instance : DecidableRel C5.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

private def c5col : Sym2 (Fin 5) → Fin 2 := fun e =>
  if e = s(1, 2) ∨ e = s(3, 4) then 0 else 1

-- the rigid fields hold on the C₅ configuration with α = 0, δ = 1,
-- Γ = {0, 1} …
example : c5col s(1, 2) = 0 := by decide
example : (C5.deleteEdges {s(0, 1)}).missingColors c5col 1 = {1} := by decide
example : (C5.deleteEdges {s(0, 1)}).missingColors c5col 2 = ∅ := by decide
example : c5col s(2, 3) ∈ ({0, 1} : Finset (Fin 2)) := by decide
example : (C5.deleteEdges {s(0, 1)}).missingColors c5col 0 =
    ({0, 1} : Finset (Fin 2)) \ {1} := by decide
-- … and the entry condition card_ge fails, exactly as Theorem A demands:
example : ¬(2 ≤ ((C5.deleteEdges {s(0, 1)}).missingColors c5col 3 ∩
    ({0, 1} : Finset (Fin 2))).card) := by decide

end Demos

end SimpleGraph
