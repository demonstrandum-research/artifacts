/-
SMKernel/EdgeColoring/KempeSwap.lean — the Kempe swap laws: properness
preservation and palette transformation (charter §3 layout, [smk1→]).

KERNEL-RETURNED, tranche smk1_swap (Aristotle 22182a0a, audited
2026-07-11): statements pinned in the payload byte-identical to these;
proofs transplanted verbatim (private involution helpers of the payload
replaced by the public `kempeSwapColor_{involutive,injective,surjective}`
API of `Kempe.lean` — same statements, same proofs).

These six lemmas are the keystone of the campaign: every step of the
Kostochka–Stiebitz short-Kierstead proof is a Kempe swap followed by
exactly this palette bookkeeping.  `IsKempeClosed` is the full hypothesis;
no component/connectivity API is consumed.
-/
import SMKernel.EdgeColoring.Kempe

namespace SimpleGraph

variable {V : Type*} {C : Type*}
variable (G : SimpleGraph V)

section SwapLaws

-- Transplant fidelity: the payload carried its definitions WITHOUT simp
-- attributes; the library adds them.  Restore the payload's simp
-- environment for the transplanted proofs (scoped to this section).
attribute [-simp] kempeGraph_adj kempeSwapColor_left kempeSwapColor_right
  kempeSwapColor_kempeSwapColor

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]

omit [Fintype V] in
/-- Vertices outside `K` keep their entire palette, edge by edge: every
edge at `v ∉ K` keeps its color. -/
theorem kempeSwap_apply_eq_of_not_mem
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v w : V} (hv : v ∉ K) :
    kempeSwap c α β K s(v, w) = c s(v, w) := by
  unfold kempeSwap;
  simp +decide [ Finset.mem_sym2_iff, hv ]

omit [Fintype V] [DecidableRel G.Adj] in
/-- For `v ∈ K` with `K` Kempe-closed, every incident edge is recolored by
exactly the color transposition (boundary edges are fixed by it, interior
edges are swapped by it). -/
theorem kempeSwap_apply_eq_kempeSwapColor_of_mem
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v w : V}
    (hK : G.IsKempeClosed c α β K) (hadj : G.Adj v w) (hv : v ∈ K) :
    kempeSwap c α β K s(v, w) = kempeSwapColor α β (c s(v, w)) := by
  unfold kempeSwap;
  have := @hK v w; simp_all +decide [ SimpleGraph.kempeGraph ] ;
  unfold kempeSwapColor; aesop;

omit [Fintype V] [DecidableRel G.Adj] in
/-- Swapping a Kempe-closed vertex set preserves properness.
(Statement byte-identical to the smk1_swap payload target T1 up to two
dropped unused instance binders; proof re-derived in-tree from the
kernel-returned application laws above — the payload's tactic script was
environment-sensitive under transplant.) -/
theorem IsProperEdgeColoring.kempeSwap_of_isKempeClosed
    {c : Sym2 V → C} {α β : C} {K : Finset V}
    (hc : G.IsProperEdgeColoring c) (hK : G.IsKempeClosed c α β K) :
    G.IsProperEdgeColoring (kempeSwap c α β K) := by
  intro u v w huv huw hvw
  by_cases hu : u ∈ K
  · rw [kempeSwap_apply_eq_kempeSwapColor_of_mem G hK huv hu,
      kempeSwap_apply_eq_kempeSwapColor_of_mem G hK huw hu]
    exact fun h => hc huv huw hvw (kempeSwapColor_injective α β h)
  · rw [kempeSwap_apply_eq_of_not_mem hu, kempeSwap_apply_eq_of_not_mem hu]
    exact hc huv huw hvw

/-- Palette transformation at a vertex of a Kempe-closed set: the present
set maps through the color transposition. -/
theorem presentColors_kempeSwap_of_mem
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v : V}
    (hK : G.IsKempeClosed c α β K) (hv : v ∈ K) :
    G.presentColors (kempeSwap c α β K) v =
      (G.presentColors c v).image (kempeSwapColor α β) := by
  simp +decide only [presentColors];
  rw [ Finset.image_image, Finset.image_congr ];
  intro e he; simp_all +decide ;
  obtain ⟨w, hw⟩ : ∃ w : V, e = s(v, w) ∧ G.Adj v w := by
    rcases e with ⟨ ⟨ u, w ⟩ ⟩ ; simp_all +decide [ SimpleGraph.incidenceSet ] ;
    rcases he.2 with ( rfl | rfl ) <;> [ exact ⟨ w, Or.inl ⟨ rfl, rfl ⟩, he.1 ⟩ ; exact ⟨ u, Or.inr ⟨ rfl, rfl ⟩, he.1.symm ⟩ ];
  grind +suggestions

/-- Palette invariance off `K`: vertices outside keep both their present
and missing sets. -/
theorem presentColors_kempeSwap_of_not_mem
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v : V} (hv : v ∉ K) :
    G.presentColors (kempeSwap c α β K) v = G.presentColors c v := by
  have h_eq : ∀ e ∈ G.incidenceFinset v, kempeSwap c α β K e = c e := by
    simp_all +decide [ SimpleGraph.mem_incidenceFinset, kempeSwap ];
    intro e he h; contrapose! hv; simp_all +decide [ SimpleGraph.incidenceSet ] ;
  exact Finset.image_congr h_eq

/-- Missing-set transformation at a vertex of a Kempe-closed set. -/
theorem missingColors_kempeSwap_of_mem [Fintype C]
    {c : Sym2 V → C} {α β : C} {K : Finset V} {v : V}
    (hK : G.IsKempeClosed c α β K) (hv : v ∈ K) :
    G.missingColors (kempeSwap c α β K) v =
      (G.missingColors c v).image (kempeSwapColor α β) := by
  unfold SimpleGraph.missingColors;
  rw [ Finset.image_sdiff ];
  · rw [ presentColors_kempeSwap_of_mem ];
    · rw [ Finset.image_univ_of_surjective ( kempeSwapColor_surjective α β ) ];
    · exact hK;
    · exact hv;
  · exact kempeSwapColor_injective α β

end SwapLaws

end SimpleGraph
