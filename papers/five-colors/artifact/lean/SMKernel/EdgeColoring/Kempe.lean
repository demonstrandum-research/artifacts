/-
SMKernel/EdgeColoring/Kempe.lean — Kempe machinery: the two-color subgraph
and the Kempe swap.

SM kernel campaign (`problems/p5-strongmajority/KERNEL-CAMPAIGN.md` §3).
Design notes (load-bearing):

* `kempeGraph G c α β` is the subgraph of `G` on the edges colored `α` or
  `β`.  For a proper coloring it has maximum degree ≤ 2 (smk1 payload
  target), so its components are paths or cycles — that decomposition is
  DERIVED, never assumed.
* The swap `kempeSwap c α β K` exchanges `α ↔ β` on every edge with both
  ends in the finite vertex set `K`, and fixes everything else.  All the
  swap lemmas require only that `K` is *Kempe-closed*
  (`IsKempeClosed`: no `{α,β}`-edge crosses the boundary of `K`) — strictly
  weaker than being a connected component of `kempeGraph`, which keeps the
  lemma statements independent of any particular component API.
* `kempeSwapColor α β` is the color-level transposition; it is an involution
  and fixes colors outside `{α, β}` (proved here — cheap and foundational).
-/
import SMKernel.EdgeColoring.Basic

namespace SimpleGraph

variable {V : Type*} {C : Type*}
variable (G : SimpleGraph V)

/-! ### The two-color (Kempe) subgraph -/

/-- The *Kempe subgraph* of `G` under the coloring `c` for the color pair
`(α, β)`: keep exactly the edges colored `α` or `β`. -/
def kempeGraph (c : Sym2 V → C) (α β : C) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (c s(u, v) = α ∨ c s(u, v) = β)
  symm := fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun u h => G.irrefl h.1⟩

@[simp]
lemma kempeGraph_adj {c : Sym2 V → C} {α β : C} {u v : V} :
    (G.kempeGraph c α β).Adj u v ↔
      G.Adj u v ∧ (c s(u, v) = α ∨ c s(u, v) = β) := Iff.rfl

instance [DecidableEq C] [DecidableRel G.Adj] (c : Sym2 V → C) (α β : C) :
    DecidableRel (G.kempeGraph c α β).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ _))

/-- The Kempe subgraph is a subgraph. -/
theorem kempeGraph_le (c : Sym2 V → C) (α β : C) : G.kempeGraph c α β ≤ G :=
  fun _ _ h => h.1

/-- Color symmetry of the Kempe subgraph. -/
theorem kempeGraph_comm (c : Sym2 V → C) (α β : C) :
    G.kempeGraph c α β = G.kempeGraph c β α := by
  ext u v
  exact and_congr_right fun _ => or_comm

/-! ### The color transposition and the Kempe swap -/

/-- Transposition of the two colors `α, β` at the color level; every other
color is fixed. -/
def kempeSwapColor [DecidableEq C] (α β γ : C) : C :=
  if γ = α then β else if γ = β then α else γ

section SwapColor

variable [DecidableEq C] {α β γ : C}

@[simp] lemma kempeSwapColor_left : kempeSwapColor α β α = β := by
  simp [kempeSwapColor]

@[simp] lemma kempeSwapColor_right : kempeSwapColor α β β = α := by
  unfold kempeSwapColor
  split_ifs with h <;> simp_all

lemma kempeSwapColor_of_ne (hα : γ ≠ α) (hβ : γ ≠ β) :
    kempeSwapColor α β γ = γ := by
  simp [kempeSwapColor, hα, hβ]

/-- The color transposition is an involution. -/
@[simp] theorem kempeSwapColor_kempeSwapColor (α β γ : C) :
    kempeSwapColor α β (kempeSwapColor α β γ) = γ := by
  unfold kempeSwapColor
  split_ifs <;> simp_all

/-- The color transposition is an involution (function form). -/
theorem kempeSwapColor_involutive (α β : C) :
    Function.Involutive (kempeSwapColor α β) :=
  kempeSwapColor_kempeSwapColor α β

/-- The color transposition is injective. -/
theorem kempeSwapColor_injective (α β : C) :
    Function.Injective (kempeSwapColor α β) :=
  (kempeSwapColor_involutive α β).injective

/-- The color transposition is surjective. -/
theorem kempeSwapColor_surjective (α β : C) :
    Function.Surjective (kempeSwapColor α β) :=
  (kempeSwapColor_involutive α β).surjective

/-- The transposition preserves membership of `{α, β}`. -/
lemma kempeSwapColor_mem_pair_iff :
    (kempeSwapColor α β γ = α ∨ kempeSwapColor α β γ = β) ↔
      (γ = α ∨ γ = β) := by
  unfold kempeSwapColor
  split_ifs <;> simp_all

end SwapColor

/-- The *Kempe swap*: exchange the colors `α ↔ β` on every edge with both
endpoints in `K`; every other edge keeps its color.  (Colors outside
`{α, β}` are fixed by `kempeSwapColor`, so only `{α,β}`-edges inside `K`
actually move.) -/
def kempeSwap [DecidableEq V] [DecidableEq C] (c : Sym2 V → C) (α β : C)
    (K : Finset V) (e : Sym2 V) : C :=
  if e ∈ K.sym2 then kempeSwapColor α β (c e) else c e

/-- `K` is *Kempe-closed* for `G, c, α, β`: no edge of the Kempe subgraph
crosses the boundary of `K`.  Connected-component supports are Kempe-closed;
the swap lemmas need only this. -/
def IsKempeClosed (c : Sym2 V → C) (α β : C) (K : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, (G.kempeGraph c α β).Adj u v → (u ∈ K ↔ v ∈ K)

instance [Fintype V] [DecidableEq V] [DecidableEq C] [DecidableRel G.Adj]
    (c : Sym2 V → C) (α β : C) (K : Finset V) :
    Decidable (G.IsKempeClosed c α β K) := by
  unfold IsKempeClosed; infer_instance

section Swap

variable [DecidableEq V] [DecidableEq C]

lemma kempeSwap_apply_of_mem {c : Sym2 V → C} {α β : C} {K : Finset V}
    {u v : V} (hu : u ∈ K) (hv : v ∈ K) :
    kempeSwap c α β K s(u, v) = kempeSwapColor α β (c s(u, v)) := by
  rw [kempeSwap, if_pos (Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩)]

lemma kempeSwap_apply_of_not_mem {c : Sym2 V → C} {α β : C} {K : Finset V}
    {u v : V} (hu : u ∉ K) :
    kempeSwap c α β K s(u, v) = c s(u, v) := by
  rw [kempeSwap, if_neg]
  intro h
  exact hu (Finset.mk_mem_sym2_iff.mp h).1

/-- The Kempe swap is an involution on colorings. -/
theorem kempeSwap_kempeSwap (c : Sym2 V → C) (α β : C) (K : Finset V) :
    kempeSwap (kempeSwap c α β K) α β K = c := by
  funext e
  unfold kempeSwap
  split_ifs with h <;> simp

end Swap

/-! ### Kempe-graph degree bounds (kernel-returned, tranche smk1_kempe_deg,
Aristotle c05bf13e, audited 2026-07-11) -/

section KempeDegree

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]

omit [DecidableEq V] in
/-- In a proper edge coloring, at most one edge of each color at each
vertex. -/
theorem card_filter_color_neighbors_le_one
    {c : Sym2 V → C} (hc : G.IsProperEdgeColoring c) (v : V) (α : C) :
    (Finset.filter (fun w => c s(v, w) = α) (G.neighborFinset v)).card ≤ 1 := by
  refine' Finset.card_le_one.mpr _;
  simp +zetaDelta at *;
  exact fun a ha ha' b hb hb' => Classical.not_not.1 fun hab => hc ha hb hab <| ha'.trans hb'.symm

/-- The Kempe neighborhood splits into the `α`-neighbors and the
`β`-neighbors. -/
theorem neighborFinset_kempeGraph_eq
    (c : Sym2 V → C) (α β : C) (v : V) :
    (G.kempeGraph c α β).neighborFinset v =
      Finset.filter (fun w => c s(v, w) = α) (G.neighborFinset v) ∪
        Finset.filter (fun w => c s(v, w) = β) (G.neighborFinset v) := by
  ext w; simp [SimpleGraph.kempeGraph] ; aesop;

/-- The Kempe subgraph of a proper coloring has maximum degree at most
two. -/
theorem degree_kempeGraph_le_two
    {c : Sym2 V → C} (hc : G.IsProperEdgeColoring c) (α β : C) (v : V) :
    (G.kempeGraph c α β).degree v ≤ 2 := by
  convert Finset.card_union_le _ _ |> le_trans <| add_le_add ( card_filter_color_neighbors_le_one G hc v α ) ( card_filter_color_neighbors_le_one G hc v β ) using 1;
  convert congr_arg Finset.card ( neighborFinset_kempeGraph_eq G c α β v )

end KempeDegree

/-! ### Reading-kit validation demos (small-n, kernel-checked) -/

section Demos

set_option maxRecDepth 100000

-- On K₄ with the perfect-matching coloring, the (0,1)-Kempe subgraph is the
-- 4-cycle 0-1-3-2-0 (matchings 0 and 1 united); the (0,2)-subgraph likewise.
-- Pinned by decide: vertex 0 has kempe-degree 2, and edge s(0,3) (color 2)
-- is NOT in the (0,1)-Kempe subgraph.
private def K4c : Sym2 (Fin 4) → Fin 3 := fun e =>
  if e = s(0, 1) ∨ e = s(2, 3) then 0
  else if e = s(0, 2) ∨ e = s(1, 3) then 1 else 2

example : ((⊤ : SimpleGraph (Fin 4)).kempeGraph K4c 0 1).degree 0 = 2 := by
  decide
example : ¬((⊤ : SimpleGraph (Fin 4)).kempeGraph K4c 0 1).Adj 0 3 := by
  decide

-- Swapping colors 0 ↔ 1 on the whole vertex set of K₄ is again a proper
-- coloring, and the double swap restores the original — pinned by decide.
example : (⊤ : SimpleGraph (Fin 4)).IsProperEdgeColoring
    (kempeSwap K4c 0 1 Finset.univ) := by decide
example : ∀ e, kempeSwap (kempeSwap K4c 0 1 Finset.univ) 0 1 Finset.univ e
    = K4c e := by decide

-- The whole vertex set is always Kempe-closed; so is the empty set.
example : (⊤ : SimpleGraph (Fin 4)).IsKempeClosed K4c 0 1 Finset.univ := by
  decide
example : (⊤ : SimpleGraph (Fin 4)).IsKempeClosed K4c 0 1 ∅ := by decide

-- A NON-closed set: {0} cuts the (0,1)-Kempe edge s(0,1).
example : ¬(⊤ : SimpleGraph (Fin 4)).IsKempeClosed K4c 0 1 {0} := by decide

-- Boundary-crossing swap on a non-closed set CAN break properness: swapping
-- only inside {0, 1} recolors s(0,1) from 0 to 1, clashing with s(1,3).
example : ¬(⊤ : SimpleGraph (Fin 4)).IsProperEdgeColoring
    (kempeSwap K4c 0 1 {0, 1}) := by decide

end Demos

end SimpleGraph
