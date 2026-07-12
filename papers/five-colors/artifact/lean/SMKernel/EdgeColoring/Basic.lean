/-
SMKernel/EdgeColoring/Basic.lean — proper edge colorings of simple graphs:
palettes, missing sets, `EdgeColorable`, critical edges.

SM kernel campaign (`problems/p5-strongmajority/KERNEL-CAMPAIGN.md` §3).
Design notes (load-bearing, inherited from the SMaj tree conventions):

* An edge coloring is a TOTAL function `c : Sym2 V → C`; only its values on
  `G.edgeSet` are meaningful.  This avoids subtype friction and keeps every
  definition `decide`-friendly (the reading-kit demos below need no trust).
* Colorings of `G − e` are colorings of `G.deleteEdges {e}` — no partial
  functions, no `Option C`.  Missing sets are computed in the deletion graph.
* Everything lives in `namespace SimpleGraph` with mathlib naming/style so
  upstreaming (`Mathlib/Combinatorics/SimpleGraph/EdgeColoring/Basic.lean`)
  is extraction, not rewrite.  mathlib at the campaign pin (v4.28.0 /
  8f9d9cff) has no proper-edge-coloring theory (`EdgeLabeling` is
  unrestricted; `LineGraph` carries no coloring API).
-/
import Mathlib

namespace SimpleGraph

variable {V : Type*} {C : Type*}
variable (G : SimpleGraph V)

/-! ### Proper edge colorings -/

/-- A total function `c : Sym2 V → C` is a *proper edge coloring* of `G` if
any two distinct edges of `G` sharing an endpoint receive different colors.
Only the values of `c` on `G.edgeSet` are constrained. -/
def IsProperEdgeColoring (c : Sym2 V → C) : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj u w → v ≠ w → c s(u, v) ≠ c s(u, w)

instance [Fintype V] [DecidableEq V] [DecidableEq C] [DecidableRel G.Adj]
    (c : Sym2 V → C) : Decidable (G.IsProperEdgeColoring c) := by
  unfold IsProperEdgeColoring; infer_instance

/-- Properness transfers down subgraph inclusions (same vertex type). -/
theorem IsProperEdgeColoring.mono {G H : SimpleGraph V} {c : Sym2 V → C}
    (hHG : H ≤ G) (hc : G.IsProperEdgeColoring c) : H.IsProperEdgeColoring c :=
  fun _ _ _ ha hb => hc (hHG ha) (hHG hb)

/-- Every edge of `G` incident to `v` is `s(v, w)` for a neighbor `w`. -/
lemma exists_adj_eq_of_mem_incidenceSet {v : V} {e : Sym2 V}
    (h : e ∈ G.incidenceSet v) : ∃ w, G.Adj v w ∧ e = s(v, w) := by
  obtain ⟨he, hv⟩ := h
  induction e with
  | _ x y =>
    rw [mem_edgeSet] at he
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨y, he, rfl⟩
    · exact ⟨x, he.symm, Sym2.eq_swap⟩

/-! ### Palettes and missing sets -/

section Palette

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]

/-- The set of colors *present* at `v`: the image of the incident edges. -/
def presentColors (c : Sym2 V → C) (v : V) : Finset C :=
  (G.incidenceFinset v).image c

/-- The set of colors *missing* at `v` (the palette is all of `C`): written
`φ̄(v)` in the edge-coloring literature. -/
def missingColors [Fintype C] (c : Sym2 V → C) (v : V) : Finset C :=
  Finset.univ \ G.presentColors c v

lemma mem_presentColors {c : Sym2 V → C} {v : V} {α : C} :
    α ∈ G.presentColors c v ↔ ∃ e ∈ G.incidenceFinset v, c e = α := by
  simp [presentColors]

lemma mem_missingColors [Fintype C] {c : Sym2 V → C} {v : V} {α : C} :
    α ∈ G.missingColors c v ↔ ∀ e ∈ G.incidenceFinset v, c e ≠ α := by
  simp [missingColors, mem_presentColors]

end Palette

/-- Decidability transport for edge-deleted graphs (single edge). -/
instance [DecidableEq V] [DecidableRel G.Adj] (e : Sym2 V) :
    DecidableRel (G.deleteEdges {e}).Adj := fun u v =>
  decidable_of_iff (G.Adj u v ∧ ¬s(u, v) = e) (by
    rw [deleteEdges_adj]; simp)

/-! ### Palette counting (kernel-returned, tranche smk1_palette,
Aristotle f06185da, audited 2026-07-11) -/

/-- A proper edge coloring shows `d(v)` distinct colors at `v`:
the incident edges carry pairwise distinct colors. -/
theorem card_presentColors_of_isProperEdgeColoring
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]
    {c : Sym2 V → C} (hc : G.IsProperEdgeColoring c) (v : V) :
    (G.presentColors c v).card = G.degree v := by
  convert Finset.card_image_of_injOn _;
  · simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
  · intro e he f hf h; have := hc; simp_all +decide [ SimpleGraph.incidenceSet ] ;
    cases he.2 ; cases hf.2 ; simp_all +decide [ SimpleGraph.IsProperEdgeColoring ] ;
    exact Or.inl ( Classical.not_not.1 fun h' => this he hf h' h )

/-- Missing-set size: `|φ̄(v)| = |C| − d(v)`. -/
theorem card_missingColors_of_isProperEdgeColoring
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype C] [DecidableEq C]
    {c : Sym2 V → C} (hc : G.IsProperEdgeColoring c) (v : V) :
    (G.missingColors c v).card = Fintype.card C - G.degree v := by
  rw [ ← card_presentColors_of_isProperEdgeColoring G hc v ];
  rw [ SimpleGraph.missingColors, Finset.card_sdiff ] ; aesop

/-- Deleting one incident edge drops the degree by one (the deletion-graph
degree bookkeeping at the endpoints of the uncolored edge:
`|φ̄(v₀)| = |C| − d(v₀) + 1` follows from this and the previous lemma). -/
theorem degree_deleteEdges_of_adj
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v w : V} (h : G.Adj v w) :
    (G.deleteEdges {s(v, w)}).degree v = G.degree v - 1 := by
  simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
  rw [ ← Finset.card_erase_add_one ( show w ∈ Finset.filter ( fun x => G.Adj v x ) Finset.univ from Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ) ] ; congr ; ext x ; by_cases hx : x = w <;> aesop;

/-- Membership in the present set, neighbor form. -/
theorem mem_presentColors_iff_exists_adj
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]
    {c : Sym2 V → C} {v : V} {α : C} :
    α ∈ G.presentColors c v ↔ ∃ w, G.Adj v w ∧ c s(v, w) = α := by
  simp [SimpleGraph.presentColors, SimpleGraph.incidenceSet];
  constructor;
  · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
    obtain ⟨ w, hw ⟩ := ha₂;
    aesop;
  · rintro ⟨ w, hw, rfl ⟩ ; exact ⟨ _, ⟨ hw, by simp +decide ⟩, rfl ⟩

/-! ### Bounded edge colorability, criticality -/

/-- `G.EdgeColorable n`: `G` has a proper edge coloring with (at most) `n`
colors.  The bounded-palette analogue of `SimpleGraph.Colorable`. -/
def EdgeColorable (n : ℕ) : Prop :=
  ∃ c : Sym2 V → Fin n, G.IsProperEdgeColoring c

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (n : ℕ) :
    Decidable (G.EdgeColorable n) := by
  unfold EdgeColorable; infer_instance

/-- Colorability is monotone in the palette size. -/
theorem EdgeColorable.mono {G : SimpleGraph V} {m n : ℕ}
    (h : G.EdgeColorable m) (hmn : m ≤ n) : G.EdgeColorable n := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun e => Fin.castLE hmn (c e),
    fun _ _ _ ha hb hne hcc => hc ha hb hne (Fin.castLE_injective hmn hcc)⟩

/-- Colorability is antitone in the graph. -/
theorem EdgeColorable.anti {G H : SimpleGraph V} {n : ℕ}
    (hHG : H ≤ G) (h : G.EdgeColorable n) : H.EdgeColorable n := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono hHG⟩

/-- `e` is an *`n`-critical edge* of `G`: `G` is not `n`-edge-colorable but
`G − e` is.  Used with `n = Δ(G)`; "class two with a critical edge" in the
literature.  (No Vizing is stated or consumed anywhere in this development.) -/
def IsCriticalEdge (n : ℕ) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ¬G.EdgeColorable n ∧ (G.deleteEdges {e}).EdgeColorable n

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (n : ℕ) (e : Sym2 V) :
    Decidable (G.IsCriticalEdge n e) := by
  unfold IsCriticalEdge; infer_instance

/-! ### Reading-kit validation demos (small-n, kernel-checked, no trust needed)

The definitions above are pinned by `decide` on concrete graphs. -/

section Demos

set_option maxRecDepth 8000

-- K₄: the perfect-matching 3-edge-coloring is proper (χ′(K₄) = 3 = Δ,
-- class one), pinned explicitly.
example : (⊤ : SimpleGraph (Fin 4)).IsProperEdgeColoring
    (fun e => if e = s(0, 1) ∨ e = s(2, 3) then (0 : Fin 3)
      else if e = s(0, 2) ∨ e = s(1, 3) then 1 else 2) := by decide

-- ... and the constant coloring is NOT proper on K₄.
example : ¬(⊤ : SimpleGraph (Fin 4)).IsProperEdgeColoring
    (fun _ => (0 : Fin 3)) := by decide

-- Palette bookkeeping on the triangle with a coloring of (⊤ − s(0,1)) = P₃:
-- both colors present at the middle vertex 2, one missing at each endpoint.
example : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).missingColors
    (fun e => if e = s(0, 2) then (0 : Fin 2) else 1) 0 = {1} := by decide
example : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).missingColors
    (fun e => if e = s(0, 2) then (0 : Fin 2) else 1) 1 = {0} := by decide
example : ((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).missingColors
    (fun e => if e = s(0, 2) then (0 : Fin 2) else 1) 2 = ∅ := by decide

-- The triangle is 3-edge-colorable (explicit witness; no enumeration —
-- `∃`-over-a-function-space kernel enumeration is out of reach, so the
-- colorability demos are witness- and pigeonhole-based).
example : (⊤ : SimpleGraph (Fin 3)).EdgeColorable 3 :=
  ⟨fun e => if e = s(0, 1) then 0 else if e = s(0, 2) then 1 else 2,
    by decide⟩

/-- The triangle is NOT 2-edge-colorable: its three edges are pairwise
adjacent, and `Fin 2` has no three pairwise-distinct elements. -/
lemma not_edgeColorable_two_triangle : ¬(⊤ : SimpleGraph (Fin 3)).EdgeColorable 2 := by
  rintro ⟨c, hc⟩
  have swap : ∀ a b : Fin 3, c s(a, b) = c s(b, a) := fun a b => by
    rw [Sym2.eq_swap]
  have h1 : c s(0, 1) ≠ c s(0, 2) := hc (by decide) (by decide) (by decide)
  have h2 : c s(1, 0) ≠ c s(1, 2) := hc (by decide) (by decide) (by decide)
  have h3 : c s(2, 0) ≠ c s(2, 1) := hc (by decide) (by decide) (by decide)
  rw [← swap 0 1] at h2
  rw [← swap 0 2, ← swap 1 2] at h3
  have key : ∀ a b d : Fin 2, a ≠ b → a ≠ d → b ≠ d → False := by decide
  exact key _ _ _ h1 h2 h3

-- Criticality: s(0,1) is a 2-critical edge of the triangle (C₃ is class
-- two at Δ = 2; deleting an edge leaves the 2-edge-colorable path P₃).
example : (⊤ : SimpleGraph (Fin 3)).IsCriticalEdge 2 s(0, 1) :=
  ⟨by decide, not_edgeColorable_two_triangle,
    ⟨fun e => if e = s(0, 2) then 0 else 1, by decide⟩⟩

-- Non-example: K₄ has NO 3-critical edge (K₄ is class one already).
example : ¬(⊤ : SimpleGraph (Fin 4)).IsCriticalEdge 3 s(0, 1) := fun h =>
  h.2.1 ⟨fun e => if e = s(0, 1) ∨ e = s(2, 3) then (0 : Fin 3)
    else if e = s(0, 2) ∨ e = s(1, 3) then 1 else 2, by decide⟩

end Demos

end SimpleGraph
