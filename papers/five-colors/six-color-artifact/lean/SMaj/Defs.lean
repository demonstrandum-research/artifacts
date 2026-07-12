/-
SMaj/Defs.lean — frozen definitions for the strong majority edge-coloring
conjecture (Kalinowski–Kamyczura–Pilśniak–Woźniak, arXiv:2605.23828,
Conjecture 14), per the Program SM dossier PROBLEM.md §1–2.

Design notes (load-bearing):
* An edge coloring is a TOTAL function `c : Sym2 V → C`; only its values on
  `G.edgeSet` ever matter (every row below is a subset of edges).  This avoids
  subtype friction with `G.edgeSet`.
* The row of an edge `uv` is built from `incidenceFinset` of the two
  endpoints, with the edge itself erased; `card_row` certifies that this
  matches the paper's d_L(e) = d(u) + d(v) − 2 (dossier §7-A1), so the
  arithmetic cap `(d(u) + d(v) − 2)/2` used in `IsStrongMajority` is exactly
  the paper's ⌊d_L(e)/2⌋ (dossier §1.2 pinned form).
-/
import Mathlib

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-- The `u`-side of the row of the edge `s(u,v)`: edges at `u` other than
`s(u,v)` itself. -/
def side (u v : V) : Finset (Sym2 V) := (G.incidenceFinset u).erase s(u, v)

/-- The row of the edge `s(u,v)`: all edges adjacent to it (sharing an
endpoint, the edge itself excluded). -/
def row (u v : V) : Finset (Sym2 V) := side G u v ∪ side G v u

/-- The number of edges of color `α` adjacent to the edge `s(u,v)`. -/
def nColor (c : Sym2 V → C) (u v : V) (α : C) : ℕ :=
  #{f ∈ row G u v | c f = α}

/-- Strong majority edge-coloring (PROBLEM.md §1.2, pinned integer form):
for every edge `uv` and EVERY color `α` (including the edge's own color),
at most ⌊(d(u)+d(v)−2)/2⌋ adjacent edges have color `α`. -/
def IsStrongMajority (c : Sym2 V → C) : Prop :=
  ∀ u v, G.Adj u v → ∀ α : C, nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2

/-- Admissibility (PROBLEM.md §1.3, edge form §7-A4): no edge has line-degree
1, i.e. no edge has endpoint degrees {1,2}. -/
def Admissible : Prop :=
  ∀ u v, G.Adj u v → G.degree u + G.degree v ≠ 3

variable {G}

lemma mem_side {u v : V} {f : Sym2 V} :
    f ∈ side G u v ↔ f ≠ s(u, v) ∧ f ∈ G.incidenceSet u := by
  simp [side, mem_incidenceFinset]

/-- The two sides of a row are disjoint: an edge incident to both `u` and `v`
is `s(u,v)` itself (simple graph; dossier §7-A1). -/
lemma disjoint_sides {u v : V} (h : G.Adj u v) :
    Disjoint (side G u v) (side G v u) := by
  rw [Finset.disjoint_left]
  intro f hfu hfv
  rw [mem_side] at hfu hfv
  have hmem : f ∈ G.incidenceSet u ∩ G.incidenceSet v := ⟨hfu.2, hfv.2⟩
  rw [G.incidenceSet_inter_incidenceSet_of_adj h] at hmem
  exact hfu.1 hmem

lemma card_side {u v : V} (h : G.Adj u v) :
    #(side G u v) = G.degree u - 1 := by
  rw [side, card_erase_of_mem, card_incidenceFinset_eq_degree]
  rw [mem_incidenceFinset]
  exact G.mk'_mem_incidenceSet_left_iff.mpr h

/-- Sanity: the row of `uv` has exactly d(u) + d(v) − 2 members, so the cap in
`IsStrongMajority` is exactly ⌊|row|/2⌋ — the paper's "at most half of the
edges adjacent to e". -/
theorem card_row {u v : V} (h : G.Adj u v) :
    #(row G u v) = G.degree u + G.degree v - 2 := by
  rw [row, card_union_of_disjoint (disjoint_sides h), card_side h, card_side h.symm]
  have hu : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, h⟩
  have hv : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, h.symm⟩
  omega

end SMaj
