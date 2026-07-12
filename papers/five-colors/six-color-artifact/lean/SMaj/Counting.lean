/-
SMaj/Counting.lean — the Counting Lemma (Lemma 1 of the technique-transfer
lens, `lenses/technique-transfer/THEOREMS.md` §1), the engine of the Master
Theorem.

Statement: if a coloring is rainbow on a grouping (at every vertex, edges in
the same group get pairwise distinct colors), then for every edge `uv` and
every color α, the number of α-colored edges adjacent to `uv` is at most
g(u) + g(v), where g(w) is the number of groups at `w`.

Formalization choices:
* A grouping is encoded as an index function `ix : V → Sym2 V → ℕ` (the group
  of an edge at a vertex is its index value); the partition-of-incident-edges
  view is recovered as the fibers of `ix v` on `G.incidenceFinset v`, and the
  number of groups at `v` is `#((G.incidenceFinset v).image (ix v))` for
  d(v) ≥ 2 and 0 for d(v) ≤ 1 (THEOREMS.md convention).  This is fully
  general: any set partition arises this way.
* Rainbowness asks injectivity of the coloring on every fiber.  Note this is
  the THEOREMS.md notion including the group containing the edge `e` itself —
  the proof handles e's own group with no special case because `e` is erased
  from the side before counting.
-/
import Mathlib
import SMaj.Defs

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

variable (G) in
/-- Number of groups at `v` of the grouping `ix`.  Vertices of degree ≤ 1
carry NO groups (THEOREMS.md §1: "Vertices of degree ≤ 1 get no groups; for
them set g(v) := 0") — their side of any row is empty, so they must not be
charged a group, or the Master Theorem's pendant-edge cases (h_s(1) = 0)
would be lost.  [Hostile-audit fix, Codex thread 019ebb57: the unconditional
image-cardinality definition made `exists_even_grouping` false at leaves.] -/
def groups (ix : V → Sym2 V → ℕ) (v : V) : ℕ :=
  if G.degree v ≤ 1 then 0 else #((G.incidenceFinset v).image (ix v))

variable (G) in
/-- `c` is rainbow on the grouping `ix`: at every vertex, two incident edges
in the same group with the same color are equal. -/
def IsRainbow (ix : V → Sym2 V → ℕ) (c : Sym2 V → C) : Prop :=
  ∀ v : V, ∀ f₁ ∈ G.incidenceFinset v, ∀ f₂ ∈ G.incidenceFinset v,
    ix v f₁ = ix v f₂ → c f₁ = c f₂ → f₁ = f₂

/-- All-implicit form of `SimpleGraph.mem_incidenceFinset` (projection-friendly). -/
lemma mem_incFinset {v : V} {f : Sym2 V} :
    f ∈ G.incidenceFinset v ↔ f ∈ G.incidenceSet v :=
  Set.mem_toFinset

/-- Per-side pigeonhole: each group contributes at most one α-edge, so a side
carries at most `groups ix u` edges of color α.  (The group of `s(u,v)` itself
needs no special treatment: its other members still have pairwise distinct
colors.  At a degree-1 endpoint the side is empty and contributes 0 = g(u);
adjacency of `u, v` is what makes the erased edge the unique incident one.) -/
lemma side_count_le {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {u v : V} (huv : G.Adj u v) (α : C) :
    #{f ∈ side G u v | c f = α} ≤ groups G ix u := by
  unfold groups
  split_ifs with hd
  · -- degree-1 endpoint: the side is empty
    have h1 : #(side G u v) = 0 := by have := card_side huv; omega
    calc #{f ∈ side G u v | c f = α} ≤ #(side G u v) := card_filter_le _ _
      _ = 0 := h1
  · apply card_le_card_of_injOn (ix u)
    · -- maps into the image of `ix u` on the incidence finset
      intro f hf
      rw [mem_coe, mem_filter, mem_side] at hf
      exact mem_coe.mpr (mem_image_of_mem _ (mem_incFinset.mpr hf.1.2))
    · -- injective on the α-colored side: same group + same color ⇒ equal
      intro f₁ h₁ f₂ h₂ hix
      rw [mem_coe, mem_filter, mem_side] at h₁ h₂
      exact hrb u f₁ (mem_incFinset.mpr h₁.1.2) f₂
        (mem_incFinset.mpr h₂.1.2) hix (h₁.2.trans h₂.2.symm)

/-- **The Counting Lemma** (THEOREMS.md, Lemma 1).  If `c` is rainbow on the
grouping `ix`, then for every edge `uv` and every color α (including the
edge's own color), the number of α-colored adjacent edges is at most
`groups ix u + groups ix v`.  No properness of `c` is needed anywhere. -/
theorem counting_lemma {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {u v : V} (huv : G.Adj u v) (α : C) :
    nColor G c u v α ≤ groups G ix u + groups G ix v := by
  unfold nColor row
  calc #{f ∈ side G u v ∪ side G v u | c f = α}
      ≤ #{f ∈ side G u v | c f = α} + #{f ∈ side G v u | c f = α} := by
        rw [filter_union]; exact card_union_le _ _
    _ ≤ groups G ix u + groups G ix v :=
        Nat.add_le_add (side_count_le hrb huv α) (side_count_le hrb huv.symm α)

end SMaj
