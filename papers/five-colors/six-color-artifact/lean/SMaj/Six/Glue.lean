/-
SMaj/Six/Glue.lean — the row-dispatch half of the (G1)–(G5) glue for
`maj_le_six` (campaign C5, lens C5L3-lean-six, 2026-06-13).

The L2 ≤ 6 proof (`lenses/L2-chain-grouping/WRITEUP.md`) splits into
  (i)  a CONSTRUCTION (G1)–(G5): grouping at junctions, chain contraction
       into a multigraph M, Shannon 6-coloring of M, port transport,
       saturated sets, interior fill; and
  (ii) a ROW CASE ANALYSIS (§4, cases (a)–(e)) showing the constructed
       coloring is strong majority.
This file closes (ii) IN FULL, against a construction-free interface:
`IsGlueColoring` packages the row-level postconditions the construction
guarantees — rainbowness, junction group counts ≤ ⌈d/4⌉, the chain-end
disjunction (l = 2 monochromatic OR the (F-b) saturated-set avoidance),
and interior distance-2 distinctness.  `strongMajority_of_glue` then
dispatches EVERY row of an admissible graph through the four closed row
lemmas (`l1_row_le` / `twoChain_row_le` / `chainEnd_row_le` /
`interior_row_le`) with no case left:

  d(u), d(v) ≠ 2        → case (b)  `l1_row_le`     (junction–junction,
                          pendant, K₂; pure-junction rows)
  d(u) = 2 xor d(v) = 2 → case (c)/(d) `twoChain_row_le`/`chainEnd_row_le`
                          via the chain-end disjunction (covers l = 2
                          chains, l ≥ 3 ports, loop chains)
  d(u) = d(v) = 2       → case (e)  `interior_row_le` (chain interiors
                          AND pure-cycle rows — case (a) needs no
                          separate treatment at the row level)

`maj_le_six_of_glue` restates the remaining formal distance to
`maj_le_six` exactly: it is now ONLY the existence statement
"every admissible graph admits a glue coloring with 6 colors"
(the (G1)–(G5) construction itself: chain decomposition + M +
`shannon_six_of_maxDegree_four` + transport + `isFill_exists`).

Machine pretest BEFORE proving (`lenses/C5L3-lean-six/pretest_glue.py`
P1, exit 0): the bundle ⇒ strong-majority implication verified by the
lab's mutation-tested checker on 24,464 constructed (G1)–(G5) colorings
over the EXHAUSTIVE 23,440 labeled connected admissible graphs n ≤ 6
(+ 400 random n = 7 + corpus incl. fat triangle, subdivided K₄/K₆,
loop chains, theta graphs, pure cycles, disjoint unions), plus 34,744
row-breaking mutants (the bundle failed in every single one — zero
soundness breaks) and 241 fully random bundle-satisfying colorings.
The same run validated interface COMPLETENESS: every constructed
(G1)–(G5) coloring satisfies the bundle verbatim.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Arith
import SMaj.Six.Arith
import SMaj.Six.Rows
import SMaj.Six.Targets

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-! ### Row symmetry -/

lemma row_comm (u v : V) : row G u v = row G v u :=
  union_comm _ _

lemma nColor_comm (c : Sym2 V → C) (u v : V) (α : C) :
    nColor G c u v α = nColor G c v u α := by
  unfold nColor
  rw [row_comm]

/-! ### Degree-2 vertices have exactly one other neighbor -/

/-- A degree-2 vertex `w` adjacent to `v` has a neighbor `y ≠ v`. -/
lemma exists_other_neighbor {w v : V} (hwv : G.Adj w v)
    (hdw : G.degree w = 2) :
    ∃ y : V, G.Adj w y ∧ y ≠ v := by
  have hv : v ∈ G.neighborFinset w := by rwa [mem_neighborFinset]
  have hcard : #((G.neighborFinset w).erase v) = 1 := by
    have h2 : #(G.neighborFinset w) = 2 := by
      rw [card_neighborFinset_eq_degree, hdw]
    rw [card_erase_of_mem hv, h2]
  obtain ⟨y, hy⟩ :=
    card_pos.mp (by omega : 0 < #((G.neighborFinset w).erase v))
  rw [mem_erase, mem_neighborFinset] at hy
  exact ⟨y, hy.2, hy.1⟩

/-! ### The glue interface -/

variable (G) in
/-- **The glue postcondition bundle**: the ROW-LEVEL postconditions of the
(G1)–(G5) construction — the part of what it guarantees that the row case
analysis consumes — stated without any reference to the construction (no
chains, no M, no fill — only the coloring and the grouping; the
construction also guarantees more, e.g. group sizes ≤ 4, which the rows
never use).  NOTE: this bundle is NOT a standalone strong-majority
certificate — `strongMajority_of_glue` additionally requires
`Admissible G` (on the inadmissible path P₃, coloring both edges alike
with singleton groups satisfies every field while the leaf row has
cap 0).  Fields:
* `rainbow` — `c` is rainbow on `ix` at every vertex ((G1) + properness of
  the M-coloring at group nodes; at degree-≤ 2 vertices the construction
  uses singleton groups, making this free there);
* `junction_groups` — at junctions the grouping uses ≤ ⌈d/4⌉ groups (G1);
* `chain_end` — at every path x–w–y with w internal (d(w) = 2) and x a
  junction: either the two chain edges at w carry one color (l = 2 chains,
  (G3)) or the inward color avoids the saturated set of the port ((G4) +
  fill condition (F-b));
* `interior` — rows with both endpoint degrees 2 (chain interiors and pure
  cycles) see distinct colors on their two sides ((F-a) distance-2
  distinctness / l = 3 port distinctness / `cycle_distance2`). -/
structure IsGlueColoring [Fintype C] (ix : V → Sym2 V → ℕ)
    (c : Sym2 V → C) : Prop where
  rainbow : IsRainbow G ix c
  junction_groups : ∀ v : V, 3 ≤ G.degree v →
    groups G ix v ≤ hfun 4 (G.degree v)
  chain_end : ∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
    G.degree w = 2 → 3 ≤ G.degree x →
    c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w
  interior : ∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
    ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g

/-! ### The dispatch theorem: the full §4 row case analysis -/

/-- **Row dispatch** (L2 §4, cases (a)–(e), CLOSED): on an admissible
graph, every glue coloring is strong majority.  This is the entire row
case analysis of the ≤ 6 theorem; together with `maj_le_six_of_glue` it
reduces `maj_le_six` to the existence of a glue coloring. -/
theorem strongMajority_of_glue [Fintype C] {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → C} (hadm : Admissible G) (h : IsGlueColoring G ix c) :
    IsStrongMajority G c := by
  -- group bound at every vertex of degree ≠ 2 (degree ≤ 1 carries no
  -- groups by the `groups` convention)
  have hgb : ∀ z : V, G.degree z ≠ 2 →
      groups G ix z ≤ hfun 4 (G.degree z) := by
    intro z hz
    rcases Nat.lt_or_ge (G.degree z) 2 with hlt | hge
    · rw [groups, if_pos (by omega)]
      exact Nat.zero_le _
    · exact h.junction_groups z (by omega)
  -- cases (c)/(d): the row of a port edge x–w (x junction, w internal),
  -- dispatched through the chain-end disjunction
  have hend : ∀ x w : V, G.Adj x w → G.degree w = 2 → G.degree x ≠ 2 →
      ∀ α : C, nColor G c x w α ≤ (G.degree x + G.degree w - 2) / 2 := by
    intro x w hxw hdw hdx α
    have hdx3 : 3 ≤ G.degree x := by
      have h1 : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨w, hxw⟩
      have h3 := hadm x w hxw
      omega
    obtain ⟨y, hwy, hyx⟩ := exists_other_neighbor hxw.symm hdw
    have hxy : x ≠ y := fun he => hyx (he ▸ rfl)
    have hg : groups G ix x ≤ G.degree x / 2 :=
      le_trans (h.junction_groups x hdx3) (g_R3 hdx3)
    rcases h.chain_end x w y hxw hwy hxy hdw hdx3 with hcc | hFb
    · exact twoChain_row_le h.rainbow hxw hwy hxy hdw (by omega) hcc hg α
    · exact chainEnd_row_le h.rainbow hxw hwy hxy hdw hg hFb α
  intro u v huv α
  by_cases hdu : G.degree u = 2 <;> by_cases hdv : G.degree v = 2
  · -- case (e) (+ pure cycles, case (a)): both endpoints internal
    exact interior_row_le huv hdu hdv (h.interior u v huv hdu hdv) α
  · -- u internal, v the junction end: flip the row and dispatch
    have h1 := hend v u huv.symm hdu hdv α
    rw [nColor_comm c u v α]
    omega
  · -- v internal, u the junction end
    exact hend u v huv hdv hdu α
  · -- case (b): no internal endpoint (junction–junction, pendant, K₂)
    exact l1_row_le h.rainbow huv hdu hdv (hgb u hdu) (hgb v hdv) α

/-- **The remaining formal distance to `maj_le_six`, restated exactly**:
if every admissible graph admits a glue coloring with palette `Fin 6`
(= the (G1)–(G5) construction: chain decomposition, contraction
multigraph M, `shannon_six_of_maxDegree_four`, port transport,
`isFill_exists`), then `maj_le_six` holds for it.  The row case
analysis no longer stands between the library and the headline. -/
theorem maj_le_six_of_glue (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G)
    (hglue : ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 6),
      IsGlueColoring G ix c) :
    ∃ c : Sym2 V → Fin 6, IsStrongMajority G c := by
  obtain ⟨ix, c, hg⟩ := hglue
  exact ⟨c, strongMajority_of_glue hadm hg⟩

end SMaj
