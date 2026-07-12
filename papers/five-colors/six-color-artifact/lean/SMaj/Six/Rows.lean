/-
SMaj/Six/Rows.lean — the row case analysis of the T1 ≤ 6 theorem
(`lenses/L2-chain-grouping/WRITEUP.md` §4), formalized per case at the
graph level.  Everything here is CLOSED (no sorry, no proof_wanted):

* `side_count_lt_own` — the own-color half of L2 Lemma 1 (Counting Lemma):
  on a rainbow grouping, the edge's own color appears at most g(u) − 1
  times on its u-side.  (The ≤ g(u) half is `side_count_le` of
  `SMaj/Counting.lean`; this strict half was missing from the bridgehead.)
* `side_eq_singleton_of_degree_two` — at a degree-2 vertex the side away
  from one neighbor is exactly the other incident edge.
* `twoChain_row_le` — **the l = 2 same-color row lemma** (case (c), the
  heart of the ≤ 6 proof): if both edges of a length-2 chain carry one
  color and the junction grouping is rainbow with g ≤ ⌊d/2⌋, the chain-end
  row is strong-majority — no cross-constraint at any degree.
* `satSet`, `card_satSet_le_two`, `satSet_eq_empty_of_ne` — L2 Lemma 3
  (saturated sets are small): |F_x| ≤ 2 ALWAYS (the writeup proved it for
  d ∈ {3,5}; the same pigeonhole works for every d ≥ 2 — pretested,
  `pretest_claims.py` P2), and F_x = ∅ off degrees {3,5} (via R4).
* `chainEnd_row_le` — case (d): chain-end rows of l ≥ 3 chains, given the
  (F-b) condition that the inward neighbor avoids the saturated set.
* `interior_row_le` — case (e): interior rows under distance-2
  distinctness (F-a).

Case (b) (l = 1 chains: junction–junction and pendant rows) is the
pointwise Counting-Lemma bound plus `crit4_of_ne_two`; it is packaged in
`SMaj/Six/Targets.lean` as `l1_row_le`.

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Six.Arith

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-! ### The own-color refinement of the Counting Lemma -/

/-- Own-color side bound (L2 Lemma 1, second half): if `c` is rainbow on
the grouping `ix` and `d(u) ≥ 2`, then the color of the edge `s(u,v)`
itself appears STRICTLY fewer than `g(u)` times on the `u`-side of its row:
the edge's own group cannot contribute (its other members differ from
`s(u,v)` in color by rainbowness), and there are only `g(u)` groups. -/
lemma side_count_lt_own {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {u v : V} (huv : G.Adj u v)
    (hd : 2 ≤ G.degree u) :
    #{f ∈ side G u v | c f = c s(u, v)} < groups G ix u := by
  have he : s(u, v) ∈ G.incidenceFinset u := by
    rw [mem_incidenceFinset]
    exact G.mk'_mem_incidenceSet_left_iff.mpr huv
  have hgroups : groups G ix u = #((G.incidenceFinset u).image (ix u)) := by
    rw [groups, if_neg (by omega)]
  rw [hgroups]
  -- inject the own-color side into the group image minus the edge's group
  calc #{f ∈ side G u v | c f = c s(u, v)}
      ≤ #(((G.incidenceFinset u).image (ix u)).erase (ix u s(u, v))) := by
        apply card_le_card_of_injOn (ix u)
        · intro f hf
          rw [mem_coe, mem_filter, mem_side] at hf
          rw [mem_coe, mem_erase]
          refine ⟨fun heq => hf.1.1 ?_,
            mem_image_of_mem _ (mem_incFinset.mpr hf.1.2)⟩
          -- same group as s(u,v) + same color ⇒ equal to s(u,v)
          exact hrb u f (mem_incFinset.mpr hf.1.2) s(u, v) he heq hf.2
        · intro f₁ h₁ f₂ h₂ hix
          rw [mem_coe, mem_filter, mem_side] at h₁ h₂
          exact hrb u f₁ (mem_incFinset.mpr h₁.1.2) f₂
            (mem_incFinset.mpr h₂.1.2) hix (h₁.2.trans h₂.2.symm)
    _ < #((G.incidenceFinset u).image (ix u)) :=
        card_erase_lt_of_mem (mem_image_of_mem _ he)

/-! ### Degree-2 sides -/

/-- At a degree-2 vertex `w` with distinct neighbors `x ≠ y`, the side of
the row of `s(w,x)` at `w` is exactly the other incident edge `s(w,y)`. -/
lemma side_eq_singleton_of_degree_two {x w y : V}
    (hwx : G.Adj w x) (hwy : G.Adj w y) (hxy : x ≠ y)
    (hdw : G.degree w = 2) :
    side G w x = {s(w, y)} := by
  have hx : s(w, x) ∈ G.incidenceFinset w := by
    rw [mem_incidenceFinset]; exact G.mk'_mem_incidenceSet_left_iff.mpr hwx
  have hy : s(w, y) ∈ G.incidenceFinset w := by
    rw [mem_incidenceFinset]; exact G.mk'_mem_incidenceSet_left_iff.mpr hwy
  have hne : s(w, x) ≠ s(w, y) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hxy h2
    · exact hwy.ne h1
  have hpair : ({s(w, x), s(w, y)} : Finset (Sym2 V)) = G.incidenceFinset w := by
    apply eq_of_subset_of_card_le
    · intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact hx
      · rwa [mem_singleton.mp hf]
    · rw [card_incidenceFinset_eq_degree, hdw, card_pair hne]
  have hside : side G w x = ({s(w, x), s(w, y)} : Finset (Sym2 V)).erase s(w, x) := by
    rw [side, hpair]
  rw [hside, erase_insert (by simpa using hne)]

omit [Fintype V] [DecidableEq V] in
/-- The α-count of a singleton side is at most 1. -/
lemma count_singleton_le {f : Sym2 V} {c : Sym2 V → C} (α : C) :
    #{g ∈ ({f} : Finset (Sym2 V)) | c g = α} ≤ 1 := by
  simpa using card_filter_le ({f} : Finset (Sym2 V)) _

omit [Fintype V] [DecidableEq V] in
/-- The α-count of a singleton side is 0 when its edge has another color. -/
lemma count_singleton_eq_zero {f : Sym2 V} {c : Sym2 V → C} {α : C}
    (h : c f ≠ α) :
    #{g ∈ ({f} : Finset (Sym2 V)) | c g = α} = 0 := by
  simp [filter_singleton, h]

/-- The row α-count splits across the two sides (subadditively). -/
lemma nColor_le_sides {c : Sym2 V → C} (u v : V) (α : C) :
    nColor G c u v α ≤
      #{f ∈ side G u v | c f = α} + #{f ∈ side G v u | c f = α} := by
  unfold nColor row
  rw [filter_union]
  exact card_union_le _ _

/-! ### Case (c): the l = 2 same-color row lemma — the heart of ≤ 6 -/

/-- **The l = 2 same-color row lemma** (L2 §4 case (c)): let `x w y` be a
length-2 chain (`d(w) = 2`, `x ≠ y`) whose two edges carry the SAME color,
and let the coloring be rainbow on a grouping at the junction `x` with
`g(x) ≤ ⌊d(x)/2⌋` (R3 supplies this for g = ⌈d/4⌉ at every d ≥ 3).  Then
the row of the chain edge `s(x,w)` is strong-majority at every color: the
chain mate's +1 lands on the port's own color, which the rainbow grouping
keeps one below the group count.  No cross-chain constraint is needed. -/
theorem twoChain_row_le {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {x w y : V}
    (hxw : G.Adj x w) (hwy : G.Adj w y) (hxy : x ≠ y)
    (hdw : G.degree w = 2) (hdx : 2 ≤ G.degree x)
    (hcc : c s(x, w) = c s(w, y))
    (hg : groups G ix x ≤ G.degree x / 2) (α : C) :
    nColor G c x w α ≤ (G.degree x + G.degree w - 2) / 2 := by
  have hcap : (G.degree x + G.degree w - 2) / 2 = G.degree x / 2 := by
    rw [hdw]; omega
  have hside : side G w x = {s(w, y)} :=
    side_eq_singleton_of_degree_two hxw.symm hwy hxy hdw
  have hsplit := nColor_le_sides (G := G) (c := c) x w α
  rw [hcap]
  by_cases hα : α = c s(x, w)
  · -- own color: x-side < g(x), w-side ≤ 1
    have h1 : #{f ∈ side G x w | c f = α} < groups G ix x := by
      rw [hα]; exact side_count_lt_own hrb hxw hdx
    have h2 : #{f ∈ side G w x | c f = α} ≤ 1 := by
      rw [hside]; exact count_singleton_le α
    omega
  · -- other colors: x-side ≤ g(x), w-side = 0 (the mate carries the
    -- port's own color ≠ α)
    have h1 := side_count_le hrb hxw α
    have h2 : #{f ∈ side G w x | c f = α} = 0 := by
      rw [hside]
      exact count_singleton_eq_zero (by rw [← hcc]; exact fun h => hα h.symm)
    omega

/-! ### Lemma 3: saturated sets are small -/

variable (G) in
/-- The saturated set F_x of a chain end `s(x,w)` (L2 (G4)): colors hitting
the `x`-side of the row at least ⌊d(x)/2⌋ times (i.e. meeting the chain-end
row cap before the inward chain edge is counted). -/
def satSet [Fintype C] (c : Sym2 V → C) (x w : V) : Finset C :=
  Finset.univ.filter fun α => G.degree x / 2 ≤ #{f ∈ side G x w | c f = α}

lemma mem_satSet_iff [Fintype C] {c : Sym2 V → C} {x w : V} {α : C} :
    α ∈ satSet G c x w ↔ G.degree x / 2 ≤ #{f ∈ side G x w | c f = α} := by
  simp [satSet]

/-- Color-threshold pigeonhole: at threshold t, the number of colors with
≥ t hits in a finite edge set s, times t, is at most |s|. -/
lemma card_threshold_mul_le [Fintype C] {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → C) (t : ℕ) :
    #(Finset.univ.filter fun α : C => t ≤ #{x ∈ s | f x = α}) * t ≤ #s := by
  set F := Finset.univ.filter fun α : C => t ≤ #{x ∈ s | f x = α} with hF
  have hsum : ∑ α ∈ F, #{x ∈ s | f x = α} ≤ #s := by
    rw [card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun x _ => mem_univ (f x))]
    exact sum_le_sum_of_subset (subset_univ _)
  have h1 : #F • t ≤ ∑ α ∈ F, #{x ∈ s | f x = α} := by
    apply Finset.card_nsmul_le_sum
    intro α hα
    rw [hF, mem_filter] at hα
    exact hα.2
  rw [smul_eq_mul] at h1
  exact h1.trans hsum

/-- **L2 Lemma 3, size bound — strengthened**: |F_x| ≤ 2 for EVERY junction
degree ≥ 2 (the writeup needed only d ∈ {3,5}; the pigeonhole
3·⌊d/2⌋ > d − 1 holds for all d ≥ 2 — pretest P2). -/
theorem card_satSet_le_two [Fintype C] {c : Sym2 V → C} {x w : V}
    (hxw : G.Adj x w) (hd : 2 ≤ G.degree x) :
    #(satSet G c x w) ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ #(satSet G c x w) := by omega
  have hfinal : 3 * (G.degree x / 2) ≤ G.degree x - 1 := by
    calc 3 * (G.degree x / 2)
        ≤ #(satSet G c x w) * (G.degree x / 2) :=
          Nat.mul_le_mul_right _ h3
      _ ≤ #(side G x w) := card_threshold_mul_le (side G x w) c _
      _ = G.degree x - 1 := card_side hxw
  omega

/-- **L2 Lemma 3, emptiness off {3,5}**: on a rainbow grouping with
g(x) ≤ ⌈d(x)/4⌉ and d(x) ∉ {3,5} (d ≥ 3), no color saturates: F_x = ∅.
(R4: ⌈d/4⌉ + 1 ≤ ⌊d/2⌋ there.) -/
theorem satSet_eq_empty_of_ne [Fintype C] {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → C} (hrb : IsRainbow G ix c) {x w : V} (hxw : G.Adj x w)
    (hd : 3 ≤ G.degree x) (h3 : G.degree x ≠ 3) (h5 : G.degree x ≠ 5)
    (hg : groups G ix x ≤ hfun 4 (G.degree x)) :
    satSet G c x w = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro α hα
  rw [mem_satSet_iff] at hα
  have h1 := side_count_le hrb hxw α
  have h2 := g_R4 hd h3 h5
  omega

/-! ### Case (d): chain-end rows of l ≥ 3 chains -/

/-- Chain-end rows of l ≥ 3 chains (L2 §4 case (d)): `x w y` with `w` the
first internal vertex of the chain (`d(w) = 2`, `x ≠ y`), the coloring
rainbow at the junction `x` with `g(x) ≤ ⌊d(x)/2⌋`, and the (F-b) fill
condition: the inward edge `s(w,y)`'s color avoids the saturated set.
Then the row of the port `s(x,w)` is strong-majority at every color:
unsaturated colors sit ≤ cap − 1 on the x-side and gain ≤ 1 from the
inward edge; saturated colors sit ≤ g(x) ≤ cap and gain 0. -/
theorem chainEnd_row_le [Fintype C] {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {x w y : V}
    (hxw : G.Adj x w) (hwy : G.Adj w y) (hxy : x ≠ y)
    (hdw : G.degree w = 2)
    (hg : groups G ix x ≤ G.degree x / 2)
    (hFb : c s(w, y) ∉ satSet G c x w) (α : C) :
    nColor G c x w α ≤ (G.degree x + G.degree w - 2) / 2 := by
  have hcap : (G.degree x + G.degree w - 2) / 2 = G.degree x / 2 := by
    rw [hdw]; omega
  have hside : side G w x = {s(w, y)} :=
    side_eq_singleton_of_degree_two hxw.symm hwy hxy hdw
  have hsplit := nColor_le_sides (G := G) (c := c) x w α
  rw [hcap]
  by_cases hα : α ∈ satSet G c x w
  · -- saturated color: the inward edge cannot carry it ((F-b)),
    -- and the x-side is ≤ g(x) ≤ cap
    have h1 := side_count_le hrb hxw α
    have h2 : #{f ∈ side G w x | c f = α} = 0 := by
      rw [hside]
      exact count_singleton_eq_zero (fun h => hFb (h ▸ hα))
    omega
  · -- unsaturated color: x-side < cap by definition of satSet
    have h1 : #{f ∈ side G x w | c f = α} < G.degree x / 2 := by
      by_contra h
      exact hα (mem_satSet_iff.mpr (by omega))
    have h2 : #{f ∈ side G w x | c f = α} ≤ 1 := by
      rw [hside]; exact count_singleton_le α
    omega

/-! ### Case (e): interior rows -/

/-- Interior chain rows (L2 §4 case (e)): an edge both of whose endpoints
have degree 2, whose two adjacent edges carry distinct colors — guaranteed
by (F-a) distance-2 distinctness, or for l = 3 by port distinctness — is
strong-majority: the cap is 1 and every color hits at most once. -/
theorem interior_row_le {c : Sym2 V → C} {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2)
    (hdiff : ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g) (α : C) :
    nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2 := by
  have hcap : (G.degree u + G.degree v - 2) / 2 = 1 := by
    rw [hdu, hdv]
  have hu : #{f ∈ side G u v | c f = α} ≤ 1 := by
    calc #{f ∈ side G u v | c f = α} ≤ #(side G u v) := card_filter_le _ _
      _ = 1 := by rw [card_side huv, hdu]
  have hv : #{f ∈ side G v u | c f = α} ≤ 1 := by
    calc #{f ∈ side G v u | c f = α} ≤ #(side G v u) := card_filter_le _ _
      _ = 1 := by rw [card_side huv.symm, hdv]
  have hnotboth : ¬(1 ≤ #{f ∈ side G u v | c f = α} ∧
      1 ≤ #{f ∈ side G v u | c f = α}) := by
    rintro ⟨h1, h2⟩
    obtain ⟨f, hf⟩ := card_pos.mp (by omega : 0 < #{f ∈ side G u v | c f = α})
    obtain ⟨g, hg⟩ := card_pos.mp (by omega : 0 < #{f ∈ side G v u | c f = α})
    rw [mem_filter] at hf hg
    exact hdiff f hf.1 g hg.1 (hf.2.trans hg.2.symm)
  have hsplit := nColor_le_sides (G := G) (c := c) u v α
  omega

end SMaj
