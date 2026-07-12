/-
# Strong-majority edge colorings: Maj'(G) <= 6 for admissible graphs -
# THE COMPLETE KERNEL DEVELOPMENT, concatenated single-file form
# (source: problems/p5-strongmajority/lenses/L5-hedges-lean/lean/SMaj/*,
# 16-file dependency cone of `maj_le_six`, concatenated in topological
# order with each source file wrapped in its own `section` to preserve
# variable scoping; zero declarations renamed, zero statements changed.)
#
# The headline theorem (bottom of this file):
#   theorem maj_le_six (G : SimpleGraph V) [DecidableRel G.Adj]
#       (hadm : Admissible G) :
#       ∃ c : Sym2 V → Fin 6, IsStrongMajority G c
# This improves the published Maj' <= 8 (arXiv:2605.23828 Thm 12).
# The literature states Maj' <= 5 is TRUE on paper (Alon-Przybylo-Solomon,
# arXiv:2607.00212). See PROMPT.txt: the task is maj_le_five.
-/
import Mathlib

set_option maxHeartbeats 1600000


/-- Pin-compatibility shim (this development was authored at mathlib
v4.30, where this lemma exists; at this pin it is the `.symm` of
`support_eq_cons`; statement byte-identical to the newer mathlib). -/
@[simp]
lemma SimpleGraph.Walk.cons_tail_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : u :: p.support.tail = p.support :=
  (p.support_eq_cons).symm

namespace SMaj

/-! ###### source file: SMaj/Defs.lean ###### -/
section
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

end

/-! ###### source file: SMaj/Counting.lean ###### -/
section
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

end

/-! ###### source file: SMaj/Six/Fill.lean ###### -/
section
/-
SMaj/Six/Fill.lean — the interior fill lemma of the T1 ≤ 6 proof
(`lenses/L2-chain-grouping/WRITEUP.md` Lemma 4), proved for ALL chain
lengths l ≥ 3 — strictly stronger than the L2 battery `battery_fill`
(exhaustive l = 3..10, 136,488 instances) in two ways:
* unbounded l (the writeup's greedy left-to-right choice, packaged as a
  recursion on l); and
* 5 colors suffice (the writeup used |C| = 6; the forbidden-set count in
  the greedy argument is ≤ 4, so any palette of size ≥ 5 works —
  machine-pretested exhaustively for |C| ∈ {5,6}, l ≤ 8, all ports and
  F-sets: `lenses/C3L4-lean-six/pretest_claims.py` P1, 138,760/138,760,
  including the recursive proof shape used here).

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.
-/


open Finset

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A palette of size ≥ 5 always has a color avoiding ≤ 4 forbidden ones. -/
lemma exists_avoid (hC : 5 ≤ Fintype.card C) {s : Finset C} (hs : #s ≤ 4) :
    ∃ x : C, x ∉ s := by
  have h : (sᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]; omega
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Finset.mem_compl.mp hx⟩

/-- `c` is an interior fill for a chain of `l` edges with port colors `p, q`
and end saturated sets `Fx, Fy` (L2 (G5)): ports pinned, distance-2
distinctness (F-a), and the second and penultimate positions avoiding the
saturated sets (F-b).  Only the values `c 0 .. c (l-1)` are constrained. -/
def IsFill (l : ℕ) (p q : C) (Fx Fy : Finset C) (c : ℕ → C) : Prop :=
  c 0 = p ∧ c (l - 1) = q ∧
  (∀ i, i + 2 ≤ l - 1 → c i ≠ c (i + 2)) ∧
  c 1 ∉ Fx ∧ c (l - 2) ∉ Fy

/-- Fill existence for l ≥ 4 (no port-distinctness needed), by induction on
l: the base l = 4 picks the two interior colors directly; the step picks
c₁ ∉ Fx and recurses on the length-(l−1) tail with left port c₁ and left
saturated set {p} (the writeup's greedy order, packaged as a recursion —
pretested shape, `pretest_claims.py` P1-recursive). -/
theorem isFill_exists_of_four_le (hC : 5 ≤ Fintype.card C) :
    ∀ l, 4 ≤ l → ∀ (p q : C) (Fx Fy : Finset C), #Fx ≤ 2 → #Fy ≤ 2 →
      ∃ c : ℕ → C, IsFill l p q Fx Fy c := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    intro p q Fx Fy hFx hFy
    -- l = 4: choose c₁ ∉ Fx ∪ {q} and c₂ ∉ Fy ∪ {p} independently.
    obtain ⟨c₁, hc₁⟩ := exists_avoid hC (s := Fx ∪ {q})
      (le_trans (Finset.card_union_le _ _) (by simp; omega))
    obtain ⟨c₂, hc₂⟩ := exists_avoid hC (s := Fy ∪ {p})
      (le_trans (Finset.card_union_le _ _) (by simp; omega))
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hc₁ hc₂
    refine ⟨fun i => if i = 0 then p else if i = 1 then c₁
      else if i = 2 then c₂ else q, rfl, rfl, ?_, by simpa using hc₁.1,
      by simpa using hc₂.1⟩
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · show p ≠ c₂
      exact fun h => hc₂.2 h.symm
    · show c₁ ≠ q
      exact hc₁.2
  | succ l hl ih =>
    intro p q Fx Fy hFx hFy
    -- choose the color next to the x-port, then fill the tail of length l.
    obtain ⟨c₁, hc₁⟩ := exists_avoid hC (le_trans hFx (by omega))
    obtain ⟨c', h0, hlast, hgap, h1, hpen⟩ :=
      ih c₁ q {p} Fy (by simp) hFy
    refine ⟨fun i => if i = 0 then p else c' (i - 1), by simp, ?_, ?_, ?_, ?_⟩
    · -- right port: position (l+1)−1 = l ≥ 4 ≠ 0
      show (if l + 1 - 1 = 0 then p else c' (l + 1 - 1 - 1)) = q
      rw [if_neg (by omega), show l + 1 - 1 - 1 = l - 1 by omega]
      exact hlast
    · -- distance-2 distinctness
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · -- pair (0,2): c 2 = c' 1 ≠ p since c' 1 ∉ {p}
        show (if (0:ℕ) = 0 then p else c' (0 - 1)) ≠
          (if (0:ℕ) + 2 = 0 then p else c' (0 + 2 - 1))
        rw [if_pos rfl, if_neg (by omega)]
        have h1' : c' (0 + 2 - 1) ≠ p := by simpa using h1
        exact fun h => h1' h.symm
      · show (if i = 0 then p else c' (i - 1)) ≠
          (if i + 2 = 0 then p else c' (i + 2 - 1))
        rw [if_neg (by omega), if_neg (by omega)]
        have := hgap (i - 1) (by omega)
        rwa [show i - 1 + 2 = i + 2 - 1 by omega] at this
    · -- c 1 = c' 0 = c₁ ∉ Fx
      show (if (1:ℕ) = 0 then p else c' (1 - 1)) ∉ Fx
      rw [if_neg (by omega), show (1:ℕ) - 1 = 0 from rfl, h0]
      exact hc₁
    · -- penultimate: c (l+1−2) = c' (l−2) ∉ Fy
      show (if l + 1 - 2 = 0 then p else c' (l + 1 - 2 - 1)) ∉ Fy
      rw [if_neg (by omega), show l + 1 - 2 - 1 = l - 2 by omega]
      exact hpen

/-- **The fill lemma** (L2 Lemma 4, all lengths, palette ≥ 5): for every
chain length l ≥ 3, port colors p, q with p ≠ q when l = 3, and saturated
sets of size ≤ 2, an interior fill exists.  With `C = Fin 6` this is
exactly the (G5) step of the ≤ 6 construction. -/
theorem isFill_exists (hC : 5 ≤ Fintype.card C)
    {l : ℕ} (hl : 3 ≤ l) (p q : C) (hpq : l = 3 → p ≠ q)
    {Fx Fy : Finset C} (hFx : #Fx ≤ 2) (hFy : #Fy ≤ 2) :
    ∃ c : ℕ → C, IsFill l p q Fx Fy c := by
  rcases eq_or_lt_of_le hl with rfl | hl4
  · -- l = 3: a single interior color avoiding Fx ∪ Fy; (F-a) is p ≠ q.
    obtain ⟨c₁, hc₁⟩ := exists_avoid hC (s := Fx ∪ Fy)
      (le_trans (Finset.card_union_le _ _) (by omega))
    simp only [Finset.mem_union, not_or] at hc₁
    refine ⟨fun i => if i = 0 then p else if i = 1 then c₁ else q,
      rfl, rfl, ?_, by simpa using hc₁.1, by simpa using hc₁.2⟩
    intro i hi
    have hi' : i = 0 := by omega
    subst hi'
    show p ≠ q
    exact hpq rfl
  · exact isFill_exists_of_four_le hC l hl4 p q Fx Fy hFx hFy

end

/-! ###### source file: SMaj/Arith.lean ###### -/
section
/-
SMaj/Arith.lean — the arithmetic layer of the Master Theorem
(`lenses/technique-transfer/THEOREMS.md` §3): the group-count function h_s,
the criterion CRIT_s, the crossover lemmas, the exact bad-pair tables for
s = 3, 4, 5, and the saturation theorem (the bad set is {(1,2),(2,2),(2,3)}
for EVERY s ≥ 5).

This is the Lean counterpart of `test_master.py::arith_checks` (machine-pinned
bad sets, re-checked to 400 there; here proved for ALL degrees via the
crossover lemmas — strictly stronger than the Python battery).
-/


/-- h_s(d): the number of groups used at a vertex of degree `d` when incident
edges are split into groups of size ≤ s as evenly as possible: 0 for d ≤ 1,
else ⌈d/s⌉ (here in the Nat form (d + s − 1)/s). -/
def hfun (s d : ℕ) : ℕ := if d ≤ 1 then 0 else (d + s - 1) / s

/-- CRIT_s at a degree pair (a, b) (THEOREMS.md §3): the grouping bound
h_s(a) + h_s(b) fits under the strong-majority cap ⌊(a + b − 2)/2⌋. -/
def Crit (s a b : ℕ) : Prop := hfun s a + hfun s b ≤ (a + b - 2) / 2

instance (s a b : ℕ) : Decidable (Crit s a b) :=
  inferInstanceAs (Decidable (_ ≤ _))

lemma hfun_eq_ceilDiv {s d : ℕ} (hd : 2 ≤ d) : hfun s d = d ⌈/⌉ s := by
  rw [hfun, if_neg (by omega), Nat.ceilDiv_eq_add_pred_div]

/-- h is antitone in the group size s (more room per group, fewer groups). -/
lemma hfun_anti {s s' : ℕ} (h1 : 0 < s') (h : s' ≤ s) (d : ℕ) :
    hfun s d ≤ hfun s' d := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · rw [hfun, if_pos (by omega)]; exact Nat.zero_le _
  · rw [hfun_eq_ceilDiv hd, hfun_eq_ceilDiv hd]
    have h0 : 0 < s := h1.trans_le h
    rw [ceilDiv_le_iff_le_mul h0]
    calc d ≤ s' * (d ⌈/⌉ s') := by
            simpa [smul_eq_mul] using le_smul_ceilDiv (α := ℕ) (β := ℕ) h1
      _ ≤ s * (d ⌈/⌉ s') := Nat.mul_le_mul_right _ h

/-- CRIT is inherited upward in s (saturation direction). -/
lemma crit_of_crit_le {s s' a b : ℕ} (h1 : 0 < s') (h : s' ≤ s)
    (hc : Crit s' a b) : Crit s a b :=
  le_trans (Nat.add_le_add (hfun_anti h1 h a) (hfun_anti h1 h b)) hc

/-! ### Crossover lemmas (the infinite part of the bad-set computation) -/

lemma crit3_of_large {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : 17 ≤ a + b) :
    Crit 3 a b := by
  unfold Crit hfun; split_ifs <;> omega

lemma crit4_of_large {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : 12 ≤ a + b) :
    Crit 4 a b := by
  unfold Crit hfun; split_ifs <;> omega

lemma crit5_of_large {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : 11 ≤ a + b) :
    Crit 5 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-! ### Exact bad-pair tables (finite part, by kernel computation) -/

/-- The s = 3 bad set below the crossover, exactly (THEOREMS.md §3 table). -/
lemma bad3_table :
    ∀ a ∈ Finset.Icc 1 16, ∀ b ∈ Finset.Icc a 16,
      (¬ Crit 3 a b ↔ (a, b) ∈ ([(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(2,7),
        (3,4),(4,4),(4,5),(4,7)] : List (ℕ × ℕ))) := by decide

/-- The s = 4 bad set below the crossover, exactly. -/
lemma bad4_table :
    ∀ a ∈ Finset.Icc 1 11, ∀ b ∈ Finset.Icc a 11,
      (¬ Crit 4 a b ↔ (a, b) ∈ ([(1,2),(2,2),(2,3),(2,5)] : List (ℕ × ℕ))) := by
  decide

/-- The s = 5 bad set below the crossover, exactly. -/
lemma bad5_table :
    ∀ a ∈ Finset.Icc 1 10, ∀ b ∈ Finset.Icc a 10,
      (¬ Crit 5 a b ↔ (a, b) ∈ ([(1,2),(2,2),(2,3)] : List (ℕ × ℕ))) := by
  decide

/-! ### Unbounded characterizations -/

/-- Corollary-A arithmetic: every degree pair avoiding 2 and 4 satisfies
CRIT_3.  (Equivalently: every bad pair for s = 3 contains a 2 or a 4.) -/
theorem crit3_of_no24 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha2 : a ≠ 2) (ha4 : a ≠ 4) (hb2 : b ≠ 2) (hb4 : b ≠ 4) : Crit 3 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-- Corollary-B arithmetic: every degree pair with no 2, or with 2 only
against 4 / ≥ 6, satisfies CRIT_4. -/
theorem crit4_of_scope {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a = 2 → b = 4 ∨ 6 ≤ b) (hba : b = 2 → a = 4 ∨ 6 ≤ a) :
    Crit 4 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-- Corollary-C arithmetic: every degree pair with no 2 against a degree ≤ 3
satisfies CRIT_5. -/
theorem crit5_of_scope {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a = 2 → 4 ≤ b) (hba : b = 2 → 4 ≤ a) : Crit 5 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-! ### Pointwise h values at the small degrees that drive the residue -/

lemma hfun_zero (s : ℕ) : hfun s 0 = 0 := by rw [hfun, if_pos (by omega)]

lemma hfun_one (s : ℕ) : hfun s 1 = 0 := by rw [hfun, if_pos (by omega)]

lemma hfun_two {s : ℕ} (hs : 2 ≤ s) : hfun s 2 = 1 := by
  rw [hfun, if_neg (by omega)]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

lemma hfun_three {s : ℕ} (hs : 3 ≤ s) : hfun s 3 = 1 := by
  rw [hfun, if_neg (by omega)]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Saturation kernel: (1,2), (2,2), (2,3) violate CRIT_s for every s ≥ 3
(h_s(2) = h_s(3) = 1 forever, and the caps are 0, 1, 1). -/
lemma not_crit_12 {s : ℕ} (hs : 2 ≤ s) : ¬ Crit s 1 2 := by
  have h1 := hfun_one s; have h2 := hfun_two hs; unfold Crit; omega

lemma not_crit_22 {s : ℕ} (hs : 2 ≤ s) : ¬ Crit s 2 2 := by
  have h2 := hfun_two hs; unfold Crit; omega

lemma not_crit_23 {s : ℕ} (hs : 3 ≤ s) : ¬ Crit s 2 3 := by
  have h2 := hfun_two (by omega : 2 ≤ s); have h3 := hfun_three hs
  unfold Crit; omega

/-- The s = 5 bad set, unbounded form: for a ≤ b (both ≥ 1) the criterion
fails exactly at (1,2), (2,2), (2,3). -/
theorem not_crit5_iff {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ¬ Crit 5 a b ↔ (a, b) ∈ ([(1,2),(2,2),(2,3)] : List (ℕ × ℕ)) := by
  rcases Nat.lt_or_ge (a + b) 11 with h | h
  · exact bad5_table a (Finset.mem_Icc.mpr (by omega)) b
      (Finset.mem_Icc.mpr (by omega))
  · constructor
    · intro hc; exact absurd (crit5_of_large ha (by omega) h) hc
    · intro hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hmem
      omega

/-- **Saturation theorem** (THEOREMS.md §3, last table row — here proved for
ALL s ≥ 5, strictly more than the machine check to 400): for every s ≥ 5 the
bad set of CRIT_s is exactly {(1,2), (2,2), (2,3)} (pairs with a ≤ b).
No choice of s pushes the framework's residue below the (2,2)/(2,3)
short-chain class: 6 colors is the framework's floor on its maximal scope. -/
theorem not_crit_saturated {s a b : ℕ} (hs : 5 ≤ s) (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ¬ Crit s a b ↔ (a, b) ∈ ([(1,2),(2,2),(2,3)] : List (ℕ × ℕ)) := by
  constructor
  · intro hc
    rw [← not_crit5_iff ha hab]
    intro h5
    exact hc (crit_of_crit_le (by omega) hs h5)
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact not_crit_12 (by omega)
    · exact not_crit_22 (by omega)
    · exact not_crit_23 (by omega)

/-- Admissibility is implied by CRIT_s (s ≥ 2): the inadmissible degree pair
{1,2} is bad for every s, so the Master Theorem's hypothesis excludes pendant
paths automatically (THEOREMS.md §3, first step of the proof). -/
theorem crit_admissible {s a b : ℕ} (hs : 2 ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Crit s a b) : a + b ≠ 3 := by
  intro h3
  have h1 := hfun_one s
  have h2 := hfun_two hs
  unfold Crit at h
  -- a + b = 3 with a, b ≥ 1 forces {a,b} = {1,2}; either way h collapses
  rcases (by omega : a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · omega
  · omega

end

/-! ###### source file: SMaj/Six/Arith.lean ###### -/
section
/-
SMaj/Six/Arith.lean — the arithmetic of the T1 ≤ 6 proof
(`lenses/L2-chain-grouping/WRITEUP.md` Lemma 2: rules R1–R4 for the
junction group count g(d) = ⌈d/4⌉), proved for ALL degrees — strictly
stronger than the L2 battery `battery_arith` (enumerated to 400).

L2's g(d) (defined there for junctions, d ≥ 3) is `hfun 4 d` of
`SMaj/Arith.lean` (h_s with s = 4): for d ≥ 2, hfun 4 d = ⌈d/4⌉.
All proofs are kernel-checked integer arithmetic (`omega` after unfolding;
division by the literals 2 and 4 is in omega's fragment).

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.  Machine pretest:
`lenses/C3L4-lean-six/pretest_claims.py` (P3) re-pinned R1–R4 to 2000
before these proofs were written.
-/


/-- R1: two junction group counts fit under the junction–junction row cap:
g(a) + g(b) ≤ ⌊(a+b−2)/2⌋ for all a, b ≥ 3 (L2 Lemma 2, R1). -/
theorem g_R1 {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    hfun 4 a + hfun 4 b ≤ (a + b - 2) / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R1 in `Crit` form: every degree pair with both entries ≥ 3 — and more
generally avoiding degree 2 entirely — satisfies CRIT₄ (the s = 4 bad pairs
(1,2), (2,2), (2,3), (2,5) all contain a 2).  This is the arithmetic behind
L2's case (b) rows including pendant ends. -/
theorem crit4_of_ne_two {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha2 : a ≠ 2) (hb2 : b ≠ 2) : Crit 4 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-- R2: a junction group count fits under a junction–pendant row cap:
g(b) ≤ ⌊(b−1)/2⌋ for b ≥ 3 (L2 Lemma 2, R2). -/
theorem g_R2 {b : ℕ} (hb : 3 ≤ b) : hfun 4 b ≤ (b - 1) / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R3: a junction group count fits under the chain-end row cap:
g(d) ≤ ⌊d/2⌋ for d ≥ 3 (L2 Lemma 2, R3). -/
theorem g_R3 {d : ℕ} (hd : 3 ≤ d) : hfun 4 d ≤ d / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R4, strict part: away from degrees 3 and 5 the group count sits STRICTLY
below the chain-end cap — g(d) + 1 ≤ ⌊d/2⌋ for d ≥ 3, d ∉ {3,5}
(L2 Lemma 2, R4; the source of "F_x = ∅ unless d(x) ∈ {3,5}"). -/
theorem g_R4 {d : ℕ} (hd : 3 ≤ d) (h3 : d ≠ 3) (h5 : d ≠ 5) :
    hfun 4 d + 1 ≤ d / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R4, saturation part: at the two exceptional degrees the group count
exactly meets the cap (g(3) = 1 = ⌊3/2⌋, g(5) = 2 = ⌊5/2⌋). -/
theorem g_R4_eq {d : ℕ} (h : d = 3 ∨ d = 5) : hfun 4 d = d / 2 := by
  rcases h with rfl | rfl <;> rfl

end

/-! ###### source file: SMaj/Six/Rows.lean ###### -/
section
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

end

/-! ###### source file: SMaj/Six/Shannon.lean ###### -/
section
/-
SMaj/Six/Shannon.lean — the multigraph edge-coloring engine of the (G3)
step, restructuring the ≤ 6 proof's sole external input.

Multigraphs are loopless symmetric multiplicity matrices `m : V → V → ℕ`
with vertex degree `mdeg m v = ∑ u, m v u`; a proper coloring (matching
`shannon_six_of_maxDegree_four` in `SMaj/Six/Targets.lean`) assigns each
parallel class a set of `m u v` distinct colors, classes at a common
vertex disjoint (`IsMulticoloring`).

CLOSED here (sorry-free, kernel-audited):

* `exists_multicoloring_of_le` — **the greedy bound χ′ ≤ 2D − 1** for
  every loopless multigraph with all degrees ≤ D, by induction on the
  edge count (machine-pretested shape: `pretest2_shannon.py` P4).
* `exists_seven_coloring_of_mdeg_le_four` — Δ ≤ 4 ⇒ 7 colors,
  UNCONDITIONALLY: the (G3) step of the L2 construction needs no
  external input at palette 7 (and rows/fill of this library already
  work at any palette ≥ 5), so the future glue gives a fully formal
  `Maj′ ≤ 7` with no open mathematical inputs.
* `exists_three_coloring_of_mdeg_le_two` — Δ ≤ 2 ⇒ 3 colors (the same
  greedy lemma at D = 2; for Δ ≤ 2 the greedy bound IS Shannon's bound).
* `IsMulticoloring.combine` — palette sum: 3-colorings of two halves
  combine to a 6-coloring of their sum (disjoint palette embedding).
* `shannon_six_of_split` / `shannon_six_of_split_hypothesis` — **Shannon
  at Δ = 4 reduced to the Euler 2-split**: if `m = m₁ + m₂` with
  `mdeg mᵢ ≤ 2` then χ′(m) ≤ 6; hence the full
  `shannon_six_of_maxDegree_four` statement follows from
  `exists_two_split` alone (closed implication, no other inputs).

UPDATE (campaign C4, lens C4L3-lean-close, 2026-06-13): the formerly
open `exists_two_split` is now a THEOREM (`SMaj/Six/Euler.lean`, via
walk-free balanced orientations).  Shannon at Δ = 4 is therefore fully
closed: see `shannon_six_of_maxDegree_four` in `SMaj/Six/Targets.lean`.

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.
-/


open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Multigraphs as multiplicity matrices -/

/-- Degree of `v` in the multiplicity matrix `m`. -/
def mdeg (m : V → V → ℕ) (v : V) : ℕ := ∑ u, m v u

/-- `φ` is a proper edge multicoloring of `m`: symmetric, the parallel
class `{u,v}` carries `m u v` distinct colors, and classes at a common
vertex are pairwise disjoint.  This is exactly the conclusion shape of
`shannon_six_of_maxDegree_four` (`SMaj/Six/Targets.lean`). -/
def IsMulticoloring {C : Type*} (m : V → V → ℕ) (φ : V → V → Finset C) : Prop :=
  (∀ u v, φ u v = φ v u) ∧ (∀ u v, #(φ u v) = m u v) ∧
    (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w))

/-- The all-empty coloring is proper for the zero matrix. -/
lemma isMulticoloring_of_zero {C : Type*} {m : V → V → ℕ}
    (hz : ∀ u v, m u v = 0) :
    IsMulticoloring m (fun _ _ => (∅ : Finset C)) :=
  ⟨fun _ _ => rfl, fun u v => by simp [hz], fun _ _ _ _ => by simp⟩

/-- The colors present at a vertex `a` form exactly `mdeg m a` colors. -/
lemma card_biUnion_eq_mdeg {C : Type*} [DecidableEq C] {m : V → V → ℕ}
    {φ : V → V → Finset C} (h : IsMulticoloring m φ) (a : V) :
    #(Finset.univ.biUnion fun w => φ a w) = mdeg m a := by
  rw [Finset.card_biUnion fun x _ y _ hxy => h.2.2 a x y hxy]
  exact Finset.sum_congr rfl fun w _ => h.2.1 a w

/-! ### Decrementing one parallel class -/

/-- `m` with the parallel class `{a,b}` decremented by one. -/
def decr (m : V → V → ℕ) (a b : V) : V → V → ℕ := fun u v =>
  if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then m u v - 1 else m u v

lemma decr_le (m : V → V → ℕ) (a b u v : V) : decr m a b u v ≤ m u v := by
  unfold decr; split <;> omega

lemma decr_ab (m : V → V → ℕ) (a b : V) : decr m a b a b = m a b - 1 := by
  unfold decr; rw [if_pos (Or.inl ⟨rfl, rfl⟩)]

lemma decr_ba (m : V → V → ℕ) (a b : V) : decr m a b b a = m b a - 1 := by
  unfold decr; rw [if_pos (Or.inr ⟨rfl, rfl⟩)]

lemma decr_of_ne (m : V → V → ℕ) {a b u v : V}
    (h : ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a))) : decr m a b u v = m u v := by
  unfold decr; rw [if_neg h]

lemma decr_symm {m : V → V → ℕ} (hsym : ∀ u v, m u v = m v u) (a b : V) :
    ∀ u v, decr m a b u v = decr m a b v u := by
  intro u v; unfold decr
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos (by tauto), hsym]
  · rw [if_neg h, if_neg (by tauto), hsym]

lemma decr_loopless {m : V → V → ℕ} (hloop : ∀ v, m v v = 0) (a b : V) :
    ∀ v, decr m a b v v = 0 := by
  intro v; have := hloop v; unfold decr; split <;> omega

lemma mdeg_decr_le (m : V → V → ℕ) (a b v : V) :
    mdeg (decr m a b) v ≤ mdeg m v :=
  Finset.sum_le_sum fun u _ => decr_le m a b v u

lemma mdeg_decr_lt_left {m : V → V → ℕ} {a b : V} (hab : 0 < m a b) :
    mdeg (decr m a b) a < mdeg m a :=
  Finset.sum_lt_sum (fun u _ => decr_le m a b a u)
    ⟨b, Finset.mem_univ b, by rw [decr_ab]; omega⟩

lemma mdeg_decr_lt_right {m : V → V → ℕ} {a b : V} (hba : 0 < m b a) :
    mdeg (decr m a b) b < mdeg m b :=
  Finset.sum_lt_sum (fun u _ => decr_le m a b b u)
    ⟨a, Finset.mem_univ a, by rw [decr_ba]; omega⟩

/-! ### The greedy bound χ′ ≤ 2D − 1 -/

/-- **Greedy multigraph edge coloring** (induction core): every loopless
symmetric multiplicity matrix with all degrees ≤ D has a proper
edge coloring with k colors whenever 2D ≤ k + 1 (i.e. k ≥ 2D − 1): an
uncolored parallel edge at `{a,b}` sees at most (D−1) colors at `a` and
(D−1) at `b`, and 2D − 2 < k.  Pretested shape: `pretest2_shannon.py`
P4 (invariant asserted at every extension step, 2,880 colorings). -/
theorem exists_multicoloring_of_le {k D : ℕ} (hkD : 2 * D ≤ k + 1) :
    ∀ N (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
      (∀ u v, m u v = m v u) → (∀ v, m v v = 0) → (∀ v, mdeg m v ≤ D) →
      ∃ φ : V → V → Finset (Fin k), IsMulticoloring m φ := by
  intro N
  induction N with
  | zero =>
    intro m htot _ _ _
    refine ⟨fun _ _ => ∅, isMulticoloring_of_zero ?_⟩
    intro u v
    have h1 : mdeg m u ≤ ∑ v, mdeg m v :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
    have h2 : m u v ≤ mdeg m u :=
      Finset.single_le_sum (f := fun w => m u w) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ v)
    omega
  | succ N ih =>
    intro m htot hsym hloop hdeg
    by_cases hex : ∃ a b, 0 < m a b
    · obtain ⟨a, b, hab⟩ := hex
      have hba : 0 < m b a := by rw [← hsym a b]; exact hab
      -- the decremented matrix
      have htot' : ∑ v, mdeg (decr m a b) v ≤ N := by
        have hlt : ∑ v, mdeg (decr m a b) v < ∑ v, mdeg m v :=
          Finset.sum_lt_sum (fun v _ => mdeg_decr_le m a b v)
            ⟨a, Finset.mem_univ a, mdeg_decr_lt_left hab⟩
        omega
      obtain ⟨φ', hφ'⟩ := ih (decr m a b) htot' (decr_symm hsym a b)
        (decr_loopless hloop a b)
        (fun v => le_trans (mdeg_decr_le m a b v) (hdeg v))
      obtain ⟨hsymφ, hcardφ, hdisjφ⟩ := hφ'
      -- a fresh color outside both endpoint palettes
      have hSa : #(Finset.univ.biUnion fun w => φ' a w) + 1 ≤ D := by
        have := card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ a
        have := mdeg_decr_lt_left (m := m) hab
        have := hdeg a
        omega
      have hSb : #(Finset.univ.biUnion fun w => φ' b w) + 1 ≤ D := by
        have := card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ b
        have := mdeg_decr_lt_right (m := m) hba
        have := hdeg b
        omega
      have hfree : ∃ x : Fin k,
          x ∉ (Finset.univ.biUnion fun w => φ' a w) ∪
              (Finset.univ.biUnion fun w => φ' b w) := by
        have hcard := Finset.card_union_le
          (Finset.univ.biUnion fun w => φ' a w)
          (Finset.univ.biUnion fun w => φ' b w)
        have hne : (((Finset.univ.biUnion fun w => φ' a w) ∪
            (Finset.univ.biUnion fun w => φ' b w))ᶜ).Nonempty := by
          rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
          omega
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, Finset.mem_compl.mp hx⟩
      obtain ⟨x, hx⟩ := hfree
      have hxa : ∀ w, x ∉ φ' a w := fun w hmem =>
        hx (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      have hxb : ∀ w, x ∉ φ' b w := fun w hmem =>
        hx (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      -- extend φ' by x on the class {a,b}
      refine ⟨fun u v => φ' u v ∪
        (if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then {x} else ∅), ?_, ?_, ?_⟩
      · -- symmetry
        intro u v; dsimp only
        rw [hsymφ u v]
        congr 1
        by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
        · rw [if_pos h, if_pos (by tauto)]
        · rw [if_neg h, if_neg (by tauto)]
      · -- cardinality
        intro u v; dsimp only
        by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
        · have hxuv : x ∉ φ' u v := by
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa v
            · exact hxb v
          rw [if_pos h, Finset.union_comm, Finset.singleton_union,
            Finset.card_insert_of_notMem hxuv, hcardφ]
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [decr_ab]; omega
          · rw [decr_ba]; omega
        · rw [if_neg h, Finset.union_empty, hcardφ, decr_of_ne m h]
      · -- disjointness at every vertex
        intro u v w hvw; dsimp only
        rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
          Finset.disjoint_union_right]
        refine ⟨⟨hdisjφ u v w hvw, ?_⟩, ?_, ?_⟩
        · -- old class (u,v) vs new singleton at (u,w)
          split_ifs with h
          · rw [Finset.disjoint_singleton_right]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa v
            · exact hxb v
          · exact Finset.disjoint_empty_right _
        · -- new singleton at (u,v) vs old class (u,w)
          split_ifs with h
          · rw [Finset.disjoint_singleton_left]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa w
            · exact hxb w
          · exact Finset.disjoint_empty_left _
        · -- the two singletons cannot both be present (v ≠ w)
          split_ifs with h1 h2
          · exfalso
            apply hvw
            rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
              rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
            · exact h1b.trans h2b.symm
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans h2b.symm
          · exact Finset.disjoint_empty_right _
          · exact Finset.disjoint_empty_left _
          · exact Finset.disjoint_empty_left _
    · -- no edge left: the zero matrix
      simp only [not_exists, not_lt, Nat.le_zero] at hex
      exact ⟨fun _ _ => ∅, isMulticoloring_of_zero hex⟩

/-- **Δ ≤ 4 ⇒ χ′ ≤ 7, unconditional** (greedy at D = 4): the (G3)
multigraph-coloring step of the ≤ 6 construction needs NO external input
at palette 7.  Since the row analysis (`SMaj/Six/Rows.lean`) and the fill
(`SMaj/Six/Fill.lean`, any palette ≥ 5) are palette-generic, this pins a
fully-formal-reachable `Maj′ ≤ 7` — already better than the published 8. -/
theorem exists_seven_coloring_of_mdeg_le_four (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ φ : V → V → Finset (Fin 7), IsMulticoloring m φ :=
  exists_multicoloring_of_le (by omega) (∑ v, mdeg m v) m le_rfl hsym hloop hdeg

/-- **Δ ≤ 2 ⇒ χ′ ≤ 3** (greedy at D = 2; for Δ ≤ 2 the greedy bound is
exactly Shannon's ⌊3Δ/2⌋).  One half of the 2-split route to 6. -/
theorem exists_three_coloring_of_mdeg_le_two (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 2) :
    ∃ φ : V → V → Finset (Fin 3), IsMulticoloring m φ :=
  exists_multicoloring_of_le (by omega) (∑ v, mdeg m v) m le_rfl hsym hloop hdeg

/-! ### Combining palettes: 3 + 3 → 6 -/

/-- `Fin 3 ↪ Fin 6` onto colors {0,1,2}. -/
def loEmb : Fin 3 ↪ Fin 6 :=
  ⟨fun i => ⟨i.1, by omega⟩, fun i j h => by
    have h' : (i : ℕ) = (j : ℕ) := by simpa using h
    exact Fin.ext h'⟩

/-- `Fin 3 ↪ Fin 6` onto colors {3,4,5}. -/
def hiEmb : Fin 3 ↪ Fin 6 :=
  ⟨fun i => ⟨i.1 + 3, by omega⟩, fun i j h => by
    have h' : (i : ℕ) = (j : ℕ) := by simpa using h
    exact Fin.ext h'⟩

/-- The two palette copies are disjoint. -/
lemma disjoint_loEmb_hiEmb (s t : Finset (Fin 3)) :
    Disjoint (s.map loEmb) (t.map hiEmb) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hy
  have h1 : (loEmb i).val = i.val := rfl
  have h2 : (hiEmb j).val = j.val + 3 := rfl
  have := congrArg Fin.val hj
  have hi3 := i.2
  omega

/-- Mapping by an embedding preserves disjointness. -/
lemma disjoint_map_emb {α β : Type*} (f : α ↪ β) {s t : Finset α}
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [Finset.disjoint_left] at h ⊢
  rintro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp hy
  exact h hi (f.injective hje ▸ hj)

/-- **Palette sum**: proper 3-colorings of two halves combine — on the
disjoint palettes {0,1,2} and {3,4,5} — to a proper 6-coloring of the
pointwise sum.  Pretested: `pretest2_shannon.py` P6 (989 instances). -/
theorem IsMulticoloring.combine {m₁ m₂ : V → V → ℕ}
    {φ₁ φ₂ : V → V → Finset (Fin 3)}
    (h₁ : IsMulticoloring m₁ φ₁) (h₂ : IsMulticoloring m₂ φ₂) :
    IsMulticoloring (fun u v => m₁ u v + m₂ u v)
      (fun u v => (φ₁ u v).map loEmb ∪ (φ₂ u v).map hiEmb) := by
  obtain ⟨hs₁, hc₁, hd₁⟩ := h₁
  obtain ⟨hs₂, hc₂, hd₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · intro u v; dsimp only
    rw [hs₁ u v, hs₂ u v]
  · intro u v; dsimp only
    rw [Finset.card_union_of_disjoint (disjoint_loEmb_hiEmb _ _),
      Finset.card_map, Finset.card_map, hc₁, hc₂]
  · intro u v w hvw; dsimp only
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    exact ⟨⟨disjoint_map_emb _ (hd₁ u v w hvw), disjoint_loEmb_hiEmb _ _⟩,
      (disjoint_loEmb_hiEmb _ _).symm, disjoint_map_emb _ (hd₂ u v w hvw)⟩

/-! ### Shannon at Δ = 4, reduced to the Euler 2-split -/

/-- **Shannon's bound at Δ ≤ 4 from a 2-split**: if `m = m₁ + m₂` with
both halves of degree ≤ 2, then `m` has a proper 6-edge-coloring
(3 greedy colors per half on disjoint palettes).  Closed implication. -/
theorem shannon_six_of_split (m m₁ m₂ : V → V → ℕ)
    (hadd : ∀ u v, m u v = m₁ u v + m₂ u v)
    (hsym₁ : ∀ u v, m₁ u v = m₁ v u) (hsym₂ : ∀ u v, m₂ u v = m₂ v u)
    (hloop₁ : ∀ v, m₁ v v = 0) (hloop₂ : ∀ v, m₂ v v = 0)
    (hdeg₁ : ∀ v, mdeg m₁ v ≤ 2) (hdeg₂ : ∀ v, mdeg m₂ v ≤ 2) :
    ∃ φ : V → V → Finset (Fin 6), IsMulticoloring m φ := by
  obtain ⟨φ₁, h₁⟩ := exists_three_coloring_of_mdeg_le_two m₁ hsym₁ hloop₁ hdeg₁
  obtain ⟨φ₂, h₂⟩ := exists_three_coloring_of_mdeg_le_two m₂ hsym₂ hloop₂ hdeg₂
  obtain ⟨hs, hc, hd⟩ := h₁.combine h₂
  exact ⟨fun u v => (φ₁ u v).map loEmb ∪ (φ₂ u v).map hiEmb,
    hs, fun u v => by rw [hc u v, hadd], hd⟩

/- **The Euler 2-split** (the formerly open obligation; replaced
Shannon's theorem as the ≤ 6 proof's sole external input): every loopless
multigraph with Δ ≤ 4 splits into two spanning sub-multigraphs of degree
≤ 2.  Classical proof: pair the (evenly many) odd-degree vertices by new
edges so all degrees lie in {2,4}; per component take an Euler circuit and
2-color its edges alternately, starting an odd-length circuit at a
degree-2 vertex (one exists: degrees in {2,4} with odd edge count force
one); each visit then contributes one edge to each half.  Machine-tested:
`pretest2_shannon.py` P5 (1,189/1,189: exhaustive n ≤ 4 + Euler
construction on random n ≤ 12).
UPDATE (campaign C4, lens C4L3-lean-close, 2026-06-13): this is now a
THEOREM — `exists_two_split` in `SMaj/Six/Euler.lean`, proved via
walk-free balanced orientations, no open inputs. -/

/-- **Shannon at Δ ≤ 4, conditional form**: the exact statement of
`shannon_six_of_maxDegree_four` (`SMaj/Six/Targets.lean`) follows from
the 2-split hypothesis alone.  The hypothesis is discharged by
`exists_two_split` (`SMaj/Six/Euler.lean`), closing Shannon at Δ = 4. -/
theorem shannon_six_of_split_hypothesis
    (hsplit : ∀ m : V → V → ℕ, (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
      (∀ v, mdeg m v ≤ 4) →
      ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
        (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
        (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2))
    (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ φ : V → V → Finset (Fin 6),
      (∀ u v, φ u v = φ v u) ∧ (∀ u v, #(φ u v) = m u v) ∧
      (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w)) := by
  obtain ⟨m₁, m₂, hadd, hsym₁, hsym₂, hdeg₁, hdeg₂⟩ :=
    hsplit m hsym hloop hdeg
  have hloop₁ : ∀ v, m₁ v v = 0 := fun v => by
    have h1 := hadd v v; have h2 := hloop v; omega
  have hloop₂ : ∀ v, m₂ v v = 0 := fun v => by
    have h1 := hadd v v; have h2 := hloop v; omega
  exact shannon_six_of_split m m₁ m₂ hadd hsym₁ hsym₂ hloop₁ hloop₂
    hdeg₁ hdeg₂

end

/-! ###### source file: SMaj/Six/Euler.lean ###### -/
section
/-
SMaj/Six/Euler.lean — the Euler 2-split, fully CLOSED (campaign C4,
lens C4L3-lean-close, 2026-06-13; the augmentation reduction is from
campaign C3, lens C3L4-lean-six, 2026-06-12).

CLOSED (sorry-free):

* `even_sum_mdeg` — the handshake lemma for multiplicity matrices
  (edge-peeling induction over `decr`).
* `even_card_odd_mdeg` — evenly many odd-degree vertices.
* `exists_pairing` — for any evenly-sized vertex set, a perfect-matching
  matrix `p` (degree 1 exactly on the set, 0 elsewhere).
* `two_split_restrict` — a degree-≤ 2 split of an augmented matrix
  `m + p` restricts to one of `m` (subtract the `p`-edges from the part
  containing them; pointwise `min` arithmetic — machine-pretested,
  `pretest2_shannon.py` P7, 2,000/2,000).
* `two_split_of_even_split_hypothesis` — **the reduction**: if every
  EVEN loopless multigraph with Δ ≤ 4 2-splits, then every loopless
  multigraph with Δ ≤ 4 2-splits (pair the odd vertices — evenly many —
  by `exists_pairing`; degrees stay ≤ 4 because an odd degree is ≤ 3;
  split the even augmented matrix; restrict).
* `orient_core` / `exists_balanced_orientation` — **walk-free Eulerian
  orientation**: every even symmetric loopless matrix orients with
  in-degree = out-degree (mutual edge-count induction tracking an open
  trail; no Euler circuits formalized).  Pretested:
  `lenses/C4L3-lean-close/pretest3_orient.py` P8 (543 instances).
* `exists_two_split_even` — **the even-degree core, CLOSED**: balanced
  orientation + balanced orientation of the odd-paired bipartite double
  + `two_split_restrict`.  Pretested end-to-end: `pretest3_orient.py`
  P9 (756 instances, exact verification).
* `exists_two_split` — **the full Euler 2-split** (Δ ≤ 4 splits into two
  Δ ≤ 2 halves), no open inputs.  Shannon's bound at Δ = 4 follows
  (`shannon_six_of_maxDegree_four`, `SMaj/Six/Targets.lean`).
-/


open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Exact degree bookkeeping for `decr` -/

lemma mdeg_decr_eq_left {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hab : 0 < m a b) : mdeg (decr m a b) a = mdeg m a - 1 := by
  have hsplit₁ : decr m a b a b + ∑ u ∈ Finset.univ.erase b, decr m a b a u =
      mdeg (decr m a b) a := Finset.add_sum_erase _ _ (Finset.mem_univ b)
  have hsplit₂ : m a b + ∑ u ∈ Finset.univ.erase b, m a u = mdeg m a :=
    Finset.add_sum_erase _ _ (Finset.mem_univ b)
  have hcongr : ∑ u ∈ Finset.univ.erase b, decr m a b a u =
      ∑ u ∈ Finset.univ.erase b, m a u := by
    refine Finset.sum_congr rfl fun u hu => decr_of_ne m ?_
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact (Finset.mem_erase.mp hu).1 h
    · exact hne h
  rw [decr_ab] at hsplit₁
  omega

lemma mdeg_decr_eq_right {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hba : 0 < m b a) : mdeg (decr m a b) b = mdeg m b - 1 := by
  have hsplit₁ : decr m a b b a + ∑ u ∈ Finset.univ.erase a, decr m a b b u =
      mdeg (decr m a b) b := Finset.add_sum_erase _ _ (Finset.mem_univ a)
  have hsplit₂ : m b a + ∑ u ∈ Finset.univ.erase a, m b u = mdeg m b :=
    Finset.add_sum_erase _ _ (Finset.mem_univ a)
  have hcongr : ∑ u ∈ Finset.univ.erase a, decr m a b b u =
      ∑ u ∈ Finset.univ.erase a, m b u := by
    refine Finset.sum_congr rfl fun u hu => decr_of_ne m ?_
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hne h.symm
    · exact (Finset.mem_erase.mp hu).1 h
  rw [decr_ba] at hsplit₁
  omega

lemma mdeg_decr_eq_other {m : V → V → ℕ} {a b v : V} (hva : v ≠ a)
    (hvb : v ≠ b) : mdeg (decr m a b) v = mdeg m v := by
  refine Finset.sum_congr rfl fun u _ => decr_of_ne m ?_
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact hva h
  · exact hvb h

/-- Removing one (a,b) edge lowers the total degree by exactly 2. -/
lemma sum_mdeg_decr {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hab : 0 < m a b) (hba : 0 < m b a) :
    ∑ v, mdeg (decr m a b) v + 2 = ∑ v, mdeg m v := by
  have hsplit : ∀ g : V → ℕ, ∑ v, g v =
      g a + (g b + ∑ v ∈ (Finset.univ.erase a).erase b, g v) := by
    intro g
    rw [Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ b⟩),
      Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have h₁ := hsplit fun v => mdeg (decr m a b) v
  have h₂ := hsplit fun v => mdeg m v
  have hcongr : ∑ v ∈ (Finset.univ.erase a).erase b, mdeg (decr m a b) v =
      ∑ v ∈ (Finset.univ.erase a).erase b, mdeg m v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' := Finset.mem_erase.mp hv
    have hv'' := Finset.mem_erase.mp hv'.2
    exact mdeg_decr_eq_other hv''.1 hv'.1
  have hda : 0 < mdeg m a :=
    lt_of_lt_of_le hab (Finset.single_le_sum (f := fun u => m a u)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ b))
  have hdb : 0 < mdeg m b :=
    lt_of_lt_of_le hba (Finset.single_le_sum (f := fun u => m b u)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ a))
  have hea := mdeg_decr_eq_left hne hab
  have heb := mdeg_decr_eq_right hne hba
  omega

/-! ### The handshake lemma and the odd-vertex count -/

/-- **Handshake**: a symmetric loopless multiplicity matrix has even
total degree (edge-peeling induction). -/
theorem even_sum_mdeg (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) : Even (∑ v, mdeg m v) := by
  suffices h : ∀ N (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
      (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
      Even (∑ v, mdeg m v) from h _ m le_rfl hsym hloop
  intro N
  induction N with
  | zero =>
    intro m htot _ _
    rw [Nat.le_zero.mp htot]
    exact ⟨0, rfl⟩
  | succ N ih =>
    intro m htot hsym hloop
    by_cases hex : ∃ a b, 0 < m a b
    · obtain ⟨a, b, hab⟩ := hex
      have hne : a ≠ b := by
        rintro rfl; have := hloop a; omega
      have hba : 0 < m b a := by rw [← hsym a b]; exact hab
      have hdrop := sum_mdeg_decr hne hab hba
      obtain ⟨c, hc⟩ := ih (decr m a b) (by omega) (decr_symm hsym a b)
        (decr_loopless hloop a b)
      exact ⟨c + 1, by omega⟩
    · simp only [not_exists, not_lt, Nat.le_zero] at hex
      have hz : ∑ v, mdeg m v = 0 :=
        Finset.sum_eq_zero fun v _ =>
          Finset.sum_eq_zero fun u _ => hex v u
      rw [hz]; exact ⟨0, rfl⟩

/-- **Evenly many odd-degree vertices.** -/
theorem even_card_odd_mdeg (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) :
    Even #(Finset.univ.filter fun v => Odd (mdeg m v)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v => Odd (mdeg m v)) fun v => mdeg m v
  -- the even-degree rows sum to an even number
  have heven_part : Even (∑ v ∈ Finset.univ.filter
      (fun v => ¬ Odd (mdeg m v)), mdeg m v) :=
    Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩
      fun v hv => Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hv).2
  have htot := even_sum_mdeg m hsym hloop
  -- so the odd-degree rows sum to an even number
  have hodd_sum : Even (∑ v ∈ Finset.univ.filter
      (fun v => Odd (mdeg m v)), mdeg m v) := by
    obtain ⟨c, hc⟩ := heven_part
    obtain ⟨d, hd⟩ := htot
    exact ⟨d - c, by omega⟩
  -- each odd row is (even) + 1, so the sum is (even) + the card
  have hshift : ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), mdeg m v =
      (∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), (mdeg m v - 1)) +
        #(Finset.univ.filter fun v => Odd (mdeg m v)) := by
    have h1 : ∀ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
        mdeg m v = (mdeg m v - 1) + 1 := by
      intro v hv
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hv).2
      omega
    calc ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), mdeg m v
        = ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
            ((mdeg m v - 1) + 1) := Finset.sum_congr rfl h1
      _ = (∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
            (mdeg m v - 1)) +
          ∑ _v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), 1 :=
            Finset.sum_add_distrib
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have heven_shift : Even (∑ v ∈ Finset.univ.filter
      (fun v => Odd (mdeg m v)), (mdeg m v - 1)) :=
    Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩ fun v hv => by
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hv).2
      exact ⟨k, by omega⟩
  obtain ⟨c, hc⟩ := hodd_sum
  obtain ⟨d, hd⟩ := heven_shift
  exact ⟨c - d, by omega⟩

/-! ### Pairing an even vertex set -/

/-- The single-edge matrix on the pair `{x, y}`. -/
def pairUnit (x y : V) : V → V → ℕ := fun u v =>
  if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then 1 else 0

lemma pairUnit_symm (x y : V) : ∀ u v, pairUnit x y u v = pairUnit x y v u := by
  intro u v; unfold pairUnit
  by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
  · rw [if_pos h, if_pos (by tauto)]
  · rw [if_neg h, if_neg (by tauto)]

lemma pairUnit_loopless {x y : V} (hxy : x ≠ y) :
    ∀ v, pairUnit x y v v = 0 := by
  intro v; unfold pairUnit
  rw [if_neg]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hxy (h1.symm.trans h2)
  · exact hxy (h2.symm.trans h1)

lemma mdeg_pairUnit {x y : V} (hxy : x ≠ y) (v : V) :
    mdeg (pairUnit x y) v = if v = x ∨ v = y then 1 else 0 := by
  by_cases hvx : v = x
  · subst hvx
    rw [if_pos (Or.inl rfl)]
    have hsplit : pairUnit v y v y +
        ∑ u ∈ Finset.univ.erase y, pairUnit v y v u = mdeg (pairUnit v y) v :=
      Finset.add_sum_erase _ _ (Finset.mem_univ y)
    have h1 : pairUnit v y v y = 1 := by
      unfold pairUnit; rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
    have h0 : ∑ u ∈ Finset.univ.erase y, pairUnit v y v u = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      unfold pairUnit
      rw [if_neg]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact (Finset.mem_erase.mp hu).1 h
      · exact hxy h
    omega
  · by_cases hvy : v = y
    · subst hvy
      rw [if_pos (Or.inr rfl)]
      have hsplit : pairUnit x v v x +
          ∑ u ∈ Finset.univ.erase x, pairUnit x v v u =
          mdeg (pairUnit x v) v :=
        Finset.add_sum_erase _ _ (Finset.mem_univ x)
      have h1 : pairUnit x v v x = 1 := by
        unfold pairUnit; rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
      have h0 : ∑ u ∈ Finset.univ.erase x, pairUnit x v v u = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        unfold pairUnit
        rw [if_neg]
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hxy h.symm
        · exact (Finset.mem_erase.mp hu).1 h
      omega
    · rw [if_neg (by tauto)]
      refine Finset.sum_eq_zero fun u _ => ?_
      unfold pairUnit
      rw [if_neg]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hvx h
      · exact hvy h

/-- **Pairing**: every evenly-sized vertex set carries a perfect-matching
matrix (symmetric, loopless, degree 1 exactly on the set). -/
theorem exists_pairing :
    ∀ (s : Finset V), Even #s →
      ∃ p : V → V → ℕ, (∀ u v, p u v = p v u) ∧ (∀ v, p v v = 0) ∧
        (∀ v, mdeg p v = if v ∈ s then 1 else 0) := by
  suffices h : ∀ (k : ℕ) (s : Finset V), #s ≤ k → Even #s →
      ∃ p : V → V → ℕ, (∀ u v, p u v = p v u) ∧ (∀ v, p v v = 0) ∧
        (∀ v, mdeg p v = if v ∈ s then 1 else 0) from
    fun s hs => h #s s le_rfl hs
  intro k
  induction k with
  | zero =>
    intro s hcard _
    have hempty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    exact ⟨fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun v => by
      simp [mdeg]⟩
  | succ k ih =>
    intro s hcard heven
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun v => by
        simp [mdeg]⟩
    · -- two distinct elements of s
      have hpos : 0 < #s := Finset.card_pos.mpr ⟨x, hx⟩
      have h2 : 2 ≤ #s := by
        obtain ⟨c, hc⟩ := heven; omega
      have herase : #(s.erase x) = #s - 1 := Finset.card_erase_of_mem hx
      have hpos2 : 0 < #(s.erase x) := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos2
      obtain ⟨hyx, hys⟩ := Finset.mem_erase.mp hy
      have hxy : x ≠ y := hyx.symm
      -- recurse on s minus the pair
      have hcard' : #((s.erase x).erase y) = #s - 2 := by
        rw [Finset.card_erase_of_mem hy, herase]
        omega
      obtain ⟨p', hsym', hloop', hdeg'⟩ := ih ((s.erase x).erase y)
        (by omega) (by obtain ⟨c, hc⟩ := heven; exact ⟨c - 1, by omega⟩)
      refine ⟨fun u v => p' u v + pairUnit x y u v, ?_, ?_, ?_⟩
      · intro u v; dsimp only; rw [hsym' u v, pairUnit_symm x y u v]
      · intro v; dsimp only; rw [hloop' v, pairUnit_loopless hxy v]
      · intro v
        have hadd : mdeg (fun u v => p' u v + pairUnit x y u v) v =
            mdeg p' v + mdeg (pairUnit x y) v := by
          unfold mdeg; exact Finset.sum_add_distrib
        rw [hadd, hdeg' v, mdeg_pairUnit hxy v]
        by_cases hvx : v = x
        · subst hvx
          rw [if_neg (show v ∉ (s.erase v).erase y from fun h =>
              (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl),
            if_pos (show v = v ∨ v = y from Or.inl rfl), if_pos hx]
        · by_cases hvy : v = y
          · subst hvy
            rw [if_neg (show v ∉ (s.erase x).erase v from fun h =>
                (Finset.mem_erase.mp h).1 rfl),
              if_pos (show v = x ∨ v = v from Or.inr rfl), if_pos hys]
          · rw [if_neg (show ¬(v = x ∨ v = y) from by tauto)]
            by_cases hvs : v ∈ s
            · rw [if_pos (show v ∈ (s.erase x).erase y from
                Finset.mem_erase.mpr ⟨hvy, Finset.mem_erase.mpr ⟨hvx, hvs⟩⟩),
                if_pos hvs]
            · rw [if_neg (show v ∉ (s.erase x).erase y from fun h =>
                hvs (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))),
                if_neg hvs]

/-! ### Restricting a split of an augmented matrix -/

/-- **Restriction** (pretested: `pretest2_shannon.py` P7): a degree-≤ 2
split `s₁ + s₂` of an augmented matrix `m + p` restricts to a degree-≤ 2
split of `m`: take `m₁ = s₁ − min s₁ p` and the rest.  All conditions are
pointwise `min` arithmetic. -/
theorem two_split_restrict {m p s₁ s₂ : V → V → ℕ}
    (hadd : ∀ u v, m u v + p u v = s₁ u v + s₂ u v)
    (hsymm : ∀ u v, m u v = m v u) (hsymp : ∀ u v, p u v = p v u)
    (hsym₁ : ∀ u v, s₁ u v = s₁ v u)
    (hdeg₁ : ∀ v, mdeg s₁ v ≤ 2) (hdeg₂ : ∀ v, mdeg s₂ v ≤ 2) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  refine ⟨fun u v => s₁ u v - min (s₁ u v) (p u v),
    fun u v => m u v - (s₁ u v - min (s₁ u v) (p u v)), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; have := hadd u v; dsimp only; omega
  · intro u v; dsimp only; rw [hsym₁ u v, hsymp u v]
  · intro u v; dsimp only; rw [hsymm u v, hsym₁ u v, hsymp u v]
  · intro v
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hdeg₁ v)
    dsimp only; omega
  · intro v
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hdeg₂ v)
    have := hadd v u; dsimp only; omega

/-! ### Directed matrices: in-degree, unit edges, and small algebra

The even-degree core is closed below WITHOUT Euler circuits: a balanced
("Eulerian") orientation is built by a walk-free mutual induction
(`orient_core`), applied twice — once on `V`, once on the bipartite
double `V ⊕ V` — and the two directions of the second orientation are the
two halves.  Machine-pretested end-to-end:
`lenses/C4L3-lean-close/pretest3_orient.py` P8/P9 (campaign C4). -/

/-- In-degree (column sum) of a directed multiplicity matrix; the
out-degree is the row sum `mdeg`. -/
def indeg (d : V → V → ℕ) (v : V) : ℕ := ∑ u, d u v

/-- An orientation `d` of `m` (`d u v + d v u = m u v`) splits each vertex
degree as out + in. -/
lemma mdeg_add_indeg {m d : V → V → ℕ}
    (hsum : ∀ u v, d u v + d v u = m u v) (v : V) :
    mdeg d v + indeg d v = mdeg m v := by
  show (∑ u, d v u) + ∑ u, d u v = ∑ u, m v u
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => hsum v u

/-- The single directed edge `a → b`. -/
def dirUnit (a b : V) : V → V → ℕ := fun u v => if u = a ∧ v = b then 1 else 0

lemma sum_dirUnit_row (a b v : V) :
    (∑ u, dirUnit a b v u) = if v = a then 1 else 0 := by
  by_cases hva : v = a
  · simp [dirUnit, hva]
  · simp [dirUnit, hva]

lemma sum_dirUnit_col (a b v : V) :
    (∑ u, dirUnit a b u v) = if v = b then 1 else 0 := by
  by_cases hvb : v = b
  · simp [dirUnit, hvb]
  · simp [dirUnit, hvb]

lemma mdeg_add_dirUnit (d : V → V → ℕ) (a b v : V) :
    mdeg (fun u w => d u w + dirUnit a b u w) v =
      mdeg d v + if v = a then 1 else 0 := by
  show (∑ u, (d v u + dirUnit a b v u)) = _
  rw [Finset.sum_add_distrib, sum_dirUnit_row]
  rfl

lemma indeg_add_dirUnit (d : V → V → ℕ) (a b v : V) :
    indeg (fun u w => d u w + dirUnit a b u w) v =
      indeg d v + if v = b then 1 else 0 := by
  show (∑ u, (d u v + dirUnit a b u v)) = _
  rw [Finset.sum_add_distrib, sum_dirUnit_col]
  rfl

lemma pairUnit_comm (a b : V) : ∀ u v, pairUnit a b u v = pairUnit b a u v := by
  intro u v; unfold pairUnit
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos (by tauto)]
  · rw [if_neg h, if_neg (by tauto)]

/-- The two directions of one undirected unit edge. -/
lemma dirUnit_add_swap {a b : V} (hab : a ≠ b) (u v : V) :
    dirUnit a b u v + dirUnit a b v u = pairUnit a b u v := by
  unfold dirUnit pairUnit
  by_cases h1 : u = a ∧ v = b
  · have h2 : ¬(v = a ∧ u = b) := fun h => hab (h1.1.symm.trans h.2)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1)]
  · by_cases h2 : v = a ∧ u = b
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr ⟨h2.2, h2.1⟩)]
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      rintro (h | ⟨hb, ha⟩)
      · exact h1 h
      · exact h2 ⟨ha, hb⟩

/-- Putting one removed edge back. -/
lemma decr_add_pairUnit {m : V → V → ℕ} {a b : V}
    (hab : 0 < m a b) (hba : 0 < m b a) :
    ∀ u v, decr m a b u v + pairUnit a b u v = m u v := by
  intro u v
  unfold decr pairUnit
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos h]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · rw [if_neg h, if_neg h]
    omega

/-! ### Balanced orientations (the walk-free Euler engine) -/

/-- **Balanced-orientation engine** (mutual induction on the edge count;
pretested: `pretest3_orient.py` P8).  (A) Every symmetric loopless matrix
with all degrees even has an orientation with in-degree = out-degree at
every vertex.  (B) With odd degrees at exactly two vertices `x ≠ y`, an
orientation with one extra out at `x` and one extra in at `y` — the
formal "open trail from x to y", built edge by edge: case (A) peels any
edge `(a, b)` and closes the trail (B) of the rest; case (B) peels an
edge `(x, c)` at the source and either finishes (`c = y`, rest even) or
continues the trail from `c`. -/
theorem orient_core : ∀ (N : ℕ) (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
    (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
    ((∀ v, Even (mdeg m v)) →
      ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
        ∀ v, indeg d v = mdeg d v) ∧
    (∀ x y : V, x ≠ y → Odd (mdeg m x) → Odd (mdeg m y) →
      (∀ v, v ≠ x → v ≠ y → Even (mdeg m v)) →
      ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
        ∀ v, indeg d v + (if v = x then 1 else 0) =
          mdeg d v + (if v = y then 1 else 0)) := by
  intro N
  induction N with
  | zero =>
    intro m htot _ _
    have hz : ∀ u v, m u v = 0 := by
      intro u v
      have h1 : mdeg m u ≤ ∑ v, mdeg m v :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
      have h2 : m u v ≤ mdeg m u :=
        Finset.single_le_sum (f := fun w => m u w) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ v)
      omega
    constructor
    · intro _
      exact ⟨fun _ _ => 0, fun u v => by have := hz u v; dsimp only; omega,
        fun v => rfl⟩
    · intro x y _ hox _ _
      exfalso
      have h1 : mdeg m x ≤ ∑ v, mdeg m v :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)
      obtain ⟨k, hk⟩ := hox
      omega
  | succ N ih =>
    intro m htot hsym hloop
    constructor
    · -- (A): all degrees even
      intro heven
      by_cases hex : ∃ a b, 0 < m a b
      · obtain ⟨a, b, hab⟩ := hex
        have hne : a ≠ b := by rintro rfl; have := hloop a; omega
        have hba : 0 < m b a := by rw [← hsym a b]; exact hab
        have hdrop := sum_mdeg_decr hne hab hba
        have hda : 0 < mdeg m a :=
          lt_of_lt_of_le hab (Finset.single_le_sum (f := fun u => m a u)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ b))
        have hdb : 0 < mdeg m b :=
          lt_of_lt_of_le hba (Finset.single_le_sum (f := fun u => m b u)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ a))
        have hoa : Odd (mdeg (decr m a b) a) := by
          rw [mdeg_decr_eq_left hne hab]
          obtain ⟨k, hk⟩ := heven a
          exact ⟨k - 1, by omega⟩
        have hob : Odd (mdeg (decr m a b) b) := by
          rw [mdeg_decr_eq_right hne hba]
          obtain ⟨k, hk⟩ := heven b
          exact ⟨k - 1, by omega⟩
        have hev' : ∀ v, v ≠ a → v ≠ b → Even (mdeg (decr m a b) v) := by
          intro v hva hvb
          rw [mdeg_decr_eq_other hva hvb]
          exact heven v
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m a b) (by omega)
          (decr_symm hsym a b) (decr_loopless hloop a b)).2 a b hne hoa hob hev'
        refine ⟨fun u v => d' u v + dirUnit b a u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hne.symm u v
          have hpc := pairUnit_comm a b u v
          have hp := decr_add_pairUnit hab hba u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          exact hbal' v
      · simp only [not_exists, not_lt, Nat.le_zero] at hex
        exact ⟨fun _ _ => 0, fun u v => by have := hex u v; dsimp only; omega,
          fun v => rfl⟩
    · -- (B): the open trail from x to y
      intro x y hxy hox hoy hev
      have hpos : 0 < mdeg m x := by obtain ⟨k, hk⟩ := hox; omega
      have hexc : ∃ c, 0 < m x c := by
        by_contra h
        push_neg at h
        have hz : mdeg m x = 0 :=
          Finset.sum_eq_zero fun u _ => Nat.le_zero.mp (h u)
        omega
      obtain ⟨c, hxc⟩ := hexc
      have hnxc : x ≠ c := by rintro rfl; have := hloop x; omega
      have hcx : 0 < m c x := by rw [← hsym x c]; exact hxc
      have hdrop := sum_mdeg_decr hnxc hxc hcx
      have hdc : 0 < mdeg m c :=
        lt_of_lt_of_le hcx (Finset.single_le_sum (f := fun u => m c u)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ x))
      by_cases hcy : c = y
      · -- the trail closes: the rest is all even
        subst hcy
        have heven' : ∀ v, Even (mdeg (decr m x c) v) := by
          intro v
          by_cases hvx : v = x
          · subst hvx
            rw [mdeg_decr_eq_left hnxc hxc]
            obtain ⟨k, hk⟩ := hox
            exact ⟨k, by omega⟩
          · by_cases hvc : v = c
            · subst hvc
              rw [mdeg_decr_eq_right hnxc hcx]
              obtain ⟨k, hk⟩ := hoy
              exact ⟨k, by omega⟩
            · rw [mdeg_decr_eq_other hvx hvc]
              exact hev v hvx hvc
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m x c) (by omega)
          (decr_symm hsym x c) (decr_loopless hloop x c)).1 heven'
        refine ⟨fun u v => d' u v + dirUnit x c u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hnxc u v
          have hp := decr_add_pairUnit hxc hcx u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          have hb := hbal' v
          omega
      · -- the trail continues from c
        have hoc : Odd (mdeg (decr m x c) c) := by
          rw [mdeg_decr_eq_right hnxc hcx]
          obtain ⟨k, hk⟩ := hev c (Ne.symm hnxc) hcy
          exact ⟨k - 1, by omega⟩
        have hoy' : Odd (mdeg (decr m x c) y) := by
          rw [mdeg_decr_eq_other (Ne.symm hxy) (Ne.symm hcy)]
          exact hoy
        have hev' : ∀ v, v ≠ c → v ≠ y → Even (mdeg (decr m x c) v) := by
          intro v hvc hvy
          by_cases hvx : v = x
          · subst hvx
            rw [mdeg_decr_eq_left hnxc hxc]
            obtain ⟨k, hk⟩ := hox
            exact ⟨k, by omega⟩
          · rw [mdeg_decr_eq_other hvx hvc]
            exact hev v hvx hvy
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m x c) (by omega)
          (decr_symm hsym x c) (decr_loopless hloop x c)).2 c y hcy hoc hoy' hev'
        refine ⟨fun u v => d' u v + dirUnit x c u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hnxc u v
          have hp := decr_add_pairUnit hxc hcx u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          have hb := hbal' v
          omega

/-- **Eulerian (balanced) orientation** of an even loopless multigraph. -/
theorem exists_balanced_orientation (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (heven : ∀ v, Even (mdeg m v)) :
    ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
      ∀ v, indeg d v = mdeg d v :=
  (orient_core (∑ v, mdeg m v) m le_rfl hsym hloop).1 heven

/-! ### The bipartite double of an orientation -/

/-- Bipartite double: vertex set `V ⊕ V`, one edge `inl u — inr v` per
directed edge `u → v` of `d`. -/
def biMat (d : V → V → ℕ) : (V ⊕ V) → (V ⊕ V) → ℕ
  | Sum.inl u, Sum.inr v => d u v
  | Sum.inr v, Sum.inl u => d u v
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

lemma biMat_symm (d : V → V → ℕ) : ∀ a b, biMat d a b = biMat d b a := by
  rintro (u | u) (v | v) <;> rfl

lemma biMat_loopless (d : V → V → ℕ) : ∀ a, biMat d a a = 0 := by
  rintro (u | u) <;> rfl

lemma mdeg_biMat_inl (d : V → V → ℕ) (v : V) :
    mdeg (biMat d) (Sum.inl v) = mdeg d v := by
  show (∑ a : V ⊕ V, biMat d (Sum.inl v) a) = ∑ u, d v u
  rw [Fintype.sum_sum_type]
  have h1 : (∑ u : V, biMat d (Sum.inl v) (Sum.inl u)) = 0 :=
    Finset.sum_eq_zero fun u _ => rfl
  have h2 : (∑ u : V, biMat d (Sum.inl v) (Sum.inr u)) = ∑ u, d v u :=
    Finset.sum_congr rfl fun u _ => rfl
  omega

lemma mdeg_biMat_inr (d : V → V → ℕ) (v : V) :
    mdeg (biMat d) (Sum.inr v) = indeg d v := by
  show (∑ a : V ⊕ V, biMat d (Sum.inr v) a) = ∑ u, d u v
  rw [Fintype.sum_sum_type]
  have h1 : (∑ u : V, biMat d (Sum.inr v) (Sum.inl u)) = ∑ u, d u v :=
    Finset.sum_congr rfl fun u _ => rfl
  have h2 : (∑ u : V, biMat d (Sum.inr v) (Sum.inr u)) = 0 :=
    Finset.sum_eq_zero fun u _ => rfl
  omega

/-! ### The even-degree core, CLOSED -/

/-- **The even-degree core** (formerly the open Euler step — now CLOSED,
without Euler circuits): every loopless multigraph with all degrees EVEN
and ≤ 4 splits into two halves of degree ≤ 2.  Proof: balanced-orient `m`
(`orient_core`, degrees become out = in = mdeg/2 ≤ 2); pair the odd
vertices of the bipartite double `biMat d` (`exists_pairing`) and
balanced-orient the augmented double (degrees ≤ 3, so out = in ≤ 1); the
two directions of that orientation classify the edges of `m` into two
halves meeting every vertex ≤ 1 + 1 = 2 times; `two_split_restrict`
removes the pairing shadow.  Machine-pretested end-to-end:
`lenses/C4L3-lean-close/pretest3_orient.py` P9. -/
theorem exists_two_split_even (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) (heven : ∀ v, Even (mdeg m v)) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  obtain ⟨d, hdsum, hdbal⟩ := exists_balanced_orientation m hsym hloop heven
  have hdhalf : ∀ v, mdeg d v ≤ 2 := by
    intro v
    have h1 := mdeg_add_indeg hdsum v
    have h2 := hdbal v
    have h3 := hdeg v
    omega
  have hihalf : ∀ v, indeg d v ≤ 2 := by
    intro v
    have h1 := hdbal v
    have h2 := hdhalf v
    omega
  -- pair the odd vertices of the bipartite double
  obtain ⟨p, hpsym, hploop, hpdeg⟩ := exists_pairing
    (Finset.univ.filter fun w : V ⊕ V => Odd (mdeg (biMat d) w))
    (even_card_odd_mdeg (biMat d) (biMat_symm d) (biMat_loopless d))
  have hpdeg' : ∀ w, mdeg p w =
      if Odd (mdeg (biMat d) w) then 1 else 0 := by
    intro w
    rw [hpdeg w]
    by_cases h : Odd (mdeg (biMat d) w)
    · have hmem : w ∈ Finset.univ.filter
          fun w : V ⊕ V => Odd (mdeg (biMat d) w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩
      rw [if_pos hmem, if_pos h]
    · have hmem : w ∉ Finset.univ.filter
          fun w : V ⊕ V => Odd (mdeg (biMat d) w) :=
        fun hmem => h (Finset.mem_filter.mp hmem).2
      rw [if_neg hmem, if_neg h]
  have hBpadd : ∀ w, mdeg (fun a b => biMat d a b + p a b) w =
      mdeg (biMat d) w + mdeg p w := by
    intro w
    show (∑ a, (biMat d w a + p w a)) = _
    rw [Finset.sum_add_distrib]
    rfl
  -- balanced orientation of the augmented (all-even) double
  obtain ⟨D, hDsum, hDbal⟩ := exists_balanced_orientation
    (fun a b => biMat d a b + p a b)
    (fun a b => by dsimp only; rw [biMat_symm d a b, hpsym a b])
    (fun a => by dsimp only; rw [biMat_loopless d a, hploop a])
    (fun w => by
      rw [hBpadd w, hpdeg' w]
      rcases Nat.even_or_odd (mdeg (biMat d) w) with h | h
      · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by omega⟩
      · rw [if_pos h]
        obtain ⟨k, hk⟩ := h
        exact ⟨k + 1, by omega⟩)
  -- per-vertex bound on the double orientation: out = in ≤ 1
  have hDtot : ∀ w, mdeg D w + indeg D w = mdeg (biMat d) w + mdeg p w := by
    intro w
    have h1 : ∀ a, D w a + D a w = biMat d w a + p w a := fun a => hDsum w a
    show (∑ a, D w a) + ∑ a, D a w = (∑ a, biMat d w a) + ∑ a, p w a
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => h1 a
  have hD1 : ∀ w, mdeg D w ≤ 1 := by
    intro w
    have h1 := hDtot w
    have h2 := hDbal w
    have h4 := hpdeg' w
    have h5 : mdeg (biMat d) w ≤ 2 := by
      rcases w with v | v
      · rw [mdeg_biMat_inl]; exact hdhalf v
      · rw [mdeg_biMat_inr]; exact hihalf v
    by_cases ho : Odd (mdeg (biMat d) w)
    · rw [if_pos ho] at h4; omega
    · rw [if_neg ho] at h4; omega
  have hD1' : ∀ w, indeg D w ≤ 1 := by
    intro w
    have h1 := hDbal w
    have h2 := hD1 w
    omega
  -- the two halves and the pairing shadow
  have hadd : ∀ u v,
      m u v + (p (Sum.inl u) (Sum.inr v) + p (Sum.inl v) (Sum.inr u)) =
      (D (Sum.inl u) (Sum.inr v) + D (Sum.inl v) (Sum.inr u)) +
      (D (Sum.inr v) (Sum.inl u) + D (Sum.inr u) (Sum.inl v)) := by
    intro u v
    have h1 := hDsum (Sum.inl u) (Sum.inr v)
    have h2 := hDsum (Sum.inl v) (Sum.inr u)
    have hb1 : biMat d (Sum.inl u) (Sum.inr v) = d u v := rfl
    have hb2 : biMat d (Sum.inl v) (Sum.inr u) = d v u := rfl
    have h3 := hdsum u v
    omega
  refine two_split_restrict
    (m := m)
    (p := fun u v => p (Sum.inl u) (Sum.inr v) + p (Sum.inl v) (Sum.inr u))
    (s₁ := fun u v => D (Sum.inl u) (Sum.inr v) + D (Sum.inl v) (Sum.inr u))
    (s₂ := fun u v => D (Sum.inr v) (Sum.inl u) + D (Sum.inr u) (Sum.inl v))
    hadd hsym ?_ ?_ ?_ ?_
  · intro u v; dsimp only; omega
  · intro u v; dsimp only; omega
  · -- degree bound on the first half
    intro v
    have hsplit : mdeg (fun u w => D (Sum.inl u) (Sum.inr w) +
        D (Sum.inl w) (Sum.inr u)) v =
        (∑ u, D (Sum.inl v) (Sum.inr u)) + ∑ u, D (Sum.inl u) (Sum.inr v) := by
      show (∑ u, (D (Sum.inl v) (Sum.inr u) + D (Sum.inl u) (Sum.inr v))) = _
      rw [Finset.sum_add_distrib]
    have hle1 : (∑ u, D (Sum.inl v) (Sum.inr u)) ≤ mdeg D (Sum.inl v) := by
      show _ ≤ ∑ a : V ⊕ V, D (Sum.inl v) a
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_left _ _
    have hle2 : (∑ u, D (Sum.inl u) (Sum.inr v)) ≤ indeg D (Sum.inr v) := by
      show _ ≤ ∑ a : V ⊕ V, D a (Sum.inr v)
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_right _ _
    have h1 := hD1 (Sum.inl v)
    have h2 := hD1' (Sum.inr v)
    omega
  · -- degree bound on the second half
    intro v
    have hsplit : mdeg (fun u w => D (Sum.inr w) (Sum.inl u) +
        D (Sum.inr u) (Sum.inl w)) v =
        (∑ u, D (Sum.inr u) (Sum.inl v)) + ∑ u, D (Sum.inr v) (Sum.inl u) := by
      show (∑ u, (D (Sum.inr u) (Sum.inl v) + D (Sum.inr v) (Sum.inl u))) = _
      rw [Finset.sum_add_distrib]
    have hle1 : (∑ u, D (Sum.inr u) (Sum.inl v)) ≤ indeg D (Sum.inl v) := by
      show _ ≤ ∑ a : V ⊕ V, D a (Sum.inl v)
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_left _ _
    have hle2 : (∑ u, D (Sum.inr v) (Sum.inl u)) ≤ mdeg D (Sum.inr v) := by
      show _ ≤ ∑ a : V ⊕ V, D (Sum.inr v) a
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_right _ _
    have h1 := hD1' (Sum.inl v)
    have h2 := hD1 (Sum.inr v)
    omega

/-- **The augmentation reduction**: if every even loopless multigraph with
Δ ≤ 4 2-splits (`exists_two_split_even`), then every loopless multigraph
with Δ ≤ 4 2-splits (`exists_two_split`) — pair the odd-degree vertices
(evenly many, `even_card_odd_mdeg`/`exists_pairing`), split the augmented
even matrix, and restrict (`two_split_restrict`). -/
theorem two_split_of_even_split_hypothesis
    (heven_split : ∀ M : V → V → ℕ, (∀ u v, M u v = M v u) →
      (∀ v, M v v = 0) → (∀ v, mdeg M v ≤ 4) → (∀ v, Even (mdeg M v)) →
      ∃ s₁ s₂ : V → V → ℕ, (∀ u v, M u v = s₁ u v + s₂ u v) ∧
        (∀ u v, s₁ u v = s₁ v u) ∧ (∀ u v, s₂ u v = s₂ v u) ∧
        (∀ v, mdeg s₁ v ≤ 2) ∧ (∀ v, mdeg s₂ v ≤ 2))
    (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  -- pair the odd-degree vertices
  obtain ⟨p, hsymp, hloopp, hdegp⟩ := exists_pairing
    (Finset.univ.filter fun v => Odd (mdeg m v))
    (even_card_odd_mdeg m hsym hloop)
  have hdegp' : ∀ v, mdeg p v = if Odd (mdeg m v) then 1 else 0 := by
    intro v
    rw [hdegp v]
    by_cases h : Odd (mdeg m v)
    · rw [if_pos (show v ∈ Finset.univ.filter (fun w => Odd (mdeg m w)) from
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩), if_pos h]
    · rw [if_neg (show v ∉ Finset.univ.filter (fun w => Odd (mdeg m w)) from
        fun hmem => h (Finset.mem_filter.mp hmem).2), if_neg h]
  -- the augmented matrix is even with degrees ≤ 4
  have hmdeg_add : ∀ v, mdeg (fun u w => m u w + p u w) v =
      mdeg m v + mdeg p v := by
    intro v; unfold mdeg; exact Finset.sum_add_distrib
  obtain ⟨s₁, s₂, hadd, hsym₁, hsym₂, hdeg₁, hdeg₂⟩ :=
    heven_split (fun u w => m u w + p u w)
      (fun u w => by dsimp only; rw [hsym u w, hsymp u w])
      (fun v => by dsimp only; rw [hloop v, hloopp v])
      (fun v => by
        rw [hmdeg_add v, hdegp' v]
        rcases Nat.even_or_odd (mdeg m v) with h | h
        · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
          have := hdeg v; omega
        · rw [if_pos h]
          obtain ⟨k, hk⟩ := h
          have := hdeg v; omega)
      (fun v => by
        rw [hmdeg_add v, hdegp' v]
        rcases Nat.even_or_odd (mdeg m v) with h | h
        · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
          obtain ⟨c, hc⟩ := h
          exact ⟨c, by omega⟩
        · rw [if_pos h]
          obtain ⟨k, hk⟩ := h
          exact ⟨k + 1, by omega⟩)
  exact two_split_restrict (fun u v => hadd u v) hsym hsymp hsym₁
    hdeg₁ hdeg₂

/-- **The Euler 2-split, CLOSED** (campaign C4; was
`proof_wanted exists_two_split` in `SMaj/Six/Shannon.lean`): every
loopless multigraph with Δ ≤ 4 splits into two spanning sub-multigraphs
of degree ≤ 2.  With `shannon_six_of_split_hypothesis` this closes
Shannon's bound at Δ = 4 (`shannon_six_of_maxDegree_four`,
`SMaj/Six/Targets.lean`) — the ≤ 6 proof's last open mathematical
input. -/
theorem exists_two_split (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) :=
  two_split_of_even_split_hypothesis
    (fun M hs hl hd he => exists_two_split_even M hs hl hd he)
    m hsym hloop hdeg

end

/-! ###### source file: SMaj/Six/Targets.lean ###### -/
section
/-
SMaj/Six/Targets.lean — case (b) rows (closed), Shannon at Δ = 4
(CLOSED, campaign C4), and the single named open obligation separating
the formalized core from the full unconditional T1 theorem
`Maj′(G) ≤ 6`:

1. `shannon_six_of_maxDegree_four` — Shannon's theorem at Δ = 4 for
   loopless multigraphs (χ′ ≤ ⌊3·4/2⌋ = 6), stated over a symmetric
   multiplicity matrix (mathlib has no multigraph edge-coloring theory:
   v4.30.0 and master both grep clean of Vizing/Shannon, checked
   2026-06-12; the `Graph α β` multigraph type has no degree API yet).
   **CLOSED (campaign C4, lens C4L3-lean-close, 2026-06-13)**: a THEOREM
   below, = `shannon_six_of_split_hypothesis` (`SMaj/Six/Shannon.lean`)
   applied to the closed Euler 2-split `exists_two_split`
   (`SMaj/Six/Euler.lean`, balanced orientations).  No open inputs.
2. `maj_le_six` — the headline: every admissible graph has a strong
   majority 6-edge-coloring (T1, strong form; proved on paper + machine,
   `lenses/L2-chain-grouping/WRITEUP.md`).  The remaining formal distance
   was the chain-decomposition glue (G1)–(G5); **its row-dispatch half is
   now CLOSED** (campaign C5, lens C5L3-lean-six, `SMaj/Six/Glue.lean`):
   `strongMajority_of_glue` dispatches every row of an admissible graph
   through `l1_row_le` / `twoChain_row_le` / `chainEnd_row_le` /
   `interior_row_le`, and `maj_le_six_of_glue` reduces this target to
   the construction half ONLY — exhibit, for every admissible G, a glue
   coloring (`IsGlueColoring`, 6 colors): build the contraction
   multigraph M from the chain decomposition, color it by
   `shannon_six_of_maxDegree_four`, transport to ports, fill interiors
   by `isFill_exists` (+ the pure-cycle construction).  No open external
   theorem input remains (and a fortiori at palette 7); what remains is
   construction formalization.

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12; Shannon closure
lens C4L3-lean-close (campaign C4), 2026-06-13.
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-- Case (b) of the ≤ 6 row analysis (l = 1 chains: junction–junction and
pendant rows): if neither endpoint has degree 2 and the coloring is rainbow
on a grouping with g ≤ ⌈d/4⌉ at both ends, the row is strong-majority
(Counting Lemma + R1/R2 via CRIT₄). -/
theorem l1_row_le {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u ≠ 2) (hdv : G.degree v ≠ 2)
    (hgu : groups G ix u ≤ hfun 4 (G.degree u))
    (hgv : groups G ix v ≤ hfun 4 (G.degree v)) (α : C) :
    nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2 := by
  have hcrit : Crit 4 (G.degree u) (G.degree v) :=
    crit4_of_ne_two ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
      ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩) hdu hdv
  calc nColor G c u v α
      ≤ groups G ix u + groups G ix v := counting_lemma hrb huv α
    _ ≤ hfun 4 (G.degree u) + hfun 4 (G.degree v) := Nat.add_le_add hgu hgv
    _ ≤ (G.degree u + G.degree v - 2) / 2 := hcrit

/-! ### The two named open obligations -/

/-- **Shannon's theorem at Δ = 4, CLOSED** (the (G3) step; formerly the
sole external mathematical input of the ≤ 6 proof — now a theorem with
no open inputs, campaign C4, lens C4L3-lean-close).  A loopless
multigraph is presented by its symmetric multiplicity matrix `m`
(m v v = 0); a proper 6-edge-coloring assigns each parallel class `{u,v}`
a set of `m u v` distinct colors (`φ u v`), classes at a common vertex
receiving disjoint sets.  Shannon 1949: χ′ ≤ ⌊3Δ/2⌋; at Δ ≤ 4 a 6-color
palette suffices.  Absent from mathlib v4.30.0 AND master (checked
2026-06-12).  Proof: `shannon_six_of_split_hypothesis`
(`SMaj/Six/Shannon.lean`) applied to the closed Euler 2-split
`exists_two_split` (`SMaj/Six/Euler.lean` — balanced orientations). -/
theorem shannon_six_of_maxDegree_four
    {V : Type*} [Fintype V] [DecidableEq V] (m : V → V → ℕ)
    (hsymm : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, ∑ u, m v u ≤ 4) :
    ∃ φ : V → V → Finset (Fin 6),
      (∀ u v, φ u v = φ v u) ∧
      (∀ u v, #(φ u v) = m u v) ∧
      (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w)) :=
  shannon_six_of_split_hypothesis
    (fun M hs hl hd => exists_two_split M hs hl hd) m hsymm hloop hdeg

/- **T1, strong form (the program headline)**: every admissible graph has
a strong majority 6-edge-coloring — `Maj′(G) ≤ 6` for every admissible G.
Formerly the `proof_wanted maj_le_six` of this file (campaigns C3–C8);
**CLOSED (campaign C9, lens C9L3-lean-assembly, 2026-07-08)**: now the
THEOREM `SMaj.maj_le_six` in `SMaj/Six/Final.lean`, via the completed
(G1)–(G5) construction `exists_isGlueColoring` composed with
`maj_le_six_of_glue` (`SMaj/Six/Glue.lean`).  No obligation remains
here. -/

end

/-! ###### source file: SMaj/Six/Glue.lean ###### -/
section
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

end

/-! ###### source file: SMaj/Six/ChainDecomp.lean ###### -/
section
/-
SMaj/Six/ChainDecomp.lean — chain-decomposition existence: the one
remaining mathematical stone of the `maj_le_six` lift (campaign C7,
lens C7L3-lean-chaindecomp, 2026-06-13; step 1 of the C6L3 WRITEUP
handoff).

`maj_le_six_of_glue` (campaign C5) reduced the headline to the
construction half; `shannon_six_indexed` + `exists_cycle_distance2`
(campaign C6) banked its coloring layer.  What the assembly still
consumes from the graph itself is the CHAIN DECOMPOSITION: every edge
lies on a piece — a trail threaded through degree-2 internal vertices,
which is either
* a CHAIN: both end degrees ≠ 2 (junction/pendant ends; x = y gives a
  loop chain, necessarily of length ≥ 3 in a simple graph), or
* a PURE CYCLE: closed with EVERY support vertex of degree 2 (length
  ≥ 3 likewise).

This file proves that existence statement for EVERY graph (no
admissibility needed), kernel-grade:
* `IsPiece` — the certificate bundle (nonempty + trail + internal
  degrees 2 + the end dichotomy);
* `exists_piece` — through every edge there is a piece (the maximal
  threaded-trail walker: extend at any degree-2 end with an unused
  edge; the parity dichotomy `end_eq_start_of_saturated` shows a
  saturated degree-2 end can only be the start, so maximal pieces
  classify);
* `IsPiece.three_le_length` — closed pieces (loop chains AND pure
  cycles) have ≥ 3 edges.

Machine pretest BEFORE proving (standing rule):
`lenses/C7L3-lean-chaindecomp/pretest_chaindecomp.py`, exit 0, re-run
fresh this session — P-A pins the slot-counting identity on 27,214
arbitrary walks; P-B the parity dichotomy at a saturated degree-2 end
(the exact E(z) = 2k_z − 1 odd-vs-≥2 contradiction shape); P-C the
walker's chain/cycle classification through every edge of the
EXHAUSTIVE 33,866 labeled graphs n ≤ 6 (251,085 edge classifications)
plus classics (C₉, theta, subdivided K₄, loop chain, disjoint union,
P₆) and 400 randoms n ≤ 14; P-D/P-E the linkage-closure and greedy
partition facts (NOT yet formalized here — see the honest-scope note
at the end of the file).
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Support bookkeeping for reversal and tails -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The internal vertices (support minus the two end positions) of the
reverse walk are those of the walk, reversed. -/
private lemma internal_reverse {x z : V} (p : G.Walk x z) :
    p.reverse.support.tail.dropLast = p.support.tail.dropLast.reverse := by
  rw [Walk.support_reverse, List.tail_reverse, List.dropLast_reverse,
    List.tail_dropLast]

omit [DecidableEq V] in
/-- If a walk's internal vertices and its END vertex all have degree 2,
then every support vertex except possibly the start has degree 2. -/
private lemma deg_two_of_mem_tail :
    ∀ {x z : V} (p : G.Walk x z), G.degree z = 2 →
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      ∀ v ∈ p.support.tail, G.degree v = 2 := by
  intro x z p
  induction p with
  | nil =>
    intro _ _ v hv
    simp at hv
  | cons h q ih =>
    intro hdz hint v hv
    rw [Walk.support_cons, List.tail_cons] at hv
    rw [Walk.support_cons, List.tail_cons] at hint
    cases q with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hdz
    | cons h' q' =>
      rw [Walk.support_cons] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · apply hint
        rw [Walk.support_cons,
          List.dropLast_cons_of_ne_nil q'.support_ne_nil]
        exact List.mem_cons_self ..
      · refine ih hdz ?_ v ?_
        · intro u hu
          rw [Walk.support_cons, List.tail_cons] at hu
          apply hint
          rw [Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_of_mem _ hu
        · rw [Walk.support_cons, List.tail_cons]
          exact hv'

/-! ### The parity dichotomy at a saturated end (pretest P-B) -/

/-- **Parity dichotomy**: if a trail ends at a degree-2 vertex `z` both
of whose incident edges already lie on the trail, the trail is closed
(`z` is its start).  Pretest P-B pins the numeric shape: the number of
trail edges at `z` is odd (2k_z − 1) for an open end but saturation
forces it to be exactly deg z = 2. -/
theorem end_eq_start_of_saturated {x z : V} {p : G.Walk x z}
    (ht : p.IsTrail) (hdz : G.degree z = 2)
    (hsat : ∀ f ∈ G.incidenceFinset z, f ∈ p.edges) : z = x := by
  have hcount : (p.edges.countP fun e => z ∈ e) = 2 := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (ht.edges_nodup.filter _),
      List.toFinset_filter, ← hdz, ← card_incidenceFinset_eq_degree]
    congr 1
    ext f
    simp only [Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq,
      mem_incidenceFinset]
    constructor
    · rintro ⟨hf, hzf⟩
      exact ⟨p.edges_subset_edgeSet hf, hzf⟩
    · intro hf
      exact ⟨hsat f (mem_incFinset.mpr hf), hf.2⟩
  by_contra hne
  have heven : Even (p.edges.countP fun e => z ∈ e) := by
    rw [hcount]
    exact ⟨1, rfl⟩
  obtain ⟨-, hzz⟩ :=
    (ht.even_countP_edges_iff z).mp heven fun h => hne h.symm
  exact hzz rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The trail-edge count at a vertex as a finset cardinality. -/
private lemma countP_edges_eq_card {x z : V} {p : G.Walk x z}
    (ht : p.IsTrail) (v : V) :
    (p.edges.countP fun e => v ∈ e) = #{f ∈ p.edges.toFinset | v ∈ f} := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (ht.edges_nodup.filter _),
    List.toFinset_filter]
  congr 1
  ext f
  simp [decide_eq_true_eq]

/-- The edges of a walk at a vertex `v` lie in `v`'s incidence finset. -/
private lemma filter_subset_incidence {x z : V} (p : G.Walk x z) (v : V) :
    {f ∈ p.edges.toFinset | v ∈ f} ⊆ G.incidenceFinset v := by
  intro f hf
  rw [Finset.mem_filter, List.mem_toFinset] at hf
  exact mem_incFinset.mpr ⟨p.edges_subset_edgeSet hf.1, hf.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every support vertex of a nonempty walk lies on one of its edges. -/
private lemma exists_edge_of_mem_support :
    ∀ {x z : V} (p : G.Walk x z), p.length ≠ 0 → ∀ v ∈ p.support,
      ∃ f ∈ p.edges, v ∈ f := by
  intro x z p
  induction p with
  | nil =>
    intro h
    simp at h
  | @cons a c d hadj q ih =>
    intro _ v hv
    rw [Walk.support_cons] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨s(v, c),
        by rw [Walk.edges_cons]; exact List.mem_cons_self ..,
        Sym2.mem_mk_left _ _⟩
    · cases q with
      | nil =>
        rw [Walk.support_nil, List.mem_singleton] at hv'
        subst hv'
        exact ⟨s(a, v),
          by rw [Walk.edges_cons]; exact List.mem_cons_self ..,
          Sym2.mem_mk_right _ _⟩
      | cons hadj' q' =>
        obtain ⟨f, hf, hvf⟩ := ih (by rw [Walk.length_cons]; omega) v hv'
        refine ⟨f, ?_, hvf⟩
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ hf

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every support vertex of a walk is the start, the end, or internal. -/
private lemma mem_support_cases :
    ∀ {x z : V} (p : G.Walk x z), ∀ v ∈ p.support,
      v = x ∨ v = z ∨ v ∈ p.support.tail.dropLast := by
  intro x z p
  induction p with
  | nil =>
    intro v hv
    rw [Walk.support_nil, List.mem_singleton] at hv
    exact Or.inl hv
  | cons h q ih =>
    intro v hv
    rw [Walk.support_cons] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Or.inl rfl
    · rcases ih v hv' with rfl | h' | h'
      · -- v is the head of the tail walk: internal unless the tail walk
        -- is trivial (then it is the end)
        cases q with
        | nil => exact Or.inr (Or.inl rfl)
        | cons hadj' q' =>
          right; right
          rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_self ..
      · exact Or.inr (Or.inl h')
      · right; right
        rw [Walk.support_cons, List.tail_cons]
        have hne : q.support.tail ≠ [] := by
          intro hnil
          rw [hnil] at h'
          simp at h'
        rw [← q.cons_tail_support,
          List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_of_mem _ h'

/-! ### Closed trails have length ≥ 3 (loop chains and pure cycles) -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A nonempty closed trail in a simple graph has at least 3 edges
(length 1 would be a loop, length 2 a repeated edge). -/
theorem three_le_length_of_closed {x : V} {p : G.Walk x x}
    (ht : p.IsTrail) (hne : p.length ≠ 0) : 3 ≤ p.length := by
  cases p with
  | nil => simp at hne
  | cons h q =>
    cases q with
    | nil => exact absurd rfl h.ne
    | cons h' q' =>
      cases q' with
      | nil =>
        exfalso
        rw [Walk.isTrail_def] at ht
        simp only [Walk.edges_cons, Walk.edges_nil, List.nodup_cons,
          List.mem_cons, List.not_mem_nil, or_false] at ht
        exact ht.1 Sym2.eq_swap
      | cons h'' q'' =>
        simp only [Walk.length_cons]
        omega

/-! ### The maximal threaded-trail walker (pretest P-C) -/

/-- One-sided maximal extension: any trail whose internal vertices have
degree 2 extends (through degree-2 ends, along unused edges — the
extension is FORCED, hence stays a trail with degree-2 internals) to
one that cannot be extended at its far end: either the far end is a
junction/pendant (degree ≠ 2) or all its incident edges are used.
Fuel-indexed recursion; a trail has at most #E(G) edges, so fuel
`#G.edgeFinset` always suffices. -/
private lemma exists_max_extension :
    ∀ (n : ℕ) (x z : V) (p : G.Walk x z), p.IsTrail →
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      #G.edgeFinset ≤ p.length + n →
      ∃ (y : V) (q : G.Walk x y), q.IsTrail ∧
        (∀ v ∈ q.support.tail.dropLast, G.degree v = 2) ∧
        (∀ f ∈ p.edges, f ∈ q.edges) ∧
        (G.degree y ≠ 2 ∨ ∀ f ∈ G.incidenceFinset y, f ∈ q.edges) := by
  intro n
  induction n with
  | zero =>
    -- out of fuel: the trail already carries every edge of G, so its
    -- end is saturated outright
    intro x z p ht hint hlen
    have hsub : p.edges.toFinset ⊆ G.edgeFinset := fun e he =>
      mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    have hcard : #G.edgeFinset ≤ #p.edges.toFinset := by
      rw [List.toFinset_card_of_nodup ht.edges_nodup, p.length_edges]
      omega
    have heq : p.edges.toFinset = G.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    refine ⟨z, p, ht, hint, fun f hf => hf, Or.inr fun f hf => ?_⟩
    have hfe : f ∈ G.edgeFinset :=
      mem_edgeFinset.mpr (mem_incFinset.mp hf).1
    rw [← heq] at hfe
    exact List.mem_toFinset.mp hfe
  | succ n ih =>
    intro x z p ht hint hlen
    by_cases hdz : G.degree z = 2
    · by_cases hsat : ∀ f ∈ G.incidenceFinset z, f ∈ p.edges
      · exact ⟨z, p, ht, hint, fun f hf => hf, Or.inr hsat⟩
      · -- forced extension along an unused edge at the degree-2 end
        push Not at hsat
        obtain ⟨f, hfz, hfp⟩ := hsat
        have hzf : z ∈ f := (mem_incFinset.mp hfz).2
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hzf
        have hzw : G.Adj z w :=
          G.mem_edgeSet.mp (mem_incFinset.mp hfz).1
        have ht' : (p.concat hzw).IsTrail := by
          rw [Walk.isTrail_def, Walk.edges_concat, List.concat_eq_append,
            List.nodup_append]
          refine ⟨ht.edges_nodup, List.nodup_singleton _, ?_⟩
          intro a ha c hc
          rw [List.mem_singleton] at hc
          subst hc
          exact fun heq => hfp (heq ▸ ha)
        have hint' : ∀ v ∈ (p.concat hzw).support.tail.dropLast,
            G.degree v = 2 := by
          intro v hv
          rw [Walk.support_concat, List.concat_eq_append, ← p.cons_tail_support,
            List.cons_append, List.tail_cons, List.dropLast_concat] at hv  -- pin-compat: v4.28 support_concat yields List.concat
          exact deg_two_of_mem_tail p hdz hint v hv
        obtain ⟨y, q, h1, h2, h3, h4⟩ := ih x w (p.concat hzw) ht' hint'
          (by rw [Walk.length_concat]; omega)
        refine ⟨y, q, h1, h2, fun f hf => h3 f ?_, h4⟩
        rw [Walk.edges_concat, List.concat_eq_append, List.mem_append]
        exact Or.inl hf
    · exact ⟨z, p, ht, hint, fun f hf => hf, Or.inl hdz⟩

/-! ### Pieces -/

variable (G) in
/-- **A piece of the chain decomposition**: a nonempty trail all of
whose internal vertices (the support with both end positions removed)
have degree 2, which is either a CHAIN (both end degrees ≠ 2 — the
case x = y is a loop chain) or a PURE CYCLE (closed, with every support
vertex of degree 2).  This is the LOCAL per-piece certificate used
toward the glue assembly (pure cycles = the `exists_cycle_distance2`
clients); the global partition/canonicality facts and the first/last
port-POSITION fact are separate obligations, still owed (see the
honest-scope note at the end of the file). -/
structure IsPiece {x y : V} (p : G.Walk x y) : Prop where
  ne : p.length ≠ 0
  trail : p.IsTrail
  internal : ∀ v ∈ p.support.tail.dropLast, G.degree v = 2
  ends : (G.degree x ≠ 2 ∧ G.degree y ≠ 2) ∨
    (x = y ∧ ∀ v ∈ p.support, G.degree v = 2)

omit [DecidableEq V] in
/-- Closed pieces — loop chains and pure cycles alike — have at least
3 edges. -/
theorem IsPiece.three_le_length {x : V} {p : G.Walk x x}
    (hp : IsPiece G p) : 3 ≤ p.length :=
  three_le_length_of_closed hp.trail hp.ne

/-- **Linkage closure** (pretest P-D): a piece is SATURATED at each of
its degree-2 support vertices — both incident edges of such a vertex lie
on the piece.  (The count of piece edges at `v` is even by the trail
parity lemma — `v` differs from both ends of a chain, and the cycle case
is closed — positive since `v` is on the walk, and at most deg v = 2.)
Consequently a piece's edge set is closed under "shares a degree-2
endpoint", the relation whose classes make the decomposition canonical:
this is the fill-independence input of the glue assembly. -/
theorem IsPiece.saturated_of_degree_two {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {v : V} (hv : v ∈ p.support)
    (hdv : G.degree v = 2) :
    ∀ f ∈ G.incidenceFinset v, f ∈ p.edges := by
  have hcc := countP_edges_eq_card hp.trail v
  have heven : Even (p.edges.countP fun e => v ∈ e) := by
    rw [hp.trail.even_countP_edges_iff v]
    intro hxy
    rcases hp.ends with ⟨hdx, hdy⟩ | ⟨heq, _⟩
    · exact ⟨fun h => hdx (h ▸ hdv), fun h => hdy (h ▸ hdv)⟩
    · exact absurd heq hxy
  have hpos : 0 < p.edges.countP fun e => v ∈ e := by
    obtain ⟨f, hf, hvf⟩ := exists_edge_of_mem_support p hp.ne v hv
    rw [List.countP_eq_length_filter]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hf, by simpa⟩)
  have hle : #{f ∈ p.edges.toFinset | v ∈ f} ≤ 2 := by
    have h1 := Finset.card_le_card (filter_subset_incidence p v)
    rwa [card_incidenceFinset_eq_degree, hdv] at h1
  have hcard : #{f ∈ p.edges.toFinset | v ∈ f} = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have heqf : {f ∈ p.edges.toFinset | v ∈ f} = G.incidenceFinset v :=
    Finset.eq_of_subset_of_card_le (filter_subset_incidence p v)
      (by rw [hcard, card_incidenceFinset_eq_degree, hdv])
  intro f hf
  rw [← heqf, Finset.mem_filter, List.mem_toFinset] at hf
  exact hf.1

omit [DecidableEq V] in
/-- **Ports** (handoff fact): a piece edge incident to a vertex of
degree ≠ 2 has that vertex as an END of the piece — at junctions, pieces
only ever START or STOP.  (Internal vertices have degree 2 by the piece
certificate.) -/
theorem IsPiece.end_of_junction {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {v : V}
    (hvf : v ∈ f) (hdv : G.degree v ≠ 2) : v = x ∨ v = y := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvf
  have hvs : v ∈ p.support := Walk.fst_mem_support_of_mem_edges p hf
  rcases mem_support_cases p v hvs with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hp.internal v h) hdv

/-! ### The existence theorem (the chain-decomposition stone) -/

/-- **Chain-decomposition existence** (pretest P-C): through every edge
of EVERY graph there is a piece — a maximal threaded trail that is a
chain (end degrees ≠ 2) or a pure cycle (closed, all degrees 2).  No
admissibility hypothesis is needed.  Proof: grow the one-edge trail at
both ends through degree-2 vertices along unused edges
(`exists_max_extension`); at a maximal degree-2 end every incident
edge is used, so the parity dichotomy `end_eq_start_of_saturated`
closes the walk, and the internal-degree invariant turns the closed
case into a pure cycle. -/
theorem exists_piece {a b : V} (hab : G.Adj a b) :
    ∃ (x y : V) (p : G.Walk x y), IsPiece G p ∧ s(a, b) ∈ p.edges := by
  classical
  -- the seed: the one-edge trail a — b
  have ht0 : (Walk.cons hab Walk.nil : G.Walk a b).IsTrail := by
    rw [Walk.isTrail_def]
    simp
  have hint0 : ∀ v ∈ (Walk.cons hab Walk.nil :
      G.Walk a b).support.tail.dropLast, G.degree v = 2 := by
    simp
  -- extend maximally at the b end
  obtain ⟨z, q, htq, hintq, hsubq, hmaxq⟩ :=
    exists_max_extension #G.edgeFinset a b (Walk.cons hab Walk.nil)
      ht0 hint0 (by omega)
  -- extend maximally at the a end (extend the reverse at its far end)
  have hintqr : ∀ v ∈ q.reverse.support.tail.dropLast,
      G.degree v = 2 := by
    intro v hv
    rw [internal_reverse, List.mem_reverse] at hv
    exact hintq v hv
  obtain ⟨y, r, htr, hintr, hsubr, hmaxr⟩ :=
    exists_max_extension #G.edgeFinset z a q.reverse htq.reverse hintqr
      (by omega)
  -- the piece is r.reverse : G.Walk y z
  have hmem : s(a, b) ∈ r.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    apply hsubr
    rw [Walk.edges_reverse, List.mem_reverse]
    apply hsubq
    simp
  have hintrr : ∀ v ∈ r.reverse.support.tail.dropLast,
      G.degree v = 2 := by
    intro v hv
    rw [internal_reverse, List.mem_reverse] at hv
    exact hintr v hv
  have hne : r.reverse.length ≠ 0 := by
    have h1 := List.length_pos_of_mem hmem
    rw [r.reverse.length_edges] at h1
    omega
  -- the z-end maximality certificate transfers from q to r.reverse
  have hmaxz : G.degree z ≠ 2 ∨
      ∀ f ∈ G.incidenceFinset z, f ∈ r.reverse.edges := by
    rcases hmaxq with h | h
    · exact Or.inl h
    · refine Or.inr fun f hf => ?_
      rw [Walk.edges_reverse, List.mem_reverse]
      apply hsubr
      rw [Walk.edges_reverse, List.mem_reverse]
      exact h f hf
  by_cases hdz : G.degree z = 2
  · -- saturated degree-2 end z: the walk is closed (z = y), and with
    -- both ends of degree 2 every support vertex has degree 2
    have hsatz : ∀ f ∈ G.incidenceFinset z, f ∈ r.reverse.edges := by
      rcases hmaxz with h | h
      · exact absurd hdz h
      · exact h
    have hzy : z = y := end_eq_start_of_saturated htr.reverse hdz hsatz
    refine ⟨y, z, r.reverse,
      ⟨hne, htr.reverse, hintrr, Or.inr ⟨hzy.symm, ?_⟩⟩, hmem⟩
    intro v hv
    rw [← r.reverse.cons_tail_support] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hzy ▸ hdz
    · exact deg_two_of_mem_tail r.reverse hdz hintrr v hv'
  · -- junction end z; the y end must be a junction too, else its
    -- saturation would close the walk onto z
    by_cases hdy : G.degree y = 2
    · exfalso
      rcases hmaxr with h | h
      · exact h hdy
      · exact hdz ((end_eq_start_of_saturated htr hdy h) ▸ hdy)
    · exact ⟨y, z, r.reverse,
        ⟨hne, htr.reverse, hintrr, Or.inl ⟨hdy, hdz⟩⟩, hmem⟩

/-! ### Honest scope note

Banked here: piece EXISTENCE through every edge (the maximal walker,
pretest P-C) with the end dichotomy and the closed-length bound — the
"one remaining mathematical stone" of the C6L3 handoff, step 1.  NOT
yet formalized (still owed to the assembly, pretests P-D/P-E):
linkage-closure (a piece's edge set is exactly the degree-2-linkage
class of any of its edges, making the decomposition canonical as a
partition) and the port-position fact (an edge of a piece at a
degree-≠ 2 vertex is the piece's first or last edge).  `maj_le_six`
remains `proof_wanted`. -/

end

/-! ###### source file: SMaj/Six/Partition.lean ###### -/
section
/-
SMaj/Six/Partition.lean — the partition/canonicality half of the chain
decomposition and the port-POSITION calculus (campaign C8, lens
C8L3-lean-assembly, 2026-06-13; step 1 of the C7L3 WRITEUP handoff).

`SMaj/Six/ChainDecomp.lean` (campaign C7) banked piece EXISTENCE through
every edge (`exists_piece`) with the linkage-closure fact
(`IsPiece.saturated_of_degree_two`) and the weak port fact
(`IsPiece.end_of_junction`).  What the glue assembly additionally
consumes from the decomposition — and what this file closes — is:

* **the partition facts** (pretest P-E, now Q-E): the linkage relation
  `Linked` (reflexive-transitive closure of "two edges of G sharing a
  degree-2 vertex") is an equivalence (`linkSetoid`), a piece's edge set
  is CLOSED under it (`IsPiece.mem_of_linked`), any two edges of a piece
  are linked (`IsPiece.linked_of_mem`), hence a piece's edge set IS the
  linkage class of any of its edges (`IsPiece.mem_edges_iff_linked`)
  and any two pieces sharing an edge have EQUAL edge sets
  (`IsPiece.edges_toFinset_eq`) — the chain decomposition is canonical
  as a partition, and a choice of piece per linkage class is consistent;

* **the port-POSITION fact** (`IsPiece.eq_first_or_last`, strengthening
  `end_of_junction`): a piece edge incident to a degree-≠ 2 vertex `v`
  IS the first edge `s(x, p.snd)` (with `v = x`) or the last edge
  `s(p.penultimate, y)` (with `v = y`) — by VALUE, which under the
  trail's `edges_nodup` pins its list position.  This is what lets the
  assembly transport the Shannon color of an M-half to its port edge;

* **the slot calculus** for the `interior`/`chain_end` fields:
  `eq_or_eq_of_mem_edges_degree_two` (a walk carries ≤ deg v = 2 edges
  at `v`; two distinct ones exhaust them), the second-edge facts
  `IsPiece.edges_one_eq` / `IsPiece.edges_length_sub_two_eq` (the edge
  after a port is `s(p.snd, z)` at slot 1, resp. `s(p.penultimate, z)`
  at slot L − 2), and the other-edge slot lemmas
  `IsPiece.other_edge_slot_of_chain` (slots i − 1 / i + 1) and
  `IsPiece.other_edge_slot_of_cycle` (modular slots (i + L − 1) % L /
  (i + 1) % L) — exactly the index arithmetic of the fill's distance-2
  guarantee and of the pure-cycle pattern `exists_cycle_distance2`.

Machine pretest BEFORE proving (standing rule):
`lenses/C8L3-lean-assembly/pretest_partition.py`, exit 0 — Q-A..Q-F
model-check the intended statement semantics above on the maximal
walker's pieces (510,046 piece checks: EXHAUSTIVE all labeled graphs
n ≤ 6, both orientations of every edge, classics, 300 randoms n ≤ 14;
the Lean lemmas quantify over arbitrary `IsPiece` witnesses — strictly
more general than the walker-generated corpus; foil caveat S4).

Still owed to the assembly after this file (honest scope): steps 2–5 of
the C6L3 handoff — the piece CHOICE per linkage class, sites/`ix`, the
M-family `t`, the `shannon_six_indexed` instantiation, fills, and the
`IsGlueColoring` bundle.  `maj_le_six` remains `proof_wanted`.
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Position foundation: edges by index -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `i`-th edge of a walk joins its `i`-th and `(i+1)`-st vertices
(pretest Q-A). -/
lemma edges_getElem {x y : V} (p : G.Walk x y) {i : ℕ}
    (hi : i < p.edges.length) :
    p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
  have hd : i < p.darts.length := by
    rw [Walk.length_darts]
    rwa [p.length_edges] at hi
  have h1 : p.edges[i] = (p.darts[i]'hd).edge := by
    show (p.darts.map Dart.edge)[i]'(by rwa [List.length_map]) = _
    rw [List.getElem_map]
  rw [h1, Walk.darts_getElem_eq_getVert i hd]
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex at a position strictly between the ends is internal (lies in
`support.tail.dropLast`). -/
lemma getVert_mem_internal {x y : V} (p : G.Walk x y) {n : ℕ}
    (h0 : 0 < n) (hn : n < p.length) :
    p.getVert n ∈ p.support.tail.dropLast := by
  have hlen : p.support.tail.dropLast.length = p.length - 1 := by
    rw [List.length_dropLast, List.length_tail, Walk.length_support]
    omega
  have hidx : n - 1 < p.support.tail.dropLast.length := by omega
  have hval : p.support.tail.dropLast[n - 1] = p.getVert n := by
    have h1 : p.getVert (n - 1 + 1) = p.getVert n := by
      rw [show n - 1 + 1 = n by omega]
    rw [← h1,
      p.getVert_eq_support_getElem (by omega : n - 1 + 1 ≤ p.length)]
    simp only [List.getElem_dropLast, List.getElem_tail]
  rw [← hval]
  exact List.getElem_mem hidx

/-! ### The port-POSITION fact (pretest Q-B) -/

omit [DecidableEq V] in
/-- **Port position** (strengthens `IsPiece.end_of_junction`): a piece
edge incident to a vertex of degree ≠ 2 is the FIRST edge `s(x, p.snd)`
(and the vertex is the start) or the LAST edge `s(p.penultimate, y)`
(and the vertex is the end).  Under `edges_nodup` this pins the edge's
list position to 0 resp. length − 1: at junctions, ports sit exactly at
the two outer slots. -/
theorem IsPiece.eq_first_or_last {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {v : V}
    (hvf : v ∈ f) (hdv : G.degree v ≠ 2) :
    (v = x ∧ f = s(x, p.snd)) ∨ (v = y ∧ f = s(p.penultimate, y)) := by
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem hf
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hfeq : f = s(p.getVert i, p.getVert (i + 1)) := by
    rw [← hfi, edges_getElem p hi]
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hfeq] at hvf
    exact Sym2.mem_iff.mp hvf
  rcases hv' with hv | hv
  · -- v sits at position i: i = 0 or v is internal (degree 2)
    have hi0 : i = 0 := by
      by_contra h0
      exact hdv (hp.internal v
        (by rw [hv]; exact getVert_mem_internal p (by omega) hil))
    subst hi0
    refine Or.inl ⟨by rw [hv, Walk.getVert_zero], ?_⟩
    rw [hfeq, Walk.getVert_zero]
  · -- v sits at position i + 1: i + 1 = length or internal
    have hiL : i + 1 = p.length := by
      by_contra hL
      exact hdv (hp.internal v
        (by rw [hv]; exact getVert_mem_internal p (by omega) (by omega)))
    refine Or.inr ⟨by rw [hv, hiL, Walk.getVert_length], ?_⟩
    rw [hfeq]
    have h1 : p.getVert i = p.penultimate := by
      show p.getVert i = p.getVert (p.length - 1)
      rw [show p.length - 1 = i by omega]
    have h2 : p.getVert (i + 1) = y := by rw [hiL, Walk.getVert_length]
    rw [h1, h2]

/-! ### The linkage relation (pretest Q-E) -/

variable (G) in
/-- One linkage step: two edges of `G` sharing a degree-2 vertex. -/
def LinkStep (f g : Sym2 V) : Prop :=
  f ∈ G.edgeSet ∧ g ∈ G.edgeSet ∧ ∃ v : V, G.degree v = 2 ∧ v ∈ f ∧ v ∈ g

variable (G) in
/-- The linkage relation: the reflexive-transitive closure of `LinkStep`.
Its classes on `G.edgeFinset` are exactly the edge sets of the chain
decomposition (`IsPiece.mem_edges_iff_linked` below). -/
def Linked : Sym2 V → Sym2 V → Prop := Relation.ReflTransGen (LinkStep G)

omit [DecidableEq V] in
lemma LinkStep.symm {f g : Sym2 V} (h : LinkStep G f g) : LinkStep G g f := by
  obtain ⟨hf, hg, v, hdv, hvf, hvg⟩ := h
  exact ⟨hg, hf, v, hdv, hvg, hvf⟩

omit [DecidableEq V] in
lemma Linked.refl (f : Sym2 V) : Linked G f f := Relation.ReflTransGen.refl

omit [DecidableEq V] in
lemma Linked.symm {f g : Sym2 V} (h : Linked G f g) : Linked G g f :=
  Relation.ReflTransGen.symmetric (fun _ _ hs => hs.symm) h

omit [DecidableEq V] in
lemma Linked.trans {f g h : Sym2 V} (h₁ : Linked G f g) (h₂ : Linked G g h) :
    Linked G f h := Relation.ReflTransGen.trans h₁ h₂

variable (G) in
/-- Linkage as a setoid on `Sym2 V` (non-edges are isolated points): the
quotient indexes the pieces of the chain decomposition, and
`Quotient.out` gives the assembly its canonical representative per
class. -/
def linkSetoid : Setoid (Sym2 V) :=
  ⟨Linked G, ⟨Linked.refl, Linked.symm, Linked.trans⟩⟩

omit [DecidableEq V] in
/-- Linkage stays inside the edge set. -/
lemma Linked.mem_edgeSet {f g : Sym2 V} (h : Linked G f g)
    (hf : f ∈ G.edgeSet) : g ∈ G.edgeSet := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hstep⟩
  · exact hf
  · exact hstep.2.1

/-! ### Closure: a piece's edge set absorbs linkage -/

/-- **Linkage closure of a piece** (pretest Q-E, closure half): an edge
linked to a piece edge is itself a piece edge.  (Each step shares a
degree-2 vertex with an edge already on the piece, and the piece is
saturated there by `IsPiece.saturated_of_degree_two`.) -/
theorem IsPiece.mem_of_linked {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f g : Sym2 V} (hf : f ∈ p.edges)
    (h : Linked G f g) : g ∈ p.edges := by
  induction h with
  | refl => exact hf
  | @tail b c _ hstep ih =>
    obtain ⟨-, hc, v, hdv, hvb, hvc⟩ := hstep
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvb
    have hvs : v ∈ p.support := Walk.fst_mem_support_of_mem_edges p ih
    exact hp.saturated_of_degree_two hvs hdv c (mem_incFinset.mpr ⟨hc, hvc⟩)

/-! ### Connectivity: all edges of a piece are linked -/

omit [DecidableEq V] in
/-- Along a walk with degree-2 internals, every edge is linked to the
first edge (consecutive walk edges share an internal vertex). -/
private lemma linked_first_of_mem :
    ∀ {x z : V} (p : G.Walk x z),
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      ∀ f ∈ p.edges, Linked G s(x, p.snd) f := by
  intro x z p
  induction p with
  | nil =>
    intro _ f hf
    simp at hf
  | @cons a b c hadj q ih =>
    intro hint f hf
    rw [Walk.edges_cons] at hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · rw [Walk.snd_cons]
      exact Relation.ReflTransGen.refl
    · cases q with
      | nil => simp at hf'
      | @cons _ b' _ hadj' q' =>
        have hintq : ∀ v ∈ (Walk.cons hadj' q').support.tail.dropLast,
            G.degree v = 2 := by
          intro v hv
          apply hint
          rw [Walk.support_cons, List.tail_cons]
          rw [← List.tail_dropLast] at hv
          exact List.mem_of_mem_tail hv
        have hdb : G.degree b = 2 := by
          apply hint
          rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_self ..
        have hstep : LinkStep G
            s(a, (Walk.cons hadj (Walk.cons hadj' q')).snd)
            s(b, (Walk.cons hadj' q').snd) := by
          rw [Walk.snd_cons, Walk.snd_cons]
          exact ⟨G.mem_edgeSet.mpr hadj, G.mem_edgeSet.mpr hadj', b, hdb,
            Sym2.mem_mk_right a b, Sym2.mem_mk_left b b'⟩
        exact Relation.ReflTransGen.head hstep (ih hintq f hf')

omit [DecidableEq V] in
/-- **Piece connectivity** (pretest Q-E, connectivity half): any two
edges of a piece are linked. -/
theorem IsPiece.linked_of_mem {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f g : Sym2 V} (hf : f ∈ p.edges)
    (hg : g ∈ p.edges) : Linked G f g :=
  (linked_first_of_mem p hp.internal f hf).symm.trans
    (linked_first_of_mem p hp.internal g hg)

/-! ### The partition facts: canonical classes and uniqueness -/

/-- **The canonical-partition fact** (pretest Q-E): a piece's edge set is
exactly the linkage class of any of its edges (membership form, no
decidability needed).  The chain decomposition is therefore canonical:
pieces are indexed by the classes of `linkSetoid` on the edge set,
independent of how the walks were grown. -/
theorem IsPiece.mem_edges_iff_linked {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {g : Sym2 V} :
    g ∈ p.edges ↔ g ∈ G.edgeSet ∧ Linked G f g := by
  constructor
  · intro hg
    exact ⟨p.edges_subset_edgeSet hg, hp.linked_of_mem hf hg⟩
  · rintro ⟨-, hlink⟩
    exact hp.mem_of_linked hf hlink

/-- Membership form of the uniqueness fact: two pieces through a common
edge carry exactly the same edges. -/
theorem IsPiece.mem_edges_iff {x y x' y' : V} {p : G.Walk x y}
    {q : G.Walk x' y'} (hp : IsPiece G p) (hq : IsPiece G q) {f : Sym2 V}
    (hf : f ∈ p.edges) (hf' : f ∈ q.edges) {g : Sym2 V} :
    g ∈ p.edges ↔ g ∈ q.edges := by
  rw [hp.mem_edges_iff_linked hf, hq.mem_edges_iff_linked hf']

/-- **Piece edge-set uniqueness** (pretest Q-E, the C8 charter item): two
pieces through a common edge have EQUAL edge sets — the choice of piece
per linkage class is consistent, whatever walks the walker grew. -/
theorem IsPiece.edges_toFinset_eq {x y x' y' : V} {p : G.Walk x y}
    {q : G.Walk x' y'} (hp : IsPiece G p) (hq : IsPiece G q) {f : Sym2 V}
    (hf : f ∈ p.edges) (hf' : f ∈ q.edges) :
    p.edges.toFinset = q.edges.toFinset := by
  ext g
  rw [List.mem_toFinset, List.mem_toFinset]
  exact hp.mem_edges_iff hq hf hf'

/-! ### The slot calculus (pretests Q-C, Q-D, Q-F) -/

/-- **The pair fact** (pretest Q-C): a walk carries at most
`deg v = 2` edges at `v`, so two DISTINCT walk edges at `v` exhaust
them: any walk edge at `v` is one of the two. -/
lemma eq_or_eq_of_mem_edges_degree_two {x y : V} {p : G.Walk x y} {v : V}
    (hdv : G.degree v = 2) {e₁ e₂ : Sym2 V} (h₁ : e₁ ∈ p.edges)
    (h₂ : e₂ ∈ p.edges) (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) (hne : e₁ ≠ e₂)
    {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f) : f = e₁ ∨ f = e₂ := by
  have hsub : {g ∈ p.edges.toFinset | v ∈ g} ⊆ G.incidenceFinset v := by
    intro g hg
    rw [Finset.mem_filter, List.mem_toFinset] at hg
    exact mem_incFinset.mpr ⟨p.edges_subset_edgeSet hg.1, hg.2⟩
  have hcard : #{g ∈ p.edges.toFinset | v ∈ g} ≤ 2 := by
    have h := Finset.card_le_card hsub
    rwa [card_incidenceFinset_eq_degree, hdv] at h
  have hpsub : ({e₁, e₂} : Finset (Sym2 V)) ⊆
      {g ∈ p.edges.toFinset | v ∈ g} := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h₁, hv₁⟩
    · rw [Finset.mem_singleton] at hg
      subst hg
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h₂, hv₂⟩
  have heq : ({e₁, e₂} : Finset (Sym2 V)) =
      {g ∈ p.edges.toFinset | v ∈ g} :=
    Finset.eq_of_subset_of_card_le hpsub
      (by rw [Finset.card_pair hne]; exact hcard)
  have hfm : f ∈ ({e₁, e₂} : Finset (Sym2 V)) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hf, hvf⟩
  simpa using hfm

omit [DecidableEq V] in
/-- A piece whose start is no degree-2 vertex but whose second vertex is
has length ≥ 2 (a one-edge piece would make the second vertex an end). -/
theorem IsPiece.two_le_length_of_snd {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdw : G.degree p.snd = 2) :
    2 ≤ p.length := by
  rcases hp.ends with ⟨-, hdy⟩ | ⟨-, hall⟩
  · by_contra h
    have h1 : p.length = 1 := by
      have := hp.ne
      omega
    have hsy : p.snd = y := by
      show p.getVert 1 = y
      rw [← h1]
      exact p.getVert_length
    exact hdy (hsy ▸ hdw)
  · exact absurd (hall x p.start_mem_support) hdx

omit [DecidableEq V] in
/-- Mirror of `two_le_length_of_snd` at the far end. -/
theorem IsPiece.two_le_length_of_penultimate {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdy : G.degree y ≠ 2)
    (hdw : G.degree p.penultimate = 2) : 2 ≤ p.length := by
  rcases hp.ends with ⟨hdx, -⟩ | ⟨-, hall⟩
  · by_contra h
    have h1 : p.length = 1 := by
      have := hp.ne
      omega
    have hsx : p.penultimate = x := by
      show p.getVert (p.length - 1) = x
      rw [h1]
      exact p.getVert_zero
    exact hdx (hsx ▸ hdw)
  · exact absurd (hall y p.end_mem_support) hdy

/-- **The second-edge fact** (pretest Q-D): on a piece whose start `x` is
a junction/pendant and whose second vertex `w := p.snd` is internal
(degree 2), the edge after the port to the OTHER neighbor `z ≠ x` of `w`
is exactly slot 1: `p.edges[1] = s(p.snd, z)`.  This is where the
`chain_end` field's inward edge lives. -/
theorem IsPiece.edges_one_eq {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdw : G.degree p.snd = 2)
    {z : V} (hz : G.Adj p.snd z) (hzx : z ≠ x) :
    ∃ h : 1 < p.edges.length, p.edges[1] = s(p.snd, z) := by
  have hlen : 2 ≤ p.length := hp.two_le_length_of_snd hdx hdw
  have h1 : 1 < p.edges.length := by
    rw [p.length_edges]
    omega
  have h0 : 0 < p.edges.length := by omega
  refine ⟨h1, ?_⟩
  have he0 : p.edges[0] = s(x, p.snd) := by
    rw [edges_getElem p h0, Walk.getVert_zero]
  have he1 : p.edges[1] = s(p.getVert 1, p.getVert 2) := edges_getElem p h1
  have hne : p.edges[0] ≠ p.edges[1] := fun h =>
    absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
  have hmem : s(p.snd, z) ∈ p.edges := by
    apply hp.saturated_of_degree_two (p.getVert_mem_support 1) hdw
    exact mem_incFinset.mpr
      ⟨G.mem_edgeSet.mpr hz, Sym2.mem_mk_left p.snd z⟩
  rcases eq_or_eq_of_mem_edges_degree_two hdw (List.getElem_mem h0)
      (List.getElem_mem h1)
      (by rw [he0]; exact Sym2.mem_mk_right x p.snd)
      (by rw [he1]; exact Sym2.mem_mk_left _ _)
      hne hmem (Sym2.mem_mk_left p.snd z) with h | h
  · exfalso
    rw [he0] at h
    rcases Sym2.eq_iff.mp h with ⟨h1', -⟩ | ⟨-, h2'⟩
    · exact hdx (h1' ▸ hdw)
    · exact hzx h2'
  · exact h.symm

/-- Mirror of `edges_one_eq` at the far end: the edge before the last
port is slot `length − 2`: `p.edges[p.edges.length − 2] =
s(p.penultimate, z)` for the other neighbor `z ≠ y` of the penultimate
vertex. -/
theorem IsPiece.edges_length_sub_two_eq {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdy : G.degree y ≠ 2)
    (hdw : G.degree p.penultimate = 2) {z : V}
    (hz : G.Adj p.penultimate z) (hzy : z ≠ y) :
    ∃ h : p.edges.length - 2 < p.edges.length,
      p.edges[p.edges.length - 2] = s(p.penultimate, z) := by
  have hlen : 2 ≤ p.length := hp.two_le_length_of_penultimate hdy hdw
  have hL : p.edges.length = p.length := p.length_edges
  have hsub : p.edges.length - 2 < p.edges.length := by omega
  have hlast : p.edges.length - 1 < p.edges.length := by omega
  refine ⟨hsub, ?_⟩
  have helast : p.edges[p.edges.length - 1] = s(p.penultimate, y) := by
    rw [edges_getElem p hlast, hL,
      show p.length - 1 + 1 = p.length by omega, p.getVert_length]
  have hesub : p.edges[p.edges.length - 2] =
      s(p.getVert (p.length - 2), p.penultimate) := by
    rw [edges_getElem p hsub, hL,
      show p.length - 2 + 1 = p.length - 1 by omega]
  have hne : p.edges[p.edges.length - 1] ≠ p.edges[p.edges.length - 2] :=
    fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
  have hpen : p.penultimate ∈ p.support := p.getVert_mem_support _
  have hmem : s(p.penultimate, z) ∈ p.edges := by
    apply hp.saturated_of_degree_two hpen hdw
    exact mem_incFinset.mpr
      ⟨G.mem_edgeSet.mpr hz, Sym2.mem_mk_left p.penultimate z⟩
  rcases eq_or_eq_of_mem_edges_degree_two hdw (List.getElem_mem hlast)
      (List.getElem_mem hsub)
      (by rw [helast]; exact Sym2.mem_mk_left _ _)
      (by rw [hesub]; exact Sym2.mem_mk_right _ _)
      hne hmem (Sym2.mem_mk_left p.penultimate z) with h | h
  · exfalso
    rw [helast] at h
    rcases Sym2.eq_iff.mp h with ⟨-, h2'⟩ | ⟨h1', -⟩
    · exact hzy h2'
    · exact hdy (h1' ▸ hdw)
  · exact h.symm

/-- **Chain slot lemma** (pretest Q-F): on a CHAIN piece (both end
degrees ≠ 2), the other piece edge at a degree-2 endpoint `v` of
`p.edges[i]` sits at slot `i − 1` (if `v` is the near vertex) or `i + 1`
(if `v` is the far vertex) — the index arithmetic consumed by the fill's
distance-2 guarantee on `interior` rows. -/
theorem IsPiece.other_edge_slot_of_chain {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) (hdx : G.degree x ≠ 2) (hdy : G.degree y ≠ 2)
    {i : ℕ} (hi : i < p.edges.length) {v : V} (hv : v ∈ p.edges[i])
    (hdv : G.degree v = 2) {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f)
    (hne : f ≠ p.edges[i]) :
    (v = p.getVert i ∧ 0 < i ∧
      ∃ h : i - 1 < p.edges.length, f = p.edges[i - 1]) ∨
    (v = p.getVert (i + 1) ∧
      ∃ h : i + 1 < p.edges.length, f = p.edges[i + 1]) := by
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hei : p.edges[i] = s(p.getVert i, p.getVert (i + 1)) :=
    edges_getElem p hi
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hei] at hv
    exact Sym2.mem_iff.mp hv
  rcases hv' with hveq | hveq
  · -- near vertex: i ≥ 1 since position 0 is the start x (degree ≠ 2)
    have h0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exact absurd (by rw [hveq, Walk.getVert_zero] at hdv; exact hdv) hdx
      · exact h
    have hprevlt : i - 1 < p.edges.length := by omega
    have heprev : p.edges[i - 1] = s(p.getVert (i - 1), p.getVert i) := by
      rw [edges_getElem p hprevlt, show i - 1 + 1 = i by omega]
    have hneprev : p.edges[i] ≠ p.edges[i - 1] := fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
    rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
        (List.getElem_mem hprevlt)
        (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
        (by rw [heprev, hveq]; exact Sym2.mem_mk_right _ _)
        hneprev hf hvf with h | h
    · exact absurd h hne
    · exact Or.inl ⟨hveq, h0, hprevlt, h⟩
  · -- far vertex: i + 1 ≤ length − 1 since position length is y
    have hL : i + 1 < p.length := by
      rcases Nat.lt_or_ge (i + 1) p.length with h | h
      · exact h
      · exfalso
        have hiL : i + 1 = p.length := by omega
        rw [hveq, hiL, Walk.getVert_length] at hdv
        exact hdy hdv
    have hnextlt : i + 1 < p.edges.length := by
      rw [p.length_edges]
      exact hL
    have henext : p.edges[i + 1] =
        s(p.getVert (i + 1), p.getVert (i + 2)) := edges_getElem p hnextlt
    have hnenext : p.edges[i] ≠ p.edges[i + 1] := fun h =>
      absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
    rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
        (List.getElem_mem hnextlt)
        (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
        (by rw [henext, hveq]; exact Sym2.mem_mk_left _ _)
        hnenext hf hvf with h | h
    · exact absurd h hne
    · exact Or.inr ⟨hveq, hnextlt, h⟩

/-- **Cycle slot lemma** (pretest Q-F): on a CLOSED piece all of whose
support vertices have degree 2 (a pure cycle), the other piece edge at a
vertex `v` of `p.edges[i]` sits at the MODULAR slot `(i + L − 1) % L`
(near vertex) or `(i + 1) % L` (far vertex), `L := p.edges.length` —
the wraparound arithmetic consumed by `exists_cycle_distance2` on
`interior` rows of pure cycles. -/
theorem IsPiece.other_edge_slot_of_cycle {x : V} {p : G.Walk x x}
    (hp : IsPiece G p) (hall : ∀ v ∈ p.support, G.degree v = 2)
    {i : ℕ} (hi : i < p.edges.length) {v : V} (hv : v ∈ p.edges[i])
    {f : Sym2 V} (hf : f ∈ p.edges) (hvf : v ∈ f)
    (hne : f ≠ p.edges[i]) :
    (v = p.getVert i ∧
      ∃ h : (i + p.edges.length - 1) % p.edges.length < p.edges.length,
        f = p.edges[(i + p.edges.length - 1) % p.edges.length]) ∨
    (v = p.getVert (i + 1) ∧
      ∃ h : (i + 1) % p.edges.length < p.edges.length,
        f = p.edges[(i + 1) % p.edges.length]) := by
  have h3 : 3 ≤ p.length := hp.three_le_length
  have hL : p.edges.length = p.length := p.length_edges
  have hil : i < p.length := by rwa [p.length_edges] at hi
  have hei : p.edges[i] = s(p.getVert i, p.getVert (i + 1)) :=
    edges_getElem p hi
  have hdv : G.degree v = 2 := by
    apply hall
    rw [hei] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact p.getVert_mem_support i
    · exact p.getVert_mem_support (i + 1)
  have hv' : v = p.getVert i ∨ v = p.getVert (i + 1) := by
    rw [hei] at hv
    exact Sym2.mem_iff.mp hv
  rcases hv' with hveq | hveq
  · -- near vertex: previous slot, wrapping at i = 0
    left
    refine ⟨hveq, ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · -- wrap: the other edge at the basepoint is the last edge
      have hmod : (0 + p.edges.length - 1) % p.edges.length =
          p.edges.length - 1 := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      refine ⟨by omega, ?_⟩
      have hlastlt : p.edges.length - 1 < p.edges.length := by omega
      have helast : p.edges[p.edges.length - 1] =
          s(p.getVert (p.length - 1), x) := by
        rw [edges_getElem p hlastlt, hL,
          show p.length - 1 + 1 = p.length by omega, p.getVert_length]
      have hnelast : p.edges[0] ≠ p.edges[p.edges.length - 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hlastlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
          (by rw [helast, hveq, Walk.getVert_zero]
              exact Sym2.mem_mk_right _ _)
          hnelast hf hvf with h | h
      · exact absurd h hne
      · exact h
    · -- interior: the previous slot, no wrap
      have hmod : (i + p.edges.length - 1) % p.edges.length = i - 1 := by
        rw [show i + p.edges.length - 1 = p.edges.length + (i - 1) by omega,
          Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have hprevlt : i - 1 < p.edges.length := by omega
      refine ⟨hprevlt, ?_⟩
      have heprev : p.edges[i - 1] =
          s(p.getVert (i - 1), p.getVert i) := by
        rw [edges_getElem p hprevlt, show i - 1 + 1 = i by omega]
      have hneprev : p.edges[i] ≠ p.edges[i - 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hprevlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_left _ _)
          (by rw [heprev, hveq]; exact Sym2.mem_mk_right _ _)
          hneprev hf hvf with h | h
      · exact absurd h hne
      · exact h
  · -- far vertex: next slot, wrapping at i + 1 = length
    right
    refine ⟨hveq, ?_⟩
    rcases Nat.lt_or_ge (i + 1) p.edges.length with hlt | hge
    · -- interior: the next slot, no wrap
      have hmod : (i + 1) % p.edges.length = i + 1 := Nat.mod_eq_of_lt hlt
      rw [hmod]
      refine ⟨hlt, ?_⟩
      have henext : p.edges[i + 1] =
          s(p.getVert (i + 1), p.getVert (i + 2)) := edges_getElem p hlt
      have hnenext : p.edges[i] ≠ p.edges[i + 1] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem hlt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
          (by rw [henext, hveq]; exact Sym2.mem_mk_left _ _)
          hnenext hf hvf with h | h
      · exact absurd h hne
      · exact h
    · -- wrap: the other edge at the basepoint is the first edge
      have hiL : i + 1 = p.edges.length := by omega
      have hmod : (i + 1) % p.edges.length = 0 := by
        rw [hiL, Nat.mod_self]
      rw [hmod]
      have h0lt : 0 < p.edges.length := by omega
      refine ⟨h0lt, ?_⟩
      have he0 : p.edges[0] = s(x, p.getVert 1) := by
        rw [edges_getElem p h0lt, Walk.getVert_zero]
      have hne0 : p.edges[i] ≠ p.edges[0] := fun h =>
        absurd ((hp.trail.edges_nodup.getElem_inj_iff).mp h) (by omega)
      rcases eq_or_eq_of_mem_edges_degree_two hdv (List.getElem_mem hi)
          (List.getElem_mem h0lt)
          (by rw [hei, hveq]; exact Sym2.mem_mk_right _ _)
          (by rw [he0, hveq, show i + 1 = p.length by omega,
                p.getVert_length]
              exact Sym2.mem_mk_left _ _)
          hne0 hf hvf with h | h
      · exact absurd h hne
      · exact h

/-! ### Honest scope note

Banked here: the partition/canonicality facts (linkage equivalence,
closure, connectivity, canonical classes, edge-set uniqueness), the
port-POSITION fact, and the slot calculus (pair fact, second-edge facts,
chain/cycle other-edge slots) — step 1 of the C7L3 handoff in full.
NOT yet formalized (steps 2–5, still owed): the piece CHOICE per linkage
class, sites/`ix`, the M-family `t : ι → Sym2 N`, the
`shannon_six_indexed` instantiation, the fills, and the `IsGlueColoring`
bundle.  `maj_le_six` remains `proof_wanted`. -/

end

/-! ###### source file: SMaj/Six/Construct.lean ###### -/
section
/-
SMaj/Six/Construct.lean — construction-half bricks for the (G1)–(G5) glue
(campaign C6, lens C6L3-lean-construction, 2026-06-13).

`maj_le_six_of_glue` (SMaj/Six/Glue.lean, campaign C5) reduced the
headline `maj_le_six` to the CONSTRUCTION half only: exhibit, for every
admissible G, a 6-color `IsGlueColoring` (chain decomposition →
contraction multigraph M → `shannon_six_of_maxDegree_four` → port
transport → `isFill_exists`).  This file banks the two construction-layer
steps that are independent of the chain decomposition itself:

* `shannon_six_indexed` — step (G3) in the form the glue assembly
  consumes: Shannon at Δ ≤ 4 repackaged from the multiplicity-matrix
  interface into an INDEXED-FAMILY interface.  The M-edges of the
  contraction multigraph arise as a family `t : ι → Sym2 N` (ι = the
  chains of length ≤ 2 plus the two halves of each chain of length ≥ 3;
  `t i` = the unordered pair of M-nodes joined: junction groups, kept
  degree-≤1 vertices, fresh middle nodes), and the transport wants ONE
  color per family member, distinct whenever two members share an
  M-node — exactly what properness of the M-coloring delivers:
  rainbowness within junction groups, l = 2 chains monochromatic, l = 3
  port distinctness via the shared middle node.  Internally: the
  multiplicity matrix of the family (`famMatrix`) satisfies Shannon's
  hypotheses (the degree transfer is `mdeg_famMatrix`, a fiberwise
  partition by the other endpoint), and Shannon's set-valued output is
  converted to a per-member color by a per-parallel-class bijection
  (`transportAt`: fiber ≃ color set via `Finset.equivFinOfCardEq`).

* `exists_cycle_distance2` — the pure-cycle part of step (G5): for every
  cycle length L ≥ 3 an explicit 3-color pattern with no two colors at
  cyclic index distance 2 equal (consumed as c(e_i) := f i along a pure
  cycle, discharging the `interior` field of `IsGlueColoring` there;
  3 ≤ 6 colors).  Formula: L = 3 ↦ (0,1,2); L ≥ 4 ↦ ⌊i/2⌋ mod 2 with the
  last two positions overridden to color 2.

Machine pretest BEFORE proving (standing rule):
`lenses/C6L3-lean-construction/pretest_construct.py`, exit 0 — P-A pins
the cycle formula verbatim (L = 3..4000, every constraint, exact); P-B
pins the indexed-Shannon proof shape (counting identity + per-fiber
bijection transport) on a corpus including the Shannon-tight fat
triangle, a 4-fold parallel class, middle-node chain shapes, and 600
random loopless Δ ≤ 4 multigraph families (524 with a degree-4-tight
node), the conclusion checked exhaustively over all index pairs.
-/


open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The multiplicity matrix of an indexed family of M-edges -/

/-- The multiplicity matrix of a family `t` of unordered node pairs:
`famMatrix t a b` counts the family members equal to `s(a,b)`.  This is
the contraction multigraph M of the ≤ 6 construction when `t` enumerates
its edges (one entry per l ≤ 2 chain, two per l ≥ 3 chain). -/
def famMatrix (t : ι → Sym2 V) (a b : V) : ℕ :=
  #{i ∈ Finset.univ | t i = s(a, b)}

lemma famMatrix_symm (t : ι → Sym2 V) (a b : V) :
    famMatrix t a b = famMatrix t b a := by
  unfold famMatrix
  rw [show s(a, b) = s(b, a) from Sym2.eq_swap]

/-- A loopless family has zero diagonal multiplicities. -/
lemma famMatrix_diag (t : ι → Sym2 V) (hloop : ∀ i, ¬(t i).IsDiag) (a : V) :
    famMatrix t a a = 0 := by
  unfold famMatrix
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ h
  exact hloop i (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)

/-- **Degree transfer**: the matrix degree of a node equals the number of
family members containing it (fiberwise partition of those members by
their other endpoint; looplessness makes the other endpoint unique). -/
lemma mdeg_famMatrix (t : ι → Sym2 V) (hloop : ∀ i, ¬(t i).IsDiag) (a : V) :
    mdeg (famMatrix t) a = #{i ∈ Finset.univ | a ∈ t i} := by
  classical
  rw [mdeg, Finset.card_eq_sum_card_fiberwise
    (f := fun i => if h : a ∈ t i then Sym2.Mem.other' h else a)
    (t := Finset.univ) (fun x _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro u _
  unfold famMatrix
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hti
    have ha : a ∈ t i := by rw [hti]; exact Sym2.mem_mk_left a u
    refine ⟨ha, ?_⟩
    simp only [dif_pos ha]
    exact Sym2.congr_right.mp ((Sym2.other_spec' ha).trans hti)
  · rintro ⟨ha, hfu⟩
    simp only [dif_pos ha] at hfu
    rw [← hfu]
    exact (Sym2.other_spec' ha).symm

/-! ### Transport: from set-valued Shannon output to one color per edge -/

/-- Pick the color of family member `i` inside the parallel class `e`:
the fiber `{k | t k = e}` is bijected onto the color set `Φ e` (their
cardinalities agree), and `i`'s image is taken.  Stated at an explicit
`e` (with `h : t i = e`) so that injectivity lives at a FIXED parallel
class — no dependent rewriting in the consumers. -/
private noncomputable def transportAt (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) (i : ι) (h : t i = e) : Fin 6 :=
  ((Φ e).equivFin.symm (Finset.equivFinOfCardEq (hc e)
    ⟨i, mem_filter.mpr ⟨mem_univ i, h⟩⟩)).1

private lemma transportAt_mem (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) (i : ι) (h : t i = e) :
    transportAt t Φ hc e i h ∈ Φ e :=
  ((Φ e).equivFin.symm _).2

/-- Within one parallel class the transport is injective. -/
private lemma transportAt_inj (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) {i j : ι} (hi : t i = e) (hj : t j = e)
    (heq : transportAt t Φ hc e i hi = transportAt t Φ hc e j hj) :
    i = j := by
  unfold transportAt at heq
  have h1 := (Φ e).equivFin.symm.injective (Subtype.ext heq)
  have h2 := (Finset.equivFinOfCardEq (hc e)).injective h1
  exact Subtype.mk_eq_mk.mp h2

/-- The transport only depends on the parallel class as a value (proof
irrelevance across the membership certificate). -/
private lemma transportAt_congr (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (i : ι) {e e' : Sym2 V} (h : t i = e) (h' : t i = e')
    (hee : e = e') :
    transportAt t Φ hc e i h = transportAt t Φ hc e' i h' := by
  subst hee
  rfl

/-! ### Shannon at Δ ≤ 4, indexed-family form -/

/-- **Indexed Shannon transport** (the (G3) step in the form the glue
assembly consumes): every finite family `t : ι → Sym2 V` of loopless
M-edges with at most 4 members at each node admits a 6-coloring
`col : ι → Fin 6` of its MEMBERS such that any two distinct members
sharing a node receive distinct colors.  Specializing `ι` to the chains
(l ≤ 2) plus chain halves (l ≥ 3) of the ≤ 6 construction, `col` is the
per-chain/per-port color: distinctness at a junction-group node is the
`rainbow` field, and distinctness at a middle node is the l = 3 port
distinctness required by `isFill_exists`. -/
theorem shannon_six_indexed (t : ι → Sym2 V)
    (hloop : ∀ i, ¬(t i).IsDiag)
    (hdeg : ∀ a : V, #{i ∈ Finset.univ | a ∈ t i} ≤ 4) :
    ∃ col : ι → Fin 6, ∀ i j : ι, i ≠ j →
      ∀ a : V, a ∈ t i → a ∈ t j → col i ≠ col j := by
  classical
  obtain ⟨φ, hφs, hφc, hφd⟩ := shannon_six_of_maxDegree_four (famMatrix t)
    (famMatrix_symm t) (famMatrix_diag t hloop)
    (fun a => by
      show mdeg (famMatrix t) a ≤ 4
      rw [mdeg_famMatrix t hloop a]
      exact hdeg a)
  set Φ : Sym2 V → Finset (Fin 6) := Sym2.lift ⟨φ, hφs⟩ with hΦdef
  have hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e) := by
    intro e
    induction e using Sym2.ind with
    | _ a b => rw [hΦdef, Sym2.lift_mk, hφc]; rfl
  refine ⟨fun i => transportAt t Φ hc (t i) i rfl, ?_⟩
  intro i j hij a hai haj hcol
  replace hcol : transportAt t Φ hc (t i) i rfl =
      transportAt t Φ hc (t j) j rfl := hcol
  by_cases he : t i = t j
  · -- same parallel class: the per-fiber bijection is injective
    rw [transportAt_congr t Φ hc j rfl he.symm he.symm] at hcol
    exact hij (transportAt_inj t Φ hc (t i) rfl he.symm hcol)
  · -- different parallel classes at a shared node: color sets disjoint
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hai
    obtain ⟨b', hb'⟩ := Sym2.mem_iff_exists.mp haj
    have hbb : b ≠ b' := fun hcontra => he (by rw [hb, hb', hcontra])
    have hdisj : Disjoint (Φ (t i)) (Φ (t j)) := by
      rw [hb, hb', hΦdef, Sym2.lift_mk, Sym2.lift_mk]
      exact hφd a b b' hbb
    have h1 := transportAt_mem t Φ hc (t i) i rfl
    have h2 := transportAt_mem t Φ hc (t j) j rfl
    rw [hcol] at h1
    exact (Finset.disjoint_left.mp hdisj h1) h2

/-! ### Pure-cycle distance-2 coloring (the (G5) pure-cycle step) -/

/-- **Pure-cycle distance-2 coloring**: for every cycle length L ≥ 3
there is a 3-color pattern `f` with `f i ≠ f ((i+2) % L)` for every
`i < L` — consumed as `c(e_i) := f i` along a pure cycle of the chain
decomposition, which discharges the `interior` field of
`IsGlueColoring` there (each side of an interior row is the edge two
steps away around the cycle).  Explicit formula, machine-pretested
verbatim (P-A): `L = 3 ↦ i % 3`, else `⌊i/2⌋ mod 2` overridden to `2`
at the last two positions. -/
theorem exists_cycle_distance2 (L : ℕ) (hL : 3 ≤ L) :
    ∃ f : ℕ → ℕ, (∀ i, f i < 3) ∧ ∀ i < L, f i ≠ f ((i + 2) % L) := by
  rcases Nat.lt_or_ge L 4 with hL3 | hL4
  · -- L = 3: the pure triangle; all three colors pairwise distinct
    have h3 : L = 3 := by omega
    subst h3
    exact ⟨fun i => i % 3, fun i => by show i % 3 < 3; omega, by decide⟩
  · -- L ≥ 4: ⌊i/2⌋ mod 2, last two positions overridden to 2
    refine ⟨fun i => if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2,
      fun i => ?_, fun i hi => ?_⟩
    · show (if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2) < 3
      split_ifs <;> omega
    · show (if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2) ≠
        (if (i + 2) % L = L - 2 ∨ (i + 2) % L = L - 1 then 2
         else ((i + 2) % L / 2) % 2)
      by_cases h2 : i = L - 2
      · -- wrap: (L−2) + 2 ≡ 0, and f 0 = 0 ≠ 2
        have hj : (i + 2) % L = 0 := by
          rw [show i + 2 = L by omega, Nat.mod_self]
        rw [if_pos (Or.inl h2), hj, if_neg (by omega)]
        omega
      · by_cases h1 : i = L - 1
        · -- wrap: (L−1) + 2 ≡ 1, and f 1 = 0 ≠ 2
          have hj : (i + 2) % L = 1 := by
            rw [show i + 2 = L + 1 by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt (by omega)]
          rw [if_pos (Or.inr h1), hj, if_neg (by omega)]
          omega
        · -- interior: no wrap, both positions ≤ L − 1
          have hj : (i + 2) % L = i + 2 := Nat.mod_eq_of_lt (by omega)
          rw [hj, if_neg (by omega)]
          by_cases hend : i + 2 = L - 2 ∨ i + 2 = L - 1
          · rw [if_pos hend]; omega
          · rw [if_neg hend]; omega

end

/-! ###### source file: SMaj/Master.lean ###### -/
section
/-
SMaj/Master.lean — the Master Theorem (THEOREMS.md §3) in Lean.

Fully proved here:
* `master_coloring` — the coloring form: a coloring rainbow on a grouping with
  g(v) ≤ h_s(d(v)) is strong majority whenever every edge satisfies CRIT_s.
* `admissible_of_crit` — CRIT_s (s ≥ 2) implies admissibility.
* `corA_coloring` — the Corollary-A instantiation (no degrees 2 or 4, s = 3).
* `master_of_inputs` — the full Master Theorem conditional on the two
  existence inputs, each isolated as a named statement below.

Also proved here (campaign C5, lens C5L3-lean-six, 2026-06-13):
* `exists_even_grouping` — partition the edges at each vertex into
  h_s(d(v)) groups of size ≤ s (the even-split construction `evenIx`:
  index the incident edges by `Finset.equivFin` and group by index
  division — CLOSED, was a `proof_wanted`).

Open obligation (stated as `proof_wanted`, keeping the library sorry-free):
* `rainbow_of_groupSizes` — a rainbow (s+1)-coloring exists when all groups
  have size ≤ s.  This is Vizing's theorem for the split graph G* (Δ(G*) ≤ s,
  G* simple — THEOREMS.md Lemmas 2–3).  Vizing's theorem is NOT in mathlib
  v4.30.0 (checked 2026-06-12) and still absent from master (GitHub code
  search grep-clean for `Vizing`, re-checked 2026-06-13); this is the
  bridgehead's single external gap.
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-- **Master Theorem, coloring form** (THEOREMS.md §3, fully proved): if `c`
is rainbow on a grouping `ix` whose group counts obey g(v) ≤ h_s(d(v)), and
every edge of `G` satisfies CRIT_s, then `c` is a strong majority coloring. -/
theorem master_coloring (s : ℕ) (ix : V → Sym2 V → ℕ) (c : Sym2 V → C)
    (hrb : IsRainbow G ix c)
    (hg : ∀ v : V, groups G ix v ≤ hfun s (G.degree v))
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    IsStrongMajority G c := by
  intro u v huv α
  calc nColor G c u v α
      ≤ groups G ix u + groups G ix v := counting_lemma hrb huv α
    _ ≤ hfun s (G.degree u) + hfun s (G.degree v) :=
        Nat.add_le_add (hg u) (hg v)
    _ ≤ (G.degree u + G.degree v - 2) / 2 := hcrit u v huv

/-- CRIT_s (any s ≥ 2) excludes the inadmissible pair (1,2): graphs satisfying
the Master Theorem's hypothesis are automatically admissible. -/
theorem admissible_of_crit (s : ℕ) (hs : 2 ≤ s)
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    Admissible G := fun u v huv =>
  crit_admissible hs ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
    ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩) (hcrit u v huv)

/-- Corollary A, coloring form: if no vertex has degree 2 or 4 and `c` is
rainbow on a grouping with g(v) ≤ h_3(d(v)) — e.g. an even grouping into
triples-and-pairs — then `c` is strong majority.  (With the two existence
inputs below this gives Maj′(G) ≤ 4 on that class.) -/
theorem corA_coloring (ix : V → Sym2 V → ℕ) (c : Sym2 V → C)
    (hrb : IsRainbow G ix c)
    (hg : ∀ v : V, groups G ix v ≤ hfun 3 (G.degree v))
    (hdeg : ∀ v : V, G.degree v ≠ 2 ∧ G.degree v ≠ 4) :
    IsStrongMajority G c :=
  master_coloring 3 ix c hrb hg fun u v huv =>
    crit3_of_no24 ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
      ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩)
      (hdeg u).1 (hdeg u).2 (hdeg v).1 (hdeg v).2

variable (G) in
/-- Every group of the grouping `ix` has at most `s` members. -/
def GroupSizesLE (ix : V → Sym2 V → ℕ) (s : ℕ) : Prop :=
  ∀ (v : V) (k : ℕ), #{f ∈ G.incidenceFinset v | ix v f = k} ≤ s

/-- **The full Master Theorem, conditional form** (proved): given the two
existence inputs — an even grouping, and a rainbow (s+1)-coloring on any
grouping with group sizes ≤ s (= Vizing for the split graph) — every graph
all of whose edges satisfy CRIT_s is admissible and has a strong majority
(s+1)-coloring (i.e. Maj′(G) ≤ s + 1). -/
theorem master_of_inputs (s : ℕ) (hs : 2 ≤ s)
    (hgrp : ∃ ix : V → Sym2 V → ℕ,
      GroupSizesLE G ix s ∧ ∀ v : V, groups G ix v ≤ hfun s (G.degree v))
    (hviz : ∀ ix : V → Sym2 V → ℕ, GroupSizesLE G ix s →
      ∃ c : Sym2 V → Fin (s + 1), IsRainbow G ix c)
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    Admissible G ∧ ∃ c : Sym2 V → Fin (s + 1), IsStrongMajority G c := by
  obtain ⟨ix, hsz, hg⟩ := hgrp
  obtain ⟨c, hrb⟩ := hviz ix hsz
  exact ⟨admissible_of_crit s hs hcrit, c, master_coloring s ix c hrb hg hcrit⟩

/-! ### The even grouping (input 1 of `master_of_inputs`): CLOSED
(campaign C5, lens C5L3-lean-six; machine pretest
`lenses/C5L3-lean-six/pretest_glue.py` P0 re-pinned the index-division
shape — fiber sizes and group counts — for s = 1..8, d = 0..200 before
these proofs were written). -/

/-- Fibers of division by `s` on `range d` have at most `s` members
(the arithmetic core of the even grouping). -/
lemma card_div_fiber_le (d : ℕ) {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    #{i ∈ Finset.range d | i / s = k} ≤ s := by
  calc #{i ∈ Finset.range d | i / s = k}
      ≤ #(Finset.Ico (k * s) (k * s + s)) := by
        apply card_le_card
        intro i hi
        rw [mem_filter, mem_range] at hi
        rw [mem_Ico]
        constructor
        · calc k * s = i / s * s := by rw [hi.2]
            _ ≤ i := Nat.div_mul_le_self i s
        · have h1 : i / s < k + 1 := by omega
          calc i < (k + 1) * s := (Nat.div_lt_iff_lt_mul (by omega)).mp h1
            _ = k * s + s := by ring
    _ = s := by rw [Nat.card_Ico]; omega

variable (G) in
/-- The canonical even grouping: index the incident edges at each vertex by
`Finset.equivFin` and group by index division (groups of `s` consecutive
indices).  Off the incidence set the value is irrelevant (0). -/
noncomputable def evenIx (s : ℕ) (v : V) (f : Sym2 V) : ℕ :=
  if h : f ∈ G.incidenceFinset v
  then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) / s else 0

/-- **Even grouping existence** (input 1 of `master_of_inputs`, CLOSED):
split the d(v) edges at each vertex into h_s(d(v)) groups of size ≤ s by
index division. -/
theorem exists_even_grouping (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ ix : V → Sym2 V → ℕ,
      GroupSizesLE G ix s ∧ ∀ v : V, groups G ix v ≤ hfun s (G.degree v) := by
  refine ⟨evenIx G s, ?_, ?_⟩
  · -- group sizes ≤ s: inject each fiber into the matching division fiber
    -- of the index range
    intro v k
    calc #{f ∈ G.incidenceFinset v | evenIx G s v f = k}
        ≤ #{i ∈ Finset.range #(G.incidenceFinset v) | i / s = k} := by
          apply card_le_card_of_injOn
            (fun f => if h : f ∈ G.incidenceFinset v
              then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0)
          · intro f hf
            rw [mem_coe, mem_filter] at hf
            obtain ⟨hmem, hval⟩ := hf
            rw [evenIx, dif_pos hmem] at hval
            show (if h : f ∈ G.incidenceFinset v
              then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0) ∈ _
            rw [dif_pos hmem, mem_coe, mem_filter, mem_range]
            exact ⟨((G.incidenceFinset v).equivFin ⟨f, hmem⟩).isLt, hval⟩
          · intro f₁ h₁ f₂ h₂ heq
            rw [mem_coe, mem_filter] at h₁ h₂
            simp only [dif_pos h₁.1, dif_pos h₂.1] at heq
            have hfin : ((G.incidenceFinset v).equivFin ⟨f₁, h₁.1⟩) =
                ((G.incidenceFinset v).equivFin ⟨f₂, h₂.1⟩) :=
              Fin.val_injective heq
            exact Subtype.ext_iff.mp ((G.incidenceFinset v).equivFin.injective hfin)
      _ ≤ s := card_div_fiber_le _ hs k
  · -- group counts ≤ h_s(d): the image of index division lies in
    -- range ((d−1)/s + 1) = range ⌈d/s⌉
    intro v
    rw [groups]
    split_ifs with hd
    · exact Nat.zero_le _
    · rw [hfun, if_neg (by omega)]
      calc #((G.incidenceFinset v).image (evenIx G s v))
          ≤ #(Finset.range ((G.degree v - 1) / s + 1)) := by
            apply card_le_card
            intro k hk
            rw [mem_image] at hk
            obtain ⟨f, hf, hfk⟩ := hk
            rw [evenIx, dif_pos hf] at hfk
            rw [mem_range]
            have hlt : ((G.incidenceFinset v).equivFin ⟨f, hf⟩ : ℕ) <
                G.degree v := by
              have h := ((G.incidenceFinset v).equivFin ⟨f, hf⟩).isLt
              have hc : #(G.incidenceFinset v) = G.degree v := by
                rw [card_incidenceFinset_eq_degree]
              omega
            subst hfk
            exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
        _ = (G.degree v + s - 1) / s := by
            rw [card_range, ← Nat.add_div_right _ (by omega : 0 < s)]
            congr 1
            omega

/-! ### Open obligation (the precise remaining gap to the unconditional
Master Theorem, hence to Corollaries A/A1/A2/B/C of THEOREMS.md §4). -/

/-- Rainbow colorability with s+1 colors when all groups have size ≤ s:
equivalently, a proper edge (s+1)-coloring of the split graph G* with
Δ(G*) ≤ s (THEOREMS.md Lemmas 2–3).  This is **Vizing's theorem**, absent
from mathlib v4.30.0 and from master (re-checked 2026-06-13) — the single
external gap of the bridgehead. -/
proof_wanted rainbow_of_groupSizes (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (ix : V → Sym2 V → ℕ) (hsz : GroupSizesLE G ix s) :
    ∃ c : Sym2 V → Fin (s + 1), IsRainbow G ix c

end

/-! ###### source file: SMaj/Six/Assembly.lean ###### -/
section
/-
SMaj/Six/Assembly.lean — step 2 of the `maj_le_six` assembly: the piece
CHOICE per linkage class, the sites/grouping `glueIx`, the M-node type,
the member family `t : Member G → Sym2 (MNode G)`, the per-node ≤ 4
bound, and the Shannon member coloring (campaign C8, lens
C8L3-lean-assembly session 2, 2026-06-13).

`SMaj/Six/Partition.lean` made the chain decomposition canonical (a
piece's edge set is the linkage class of any of its edges).  This file
consumes that canonicality to CHOOSE one piece per linkage class
(`classPiece`, via `Quotient`-representatives — consistent by
`IsPiece.edges_toFinset_eq`) and builds the contraction multigraph M of
the ≤ 6 construction as an indexed family, exactly in the shape
`shannon_six_indexed` (campaign C6) consumes:

* `glueIx` — the glue grouping: `evenIx G 4` at junctions (degree ≥ 3;
  group sizes ≤ 4, group counts ≤ ⌈d/4⌉ = the `junction_groups` field),
  `evenIx G 1` at degree ≤ 2 vertices (singleton groups — the l = 2
  monochromatic chains FORCE rainbow-freeness there);
* `MNode` — M-nodes: junction/kept group sites `(v, k)` (`k` bounded by
  `Fintype.card V + 1`, keeping the node type FINITE for Shannon) ⊕ one
  middle node per linkage class (`Quotient (linkSetoid G)`);
* `Member` — the M-edges: per CHAIN class one member (the whole chain)
  when its piece has ≤ 2 edges, two members (L/R halves through the
  middle node) when ≥ 3; pure cycles contribute none;
* `mfam` — the family itself, with `mfam_not_isDiag` (looplessness; a
  closed trail has ≥ 3 edges, so short chains have distinct ends) and
  `mfam_count_le` (per-node count ≤ 4: at a group site the members
  inject into the ≤ 4 edges of the group via their PORT edges —
  first/last edges of the chosen pieces, distinct by `edges_nodup`; at
  a middle node only the class's own two halves appear);
* `exists_member_coloring` — `shannon_six_indexed` instantiated: a
  6-coloring of the members, distinct at shared M-nodes.  This is the
  (G3) coloring layer of the glue construction, on the REAL M of an
  arbitrary graph.

Machine pretest BEFORE proving (standing rule):
`lenses/C8L3-lean-assembly/pretest_assembly.py`, exit 0 — R-A..R-F pin
the design on 255,050 edge checks (EXHAUSTIVE all labeled graphs n ≤ 5
and n = 6, classics incl. a degree-9 star of chains, 300 randoms
n ≤ 14): fiber bounds, member well-formedness/looplessness, per-node
counts, the member → port-edge injection, port coverage, and Shannon
6-colorability (the pretest's own first run caught that GREEDY needs 7
colors — 6 genuinely needs the banked Shannon theorem).

Still owed to the assembly after this file (honest scope): the port
coloring/its agreement with `satSet`, the fills, the global coloring,
the `IsGlueColoring` bundle, and `maj_le_six` (which remains
`proof_wanted`), plus `rainbow_of_groupSizes` (Vizing).
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Per-vertex forms of the even-grouping facts (`SMaj/Master.lean`
proves them inline inside `exists_even_grouping`; the assembly needs
them per vertex and per fiber). -/

/-- Group sizes of `evenIx` are ≤ s, per vertex and group. -/
lemma evenIx_fiber_le (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (hs : 1 ≤ s) (v : V) (k : ℕ) :
    #{f ∈ G.incidenceFinset v | evenIx G s v f = k} ≤ s := by
  calc #{f ∈ G.incidenceFinset v | evenIx G s v f = k}
      ≤ #{i ∈ Finset.range #(G.incidenceFinset v) | i / s = k} := by
        apply card_le_card_of_injOn
          (fun f => if h : f ∈ G.incidenceFinset v
            then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0)
        · intro f hf
          rw [mem_coe, mem_filter] at hf
          obtain ⟨hmem, hval⟩ := hf
          rw [evenIx, dif_pos hmem] at hval
          show (if h : f ∈ G.incidenceFinset v
            then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0) ∈ _
          rw [dif_pos hmem, mem_coe, mem_filter, mem_range]
          exact ⟨((G.incidenceFinset v).equivFin ⟨f, hmem⟩).isLt, hval⟩
        · intro f₁ h₁ f₂ h₂ heq
          rw [mem_coe, mem_filter] at h₁ h₂
          simp only [dif_pos h₁.1, dif_pos h₂.1] at heq
          have hfin : ((G.incidenceFinset v).equivFin ⟨f₁, h₁.1⟩) =
              ((G.incidenceFinset v).equivFin ⟨f₂, h₂.1⟩) :=
            Fin.val_injective heq
          exact Subtype.ext_iff.mp
            ((G.incidenceFinset v).equivFin.injective hfin)
    _ ≤ s := card_div_fiber_le _ hs k

/-- Group counts of `evenIx` are ≤ h_s(d), per vertex. -/
lemma groups_evenIx_le (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ}
    (hs : 1 ≤ s) (v : V) :
    groups G (evenIx G s) v ≤ hfun s (G.degree v) := by
  rw [groups]
  split_ifs with hd
  · exact Nat.zero_le _
  · rw [hfun, if_neg (by omega)]
    calc #((G.incidenceFinset v).image (evenIx G s v))
        ≤ #(Finset.range ((G.degree v - 1) / s + 1)) := by
          apply card_le_card
          intro k hk
          rw [mem_image] at hk
          obtain ⟨f, hf, hfk⟩ := hk
          rw [evenIx, dif_pos hf] at hfk
          rw [mem_range]
          have hlt : ((G.incidenceFinset v).equivFin ⟨f, hf⟩ : ℕ) <
              G.degree v := by
            have h := ((G.incidenceFinset v).equivFin ⟨f, hf⟩).isLt
            have hc : #(G.incidenceFinset v) = G.degree v := by
              rw [card_incidenceFinset_eq_degree]
            omega
          subst hfk
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
      _ = (G.degree v + s - 1) / s := by
          rw [card_range, ← Nat.add_div_right _ (by omega : 0 < s)]
          congr 1
          omega

/-- `evenIx G 1` is injective on the incidence finset (singleton
groups): the rainbow field is free at its vertices. -/
lemma evenIx_one_inj {v : V} {f₁ f₂ : Sym2 V}
    (h₁ : f₁ ∈ G.incidenceFinset v) (h₂ : f₂ ∈ G.incidenceFinset v)
    (h : evenIx G 1 v f₁ = evenIx G 1 v f₂) : f₁ = f₂ := by
  rw [evenIx, evenIx, dif_pos h₁, dif_pos h₂, Nat.div_one, Nat.div_one] at h
  exact Subtype.ext_iff.mp
    ((G.incidenceFinset v).equivFin.injective (Fin.val_injective h))

/-! ### The glue grouping -/

variable (G) in
/-- **The glue grouping** (the `ix` of the future `IsGlueColoring`):
`evenIx G 4` at junctions (degree ≥ 3), singleton groups (`evenIx G 1`)
at degree ≤ 2 vertices.  The l = 2 chains are monochromatic in the ≤ 6
construction, so their shared degree-2 vertex must not group its two
edges together — singleton groups make the rainbow field free there. -/
noncomputable def glueIx : V → Sym2 V → ℕ := fun v =>
  if 3 ≤ G.degree v then evenIx G 4 v else evenIx G 1 v

lemma glueIx_eq_junction {v : V} (h : 3 ≤ G.degree v) :
    glueIx G v = evenIx G 4 v := by
  unfold glueIx
  exact if_pos h

lemma glueIx_eq_low {v : V} (h : ¬3 ≤ G.degree v) :
    glueIx G v = evenIx G 1 v := by
  unfold glueIx
  exact if_neg h

/-- Every `glueIx` group has at most 4 members. -/
lemma glueIx_fiber_le (v : V) (k : ℕ) :
    #{f ∈ G.incidenceFinset v | glueIx G v f = k} ≤ 4 := by
  by_cases h : 3 ≤ G.degree v
  · rw [glueIx_eq_junction h]
    exact evenIx_fiber_le G (by omega) v k
  · rw [glueIx_eq_low h]
    exact le_trans (evenIx_fiber_le G le_rfl v k) (by omega)

/-- At junctions, `glueIx` uses at most ⌈d/4⌉ groups — the
`junction_groups` field of the glue bundle. -/
lemma groups_glueIx_le {v : V} (h : 3 ≤ G.degree v) :
    groups G (glueIx G) v ≤ hfun 4 (G.degree v) := by
  have heq : groups G (glueIx G) v = groups G (evenIx G 4) v := by
    unfold groups
    rw [glueIx_eq_junction h]
  rw [heq]
  exact groups_evenIx_le G (by omega) v

/-- At degree ≤ 2 vertices, `glueIx` groups are singletons: two incident
edges in one group are equal (the rainbow field is free there). -/
lemma glueIx_inj_low {v : V} (h : ¬3 ≤ G.degree v) {f₁ f₂ : Sym2 V}
    (h₁ : f₁ ∈ G.incidenceFinset v) (h₂ : f₂ ∈ G.incidenceFinset v)
    (heq : glueIx G v f₁ = glueIx G v f₂) : f₁ = f₂ := by
  rw [glueIx_eq_low h] at heq
  exact evenIx_one_inj h₁ h₂ heq

/-- `glueIx` values are bounded by `Fintype.card V` — the group index
fits in `Fin (Fintype.card V + 1)`, keeping the M-node type finite. -/
lemma glueIx_lt (v : V) (f : Sym2 V) :
    glueIx G v f < Fintype.card V + 1 := by
  have hgen : ∀ s : ℕ, evenIx G s v f < Fintype.card V + 1 := by
    intro s
    rw [evenIx]
    split_ifs with h
    · have h1 : ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) <
          #(G.incidenceFinset v) := Fin.isLt _
      have h2 : #(G.incidenceFinset v) ≤ Fintype.card V := by
        rw [card_incidenceFinset_eq_degree, ← card_neighborFinset_eq_degree]
        exact card_le_univ _
      have h3 := Nat.div_le_self
        ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) s
      omega
    · omega
  by_cases h : 3 ≤ G.degree v
  · rw [glueIx_eq_junction h]; exact hgen 4
  · rw [glueIx_eq_low h]; exact hgen 1

/-! ### Pieces as bundled data, and the choice per linkage class -/

variable (G) in
/-- A piece of the chain decomposition, bundled with its endpoints (the
walk-level certificate is `IsPiece`, `SMaj/Six/ChainDecomp.lean`). -/
structure Piece where
  a : V
  b : V
  walk : G.Walk a b
  piece : IsPiece G walk

namespace Piece

/-- The first edge, by value (matches `IsPiece.eq_first_or_last`). -/
def firstEdge (P : Piece G) : Sym2 V := s(P.a, P.walk.snd)

/-- The last edge, by value (matches `IsPiece.eq_first_or_last`). -/
def lastEdge (P : Piece G) : Sym2 V := s(P.walk.penultimate, P.b)

/-- Pure-cycle discriminator: chains have start degree ≠ 2, pure cycles
start degree 2 (a piece's ends-dichotomy separates exactly there). -/
def IsCycle (P : Piece G) : Prop := G.degree P.a = 2

omit [DecidableEq V] in
lemma chain_ends (P : Piece G) (h : ¬P.IsCycle) :
    G.degree P.a ≠ 2 ∧ G.degree P.b ≠ 2 := by
  rcases P.piece.ends with h1 | ⟨-, hall⟩
  · exact h1
  · exact absurd (hall P.a P.walk.start_mem_support) h

omit [DecidableEq V] in
lemma cycle_spec (P : Piece G) (h : P.IsCycle) :
    P.a = P.b ∧ ∀ v ∈ P.walk.support, G.degree v = 2 := by
  rcases P.piece.ends with ⟨h1, -⟩ | h2
  · exact absurd h h1
  · exact h2

omit [DecidableEq V] in
lemma edges_length_pos (P : Piece G) : 0 < P.walk.edges.length := by
  rw [P.walk.length_edges]
  exact Nat.pos_of_ne_zero P.piece.ne

omit [DecidableEq V] in
/-- The first edge sits at slot 0. -/
lemma firstEdge_eq (P : Piece G) :
    ∃ h : 0 < P.walk.edges.length, P.walk.edges[0] = P.firstEdge := by
  refine ⟨P.edges_length_pos, ?_⟩
  rw [edges_getElem P.walk P.edges_length_pos, Walk.getVert_zero]
  rfl

omit [DecidableEq V] in
/-- The last edge sits at slot `length − 1`. -/
lemma lastEdge_eq (P : Piece G) :
    ∃ h : P.walk.edges.length - 1 < P.walk.edges.length,
      P.walk.edges[P.walk.edges.length - 1] = P.lastEdge := by
  have h0 := P.edges_length_pos
  have hL : P.walk.edges.length = P.walk.length := P.walk.length_edges
  refine ⟨by omega, ?_⟩
  rw [edges_getElem P.walk (by omega), hL,
    show P.walk.length - 1 + 1 = P.walk.length by omega,
    P.walk.getVert_length]
  rfl

omit [DecidableEq V] in
lemma firstEdge_mem (P : Piece G) : P.firstEdge ∈ P.walk.edges := by
  obtain ⟨h, heq⟩ := P.firstEdge_eq
  rw [← heq]
  exact List.getElem_mem h

omit [DecidableEq V] in
lemma lastEdge_mem (P : Piece G) : P.lastEdge ∈ P.walk.edges := by
  obtain ⟨h, heq⟩ := P.lastEdge_eq
  rw [← heq]
  exact List.getElem_mem h

omit [DecidableEq V] in
/-- On a piece with ≥ 2 edges, the first and last edges differ
(`edges_nodup`). -/
lemma firstEdge_ne_lastEdge (P : Piece G) (h2 : 2 ≤ P.walk.length) :
    P.firstEdge ≠ P.lastEdge := by
  obtain ⟨hf, hfe⟩ := P.firstEdge_eq
  obtain ⟨hl, hle⟩ := P.lastEdge_eq
  intro heq
  have h : P.walk.edges[0] = P.walk.edges[P.walk.edges.length - 1] := by
    rw [hfe, hle, heq]
  have h01 := (P.piece.trail.edges_nodup.getElem_inj_iff).mp h
  have hL : P.walk.edges.length = P.walk.length := P.walk.length_edges
  omega

omit [DecidableEq V] in
/-- Short pieces (< 3 edges) have distinct ends: a closed trail has ≥ 3
edges — the looplessness input for whole-chain members. -/
lemma a_ne_b_of_length_lt_three (P : Piece G) (hl : P.walk.length < 3) :
    P.a ≠ P.b := by
  obtain ⟨a, b, w, hp⟩ := P
  show a ≠ b
  rintro rfl
  exact absurd (three_le_length_of_closed hp.trail hp.ne) (by
    simp only at hl
    omega)

end Piece

/-- Every edge lies on some (bundled) piece — `exists_piece`
repackaged. -/
lemma exists_piece_through {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, e ∈ P.walk.edges := by
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    obtain ⟨x, y, p, hp, hm⟩ := exists_piece (G.mem_edgeSet.mp he)
    exact ⟨⟨x, y, p, hp⟩, hm⟩

variable (G) in
/-- The edge classes: linkage classes represented by an edge.  These
index the pieces of the canonical decomposition. -/
abbrev EdgeClass : Type _ :=
  {q : Quotient (linkSetoid G) // q.out ∈ G.edgeSet}

variable (G) in
/-- **The piece choice**: one piece per edge class, through the class's
canonical representative.  Consistent by `IsPiece.edges_toFinset_eq`
(any two pieces through a common edge have equal edge sets). -/
noncomputable def classPiece (q : EdgeClass G) : Piece G :=
  (exists_piece_through q.2).choose

variable (G) in
lemma classPiece_mem (q : EdgeClass G) :
    q.1.out ∈ (classPiece G q).walk.edges :=
  (exists_piece_through q.2).choose_spec

variable (G) in
/-- Every edge of a class's piece belongs to that class. -/
lemma classPiece_class_eq {q : EdgeClass G} {g : Sym2 V}
    (hg : g ∈ (classPiece G q).walk.edges) :
    Quotient.mk (linkSetoid G) g = q.1 := by
  have h1 : Linked G g q.1.out :=
    (classPiece G q).piece.linked_of_mem hg (classPiece_mem G q)
  calc Quotient.mk (linkSetoid G) g
      = Quotient.mk (linkSetoid G) q.1.out := Quotient.sound h1
    _ = q.1 := Quotient.out_eq _

omit [DecidableEq V] in
/-- The class representative of an edge is an edge. -/
lemma out_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (Quotient.mk (linkSetoid G) e).out ∈ G.edgeSet :=
  Linked.mem_edgeSet
    (Linked.symm (Quotient.exact
      (Quotient.out_eq (Quotient.mk (linkSetoid G) e)))) he

variable (G) in
/-- **The canonical piece through an edge** — a function of the edge's
linkage class only. -/
noncomputable def pieceOf (e : Sym2 V) (he : e ∈ G.edgeSet) : Piece G :=
  classPiece G ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩

variable (G) in
lemma mem_pieceOf {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (pieceOf G e he).walk.edges :=
  (pieceOf G e he).piece.mem_of_linked (classPiece_mem G _)
    (Quotient.exact (Quotient.out_eq (Quotient.mk (linkSetoid G) e)))

variable (G) in
/-- Class-constancy of the piece choice: linked edges get THE SAME
piece (not merely pieces with equal edge sets). -/
lemma pieceOf_eq_of_linked {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (hf : f ∈ G.edgeSet) (h : Linked G e f) :
    pieceOf G e he = pieceOf G f hf := by
  unfold pieceOf
  congr 1
  exact Subtype.ext (Quotient.sound h)

variable (G) in
/-- Every edge of `pieceOf e` has the same canonical piece. -/
lemma pieceOf_eq_of_mem {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (hf : f ∈ G.edgeSet) (hmem : f ∈ (pieceOf G e he).walk.edges) :
    pieceOf G f hf = pieceOf G e he :=
  pieceOf_eq_of_linked G hf he
    ((pieceOf G e he).piece.linked_of_mem hmem (mem_pieceOf G he))

variable (G) in
/-- **Ports of the canonical piece** (`eq_first_or_last` transported):
a junction-incident edge is the first or last edge of its canonical
piece, with the junction at the corresponding end. -/
lemma pieceOf_port {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V}
    (hv : v ∈ e) (hdv : G.degree v ≠ 2) :
    (v = (pieceOf G e he).a ∧ e = (pieceOf G e he).firstEdge) ∨
    (v = (pieceOf G e he).b ∧ e = (pieceOf G e he).lastEdge) :=
  (pieceOf G e he).piece.eq_first_or_last (mem_pieceOf G he) hv hdv

/-! ### M-nodes and members -/

variable (G) in
/-- **The M-nodes** of the contraction multigraph: group sites `(v, k)`
(junction groups at degree ≥ 3, singleton sites at degree ≤ 2 — with
the group index bounded to keep the type FINITE, `glueIx_lt`) ⊕ one
middle node per linkage class. -/
abbrev MNode : Type _ :=
  (V × Fin (Fintype.card V + 1)) ⊕ Quotient (linkSetoid G)

variable (G) in
/-- The group site of the edge `f` at the vertex `v`. -/
noncomputable def nodeAt (v : V) (f : Sym2 V) : MNode G :=
  Sum.inl (v, ⟨glueIx G v f, glueIx_lt v f⟩)

lemma nodeAt_eq_inl_iff {v' v : V} {f : Sym2 V}
    {k : Fin (Fintype.card V + 1)} :
    nodeAt G v' f = Sum.inl (v, k) ↔ v' = v ∧ glueIx G v' f = k.1 := by
  simp [nodeAt, Fin.ext_iff]

lemma nodeAt_ne_inr {v : V} {f : Sym2 V}
    {q : Quotient (linkSetoid G)} : nodeAt G v f ≠ Sum.inr q := by
  simp [nodeAt]

namespace Piece

/-- The M-node at a piece's start (its first-edge group site). -/
noncomputable def startNode (P : Piece G) : MNode G :=
  nodeAt G P.a P.firstEdge

/-- The M-node at a piece's end (its last-edge group site). -/
noncomputable def endNode (P : Piece G) : MNode G :=
  nodeAt G P.b P.lastEdge

lemma startNode_ne_endNode (P : Piece G) (hab : P.a ≠ P.b) :
    P.startNode ≠ P.endNode := by
  unfold startNode endNode nodeAt
  simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq, not_and]
  intro h
  exact absurd h hab

end Piece

variable (G) in
/-- **Member validity**: `inl q` (the whole chain, or its L-half when
the piece has ≥ 3 edges) exists for every CHAIN class; `inr q` (the
R-half) additionally needs ≥ 3 edges.  Pure cycles contribute no
members — their edges are colored by `exists_cycle_distance2`, not
through M. -/
def MemberSpec : EdgeClass G ⊕ EdgeClass G → Prop
  | Sum.inl q => ¬(classPiece G q).IsCycle
  | Sum.inr q => ¬(classPiece G q).IsCycle ∧
      3 ≤ (classPiece G q).walk.length

variable (G) in
/-- **The members** — the M-edges of the contraction multigraph. -/
abbrev Member : Type _ := {m : EdgeClass G ⊕ EdgeClass G // MemberSpec G m}

variable (G) in
/-- The linkage class of a member. -/
def Member.cls : Member G → EdgeClass G
  | ⟨Sum.inl q, _⟩ => q
  | ⟨Sum.inr q, _⟩ => q

variable (G) in
/-- **The M-family** (the `t : ι → Sym2 N` of `shannon_six_indexed`):
the whole-chain member joins the two end sites; the L/R halves of a
long chain join their end site to the class's middle node. -/
noncomputable def mfam : Member G → Sym2 (MNode G)
  | ⟨Sum.inl q, _⟩ =>
      if 3 ≤ (classPiece G q).walk.length
      then s((classPiece G q).startNode, Sum.inr q.1)
      else s((classPiece G q).startNode, (classPiece G q).endNode)
  | ⟨Sum.inr q, _⟩ => s(Sum.inr q.1, (classPiece G q).endNode)

variable (G) in
/-- **Looplessness** of the M-family (`hloop` of
`shannon_six_indexed`): half members join a site to a middle node;
whole members join the two end sites of a chain with < 3 edges, whose
ends are DISTINCT vertices (a closed trail has ≥ 3 edges). -/
lemma mfam_not_isDiag (m : Member G) : ¬(mfam G m).IsDiag := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3, Sym2.mk_isDiag_iff]
      exact fun h => nodeAt_ne_inr h
    · simp only [mfam, if_neg h3, Sym2.mk_isDiag_iff]
      exact (classPiece G q).startNode_ne_endNode
        ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
  · simp only [mfam, Sym2.mk_isDiag_iff]
    exact fun h => nodeAt_ne_inr h.symm

/-! ### The port-edge injection and the per-node count bound -/

variable (G) in
open Classical in
/-- The port edge of a member at a target node: the member's first or
last edge, picked toward the node (only meaningful when the node lies
on the member — see `mfam_count_junction`). -/
noncomputable def portEdge (nd : MNode G) : Member G → Sym2 V
  | ⟨Sum.inl q, _⟩ =>
      if (classPiece G q).startNode = nd then (classPiece G q).firstEdge
      else (classPiece G q).lastEdge
  | ⟨Sum.inr q, _⟩ => (classPiece G q).lastEdge

variable (G) in
lemma portEdge_mem (nd : MNode G) (m : Member G) :
    portEdge G nd m ∈ (classPiece G (Member.cls G m)).walk.edges := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · simp only [portEdge, Member.cls]
    split_ifs
    · exact (classPiece G q).firstEdge_mem
    · exact (classPiece G q).lastEdge_mem
  · simp only [portEdge, Member.cls]
    exact (classPiece G q).lastEdge_mem

variable (G) in
/-- A whole/L member through a group site has it as its START node, and
its port edge there is the FIRST edge — unless the site is the end node
of a short chain, where the port edge is the LAST edge.  Packaged as:
the port edge is incident to `v` inside group `k`. -/
lemma portEdge_spec {v : V} {k : Fin (Fintype.card V + 1)}
    {m : Member G} (hnd : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    portEdge G (Sum.inl (v, k)) m ∈ G.incidenceFinset v ∧
      glueIx G v (portEdge G (Sum.inl (v, k)) m) = k.1 := by
  obtain ⟨mv, hspec⟩ := m
  have hinc : ∀ (P : Piece G), P.startNode = Sum.inl (v, k) →
      P.firstEdge ∈ G.incidenceFinset v ∧
        glueIx G v P.firstEdge = k.1 := by
    intro P h
    obtain ⟨hva, hix⟩ := nodeAt_eq_inl_iff.mp h
    subst hva
    refine ⟨mem_incFinset.mpr ⟨P.walk.edges_subset_edgeSet P.firstEdge_mem,
      Sym2.mem_mk_left _ _⟩, hix⟩
  have hinc' : ∀ (P : Piece G), P.endNode = Sum.inl (v, k) →
      P.lastEdge ∈ G.incidenceFinset v ∧
        glueIx G v P.lastEdge = k.1 := by
    intro P h
    obtain ⟨hva, hix⟩ := nodeAt_eq_inl_iff.mp h
    subst hva
    refine ⟨mem_incFinset.mpr ⟨P.walk.edges_subset_edgeSet P.lastEdge_mem,
      Sym2.mem_mk_right _ _⟩, hix⟩
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3] at hnd
      have hs : (classPiece G q).startNode = Sum.inl (v, k) := by
        rcases Sym2.mem_iff.mp hnd with h | h
        · exact h.symm
        · exact absurd h.symm (by simp)
      simp only [portEdge, if_pos hs]
      exact hinc _ hs
    · simp only [mfam, if_neg h3] at hnd
      rcases Sym2.mem_iff.mp hnd with h | h
      · simp only [portEdge, if_pos h.symm]
        exact hinc _ h.symm
      · have hne : (classPiece G q).startNode ≠
            (classPiece G q).endNode :=
          (classPiece G q).startNode_ne_endNode
            ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
        have hcond : ¬((classPiece G q).startNode = Sum.inl (v, k)) := by
          intro hc
          exact hne (hc.trans h)
        simp only [portEdge, if_neg hcond]
        exact hinc' _ h.symm
  · simp only [mfam] at hnd
    have hs : (classPiece G q).endNode = Sum.inl (v, k) := by
      rcases Sym2.mem_iff.mp hnd with h | h
      · exact absurd h.symm (by simp)
      · exact h.symm
    simp only [portEdge]
    exact hinc' _ hs

variable (G) in
/-- The L-half's port edge at a site it contains is the FIRST edge
(when the piece is long, its middle node is not a site). -/
lemma portEdge_inl_of_three_le {v : V} {k : Fin (Fintype.card V + 1)}
    {q : EdgeClass G} {h : MemberSpec G (Sum.inl q)}
    (h3 : 3 ≤ (classPiece G q).walk.length)
    (hnd : (Sum.inl (v, k) : MNode G) ∈ mfam G ⟨Sum.inl q, h⟩) :
    portEdge G (Sum.inl (v, k)) ⟨Sum.inl q, h⟩ =
      (classPiece G q).firstEdge := by
  simp only [mfam, if_pos h3] at hnd
  have hs : (classPiece G q).startNode = Sum.inl (v, k) := by
    rcases Sym2.mem_iff.mp hnd with h' | h'
    · exact h'.symm
    · exact absurd h'.symm (by simp)
  simp only [portEdge, if_pos hs]

variable (G) in
/-- **Port-member uniqueness** (the injection behind the site count,
and the rainbow input's uniqueness half): two members through a common
group site with THE SAME port edge there are equal.  (They share a
linkage class via the port edge; within a class, the L and R halves
have distinct ports by `edges_nodup`.) -/
theorem port_member_unique {v : V} {k : Fin (Fintype.card V + 1)}
    {m m' : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m)
    (hm' : (Sum.inl (v, k) : MNode G) ∈ mfam G m')
    (heq : portEdge G (Sum.inl (v, k)) m =
      portEdge G (Sum.inl (v, k)) m') : m = m' := by
  -- the two members share a linkage class
  have hc : Member.cls G m = Member.cls G m' := by
    apply Subtype.ext
    rw [← classPiece_class_eq G (portEdge_mem G _ m),
      ← classPiece_class_eq G (portEdge_mem G _ m'), heq]
  -- same constructor ⇒ equal; mixed ⇒ first = last edge, absurd
  obtain ⟨mv, hs⟩ := m
  obtain ⟨mv', hs'⟩ := m'
  apply Subtype.ext
  rcases mv with q | q <;> rcases mv' with q' | q'
  · simp only [Member.cls] at hc
    subst hc
    rfl
  · -- L/whole vs R: the R-half forces length ≥ 3, whence the
    -- L port is the first edge and the R port the last
    exfalso
    simp only [Member.cls] at hc
    subst hc
    have h3 : 3 ≤ (classPiece G q).walk.length := hs'.2
    rw [portEdge_inl_of_three_le G h3 hm] at heq
    simp only [portEdge] at heq
    exact (classPiece G q).firstEdge_ne_lastEdge (by omega) heq
  · exfalso
    simp only [Member.cls] at hc
    subst hc
    have h3 : 3 ≤ (classPiece G q).walk.length := hs.2
    rw [portEdge_inl_of_three_le G h3 hm'] at heq
    simp only [portEdge] at heq
    exact (classPiece G q).firstEdge_ne_lastEdge (by omega) heq.symm
  · simp only [Member.cls] at hc
    subst hc
    rfl

variable (G) in
/-- **The junction-site count** (`hdeg` at group sites): the members at
a site `(v, k)` inject via their port edges into the ≤ 4 edges of the
group `k` at `v`. -/
lemma mfam_count_junction [Fintype (Member G)] [DecidableEq (MNode G)]
    (v : V) (k : Fin (Fintype.card V + 1)) :
    #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inl (v, k) : MNode G) ∈ mfam G m} ≤ 4 := by
  classical
  calc #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inl (v, k) : MNode G) ∈ mfam G m}
      ≤ #{f ∈ G.incidenceFinset v | glueIx G v f = k.1} := by
        apply card_le_card_of_injOn (portEdge G (Sum.inl (v, k)))
        · intro m hm
          rw [mem_coe, mem_filter] at hm
          obtain ⟨hf, hix⟩ := portEdge_spec G hm.2
          rw [mem_coe, mem_filter]
          exact ⟨hf, hix⟩
        · intro m hm m' hm' heq
          rw [mem_coe, mem_filter] at hm hm'
          exact port_member_unique G hm.2 hm'.2 heq
    _ ≤ 4 := glueIx_fiber_le v k.1

variable (G) in
/-- Only the two halves of a class touch its middle node. -/
lemma cls_eq_of_inr_mem {q₀ : Quotient (linkSetoid G)} {m : Member G}
    (h : (Sum.inr q₀ : MNode G) ∈ mfam G m) : (Member.cls G m).1 = q₀ := by
  obtain ⟨mv, hspec⟩ := m
  rcases mv with q | q
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3] at h
      rcases Sym2.mem_iff.mp h with h' | h'
      · exact absurd h'.symm nodeAt_ne_inr
      · simp only [Member.cls]
        exact (Sum.inr.inj h').symm
    · simp only [mfam, if_neg h3] at h
      rcases Sym2.mem_iff.mp h with h' | h' <;>
        exact absurd h'.symm nodeAt_ne_inr
  · simp only [mfam] at h
    rcases Sym2.mem_iff.mp h with h' | h'
    · simp only [Member.cls]
      exact (Sum.inr.inj h').symm
    · exact absurd h'.symm nodeAt_ne_inr

variable (G) in
/-- **The middle-node count** (`hdeg` at middle nodes): at most the two
halves of the class — inject by the constructor tag. -/
lemma mfam_count_middle [Fintype (Member G)] [DecidableEq (MNode G)]
    (q₀ : Quotient (linkSetoid G)) :
    #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inr q₀ : MNode G) ∈ mfam G m} ≤ 4 := by
  classical
  calc #{m ∈ (Finset.univ : Finset (Member G)) |
        (Sum.inr q₀ : MNode G) ∈ mfam G m}
      ≤ #(Finset.univ : Finset Bool) := by
        apply card_le_card_of_injOn (fun m => m.1.isLeft)
        · intro m _
          exact mem_coe.mpr (mem_univ _)
        · intro m hm m' hm' hleft
          rw [mem_coe, mem_filter] at hm hm'
          have h1 := cls_eq_of_inr_mem G hm.2
          have h2 := cls_eq_of_inr_mem G hm'.2
          have hc : Member.cls G m = Member.cls G m' :=
            Subtype.ext (h1.trans h2.symm)
          obtain ⟨mv, hs⟩ := m
          obtain ⟨mv', hs'⟩ := m'
          apply Subtype.ext
          rcases mv with q | q <;> rcases mv' with q' | q' <;>
            simp only [Member.cls] at hc <;>
            simp only [Sum.isLeft] at hleft
          · subst hc; rfl
          · exact absurd hleft (by simp)
          · exact absurd hleft (by simp)
          · subst hc; rfl
    _ ≤ 4 := by
        rw [Finset.card_univ, Fintype.card_bool]
        omega

/-! ### Port coverage: every junction-incident edge is a member's port
(pretest R-E — the rainbow input's existence half; uniqueness is
`port_member_unique`) -/

variable (G) in
/-- The whole/L member contains the start site, with the first edge as
its port there. -/
lemma member_port_start {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle) :
    (classPiece G q).startNode ∈ mfam G ⟨Sum.inl q, hnc⟩ ∧
    portEdge G ((classPiece G q).startNode) ⟨Sum.inl q, hnc⟩ =
      (classPiece G q).firstEdge := by
  constructor
  · by_cases h3 : 3 ≤ (classPiece G q).walk.length
    · simp only [mfam, if_pos h3]
      exact Sym2.mem_mk_left _ _
    · simp only [mfam, if_neg h3]
      exact Sym2.mem_mk_left _ _
  · simp only [portEdge]
    exact if_pos trivial

variable (G) in
/-- On a long chain, the R-half contains the end site, with the last
edge as its port there. -/
lemma member_port_end_long {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    (classPiece G q).endNode ∈ mfam G ⟨Sum.inr q, ⟨hnc, h3⟩⟩ ∧
    portEdge G ((classPiece G q).endNode) ⟨Sum.inr q, ⟨hnc, h3⟩⟩ =
      (classPiece G q).lastEdge := by
  constructor
  · simp only [mfam]
    exact Sym2.mem_mk_right _ _
  · simp only [portEdge]

variable (G) in
/-- On a short chain, the whole member contains the end site, with the
last edge as its port there (the start site differs from the end site,
so the port selector picks the last edge). -/
lemma member_port_end_short {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    (classPiece G q).endNode ∈ mfam G ⟨Sum.inl q, hnc⟩ ∧
    portEdge G ((classPiece G q).endNode) ⟨Sum.inl q, hnc⟩ =
      (classPiece G q).lastEdge := by
  have hne := (classPiece G q).startNode_ne_endNode
    ((classPiece G q).a_ne_b_of_length_lt_three (by omega))
  constructor
  · simp only [mfam, if_neg h3]
    exact Sym2.mem_mk_right _ _
  · simp only [portEdge]
    rw [if_neg hne]

variable (G) in
/-- **Port coverage** (pretest R-E): every edge at a vertex of
degree ≠ 2 is the port edge of a member through the corresponding
group site.  With `port_member_unique`, "the member of a port" is
well-defined — the future port coloring gives every junction-incident
edge its member's Shannon color, which is the `rainbow` field's
input. -/
theorem exists_port_member {v : V} (hdv : G.degree v ≠ 2) {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hv : v ∈ e) :
    ∃ m : Member G, nodeAt G v e ∈ mfam G m ∧
      portEdge G (nodeAt G v e) m = e := by
  have hnc : ¬(pieceOf G e he).IsCycle := by
    intro hcyc
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    have hmem : s(v, w) ∈ (pieceOf G e he).walk.edges := by
      rw [← hw]
      exact mem_pieceOf G he
    exact hdv (((pieceOf G e he).cycle_spec hcyc).2 v
      ((pieceOf G e he).walk.fst_mem_support_of_mem_edges hmem))
  rcases pieceOf_port G he hv hdv with ⟨hva, hef⟩ | ⟨hvb, hel⟩
  · -- v is the start: the whole/L member through the start site
    obtain ⟨hmem, hport⟩ := member_port_start G
      (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc
    have hnd : nodeAt G v e = (pieceOf G e he).startNode :=
      congrArg₂ (nodeAt G) hva hef
    refine ⟨⟨Sum.inl ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
      hnc⟩, ?_, ?_⟩
    · rw [hnd]
      exact hmem
    · rw [hnd]
      exact hport.trans hef.symm
  · -- v is the end: the R-half (long) or the whole member (short)
    have hnd : nodeAt G v e = (pieceOf G e he).endNode :=
      congrArg₂ (nodeAt G) hvb hel
    by_cases h3 : 3 ≤ (pieceOf G e he).walk.length
    · obtain ⟨hmem, hport⟩ := member_port_end_long G
        (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc h3
      refine ⟨⟨Sum.inr ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
        ⟨hnc, h3⟩⟩, ?_, ?_⟩
      · rw [hnd]
        exact hmem
      · rw [hnd]
        exact hport.trans hel.symm
    · obtain ⟨hmem, hport⟩ := member_port_end_short G
        (q := ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩) hnc h3
      refine ⟨⟨Sum.inl ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩,
        hnc⟩, ?_, ?_⟩
      · rw [hnd]
        exact hmem
      · rw [hnd]
        exact hport.trans hel.symm

/-! ### The Shannon member coloring -/

/-- **The member coloring exists** (`shannon_six_indexed` on the real
M-family of an arbitrary graph): a 6-coloring of the members, distinct
whenever two members share an M-node.  Specialized downstream: at a
group site this is the rainbow input (distinct port colors within a
group), at a middle node the l = 3 port distinctness `isFill_exists`
needs.  All finiteness/decidability is supplied classically — the
linkage quotient is finite but not constructively enumerable here. -/
theorem exists_member_coloring (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ col : Member G → Fin 6, ∀ m m' : Member G, m ≠ m' →
      ∀ a : MNode G, a ∈ mfam G m → a ∈ mfam G m' → col m ≠ col m' := by
  classical
  haveI : Fintype (Quotient (linkSetoid G)) := Fintype.ofFinite _
  haveI : Fintype (MNode G) := Fintype.ofFinite _
  haveI : Fintype (Member G) := Fintype.ofFinite _
  refine shannon_six_indexed (mfam G) (mfam_not_isDiag G) ?_
  intro a
  rcases a with ⟨v, k⟩ | q
  · exact mfam_count_junction G v k
  · exact mfam_count_middle G q

/-! ### Honest scope note

Banked here: the per-vertex grouping facts (`glueIx`), the piece choice
per linkage class (`classPiece`/`pieceOf`, class-constant), the port
fact transported (`pieceOf_port`), the M-node/member family with
looplessness and the per-node ≤ 4 bound, and the Shannon member
coloring `exists_member_coloring` — step 2 of the C6L3/C7L3 handoff.
NOT yet formalized (steps 3–5, still owed): the port coloring and its
`satSet` agreement, the fills (`isFill_exists` instantiation), the
pure-cycle coloring hookup, the global coloring and the
`IsGlueColoring` bundle.  `maj_le_six` remains `proof_wanted`. -/

end

/-! ###### source file: SMaj/Six/Final.lean ###### -/
section
/-
SMaj/Six/Final.lean — steps 3–5 of the `maj_le_six` assembly: the port
coloring, the fills, the global coloring, the `IsGlueColoring` bundle,
and the headline theorem `maj_le_six` (campaign C9, lens
C9L3-lean-assembly, 2026-07-08).

`SMaj/Six/Assembly.lean` (C8) banked the M-family and the Shannon member
coloring `exists_member_coloring`; `SMaj/Six/Partition.lean` (C8) the
slot calculus; `SMaj/Six/Fill.lean` (C3) the fill lemma;
`SMaj/Six/Construct.lean` (C6) the pure-cycle pattern;
`SMaj/Six/Glue.lean` (C5) the row dispatch `maj_le_six_of_glue`.  This
file composes them:

* `portColor` — the PORT-STAGE coloring: a junction-incident edge gets
  the Shannon color of its (unique) port member; defined per linkage
  class by slot so that the two ends of an l = 1 chain and the two
  ports of an l = 2 chain agree BY CONSTRUCTION (the whole-chain member
  is one term — the C8L3 risk note (ii) discharged as designed);
* `FxOf`/`FyOf` — the fill's saturated sets, computed from `portColor`
  at junction chain ends (`card_satSet_le_two` gives ≤ 2) and EMPTY at
  pendant ends (degree < 3; the `chain_end` field never looks there);
* `fillFun` — `isFill_exists` instantiated per chain class of length
  ≥ 3, ports pinned to the two half colors (distinct at every length
  ≥ 3 — the halves share the class's middle node, `col_inl_ne_inr`);
* `cycleFun` — `exists_cycle_distance2` per pure cycle;
* `glueColor` — the global coloring, per class by slot index
  (`List.idxOf` in the canonical piece's edge list, pinned by
  `edges_nodup`);
* the satSet agreement (`satSet_glueColor_eq`): the final and
  port-stage saturated sets agree at junctions, because every side
  edge there is a port (`eq_first_or_last`) and fills pin port slots
  to the port colors — the fill ↔ satSet circularity broken exactly as
  the C8L3 risk note (i) prescribed;
* the four `IsGlueColoring` fields (`glueColor_rainbow`,
  `groups_glueIx_le`, `glueColor_chain_end`, `glueColor_interior`) and
  `exists_isGlueColoring` — NO admissibility needed for the
  construction itself;
* **`maj_le_six`** — the T1 headline, now a THEOREM through
  `maj_le_six_of_glue` (the former `proof_wanted` in
  `SMaj/Six/Targets.lean` is deleted).

Machine pretest BEFORE proving (standing rule):
`lenses/C9L3-lean-assembly/pretest_final.py`, exit 0 — S-A..S-E pin
this file's definitions verbatim on 34,165 graphs (EXHAUSTIVE all
labeled graphs n ≤ 6, classics incl. a 9-arm star of chains and
subdivided K₄, 300 randoms n ≤ 14): fill sat-set cards ≤ 2 with the
pendant-∅ choice, p ≠ q at long chains, IsFill existence, satSet
agreement, all four bundle fields, strong majority on all 28,070
admissible corpus graphs, and the cycle wraparound arithmetic.
-/


open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### List slot bookkeeping -/

/-- On a nodup list, the index of the value at a position is that
position — `idxOf` inverts `getElem`. -/
lemma idxOf_eq_of_getElem {α : Type*} [DecidableEq α] {l : List α}
    (hnd : l.Nodup) {i : ℕ} (hi : i < l.length) {a : α}
    (ha : l[i] = a) : l.idxOf a = i := by
  have hmem : a ∈ l := ha ▸ List.getElem_mem hi
  have hlt : l.idxOf a < l.length := List.idxOf_lt_length_of_mem hmem
  have h2 : l[l.idxOf a]'hlt = l[i]'hi := by
    rw [List.getElem_idxOf hlt, ha]
  exact hnd.getElem_inj_iff.mp h2

/-! ### Piece-level cycle transports (the `IsPiece` cycle lemmas need a
closed walk `G.Walk x x`; a `Piece` carries `G.Walk P.a P.b` with
`P.a = P.b` only propositionally) -/

namespace Piece

omit [DecidableEq V] in
/-- Pure-cycle pieces have at least 3 edges. -/
lemma three_le_length_of_cycle (P : Piece G) (h : P.IsCycle) :
    3 ≤ P.walk.length := by
  obtain ⟨hab, -⟩ := P.cycle_spec h
  obtain ⟨a, b, w, hp⟩ := P
  have hab' : a = b := hab
  subst hab'
  exact three_le_length_of_closed hp.trail hp.ne

/-- `IsPiece.other_edge_slot_of_cycle`, transported to a `Piece`. -/
lemma cycle_slot (P : Piece G) (hcyc : P.IsCycle) {i : ℕ}
    (hi : i < P.walk.edges.length) {v : V} (hv : v ∈ P.walk.edges[i])
    {f : Sym2 V} (hf : f ∈ P.walk.edges) (hvf : v ∈ f)
    (hne : f ≠ P.walk.edges[i]) :
    (v = P.walk.getVert i ∧
      ∃ h : (i + P.walk.edges.length - 1) % P.walk.edges.length <
          P.walk.edges.length,
        f = P.walk.edges[(i + P.walk.edges.length - 1) %
          P.walk.edges.length]) ∨
    (v = P.walk.getVert (i + 1) ∧
      ∃ h : (i + 1) % P.walk.edges.length < P.walk.edges.length,
        f = P.walk.edges[(i + 1) % P.walk.edges.length]) := by
  obtain ⟨hab, hall⟩ := P.cycle_spec hcyc
  obtain ⟨a, b, w, hp⟩ := P
  have hab' : a = b := hab
  subst hab'
  exact IsPiece.other_edge_slot_of_cycle hp hall hi hv hf hvf hne

end Piece

/-! ### The class of an edge -/

variable (G) in
/-- The linkage class of an edge, as an `EdgeClass` (the index type of
the canonical pieces). -/
noncomputable def edgeClassOf {e : Sym2 V} (he : e ∈ G.edgeSet) :
    EdgeClass G :=
  ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩

variable (G) in
/-- An edge on a class's piece has that class (`pieceOf G e he` is
definitionally `classPiece G (edgeClassOf G he)`). -/
lemma edgeClassOf_eq {q : EdgeClass G} {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hm : e ∈ (classPiece G q).walk.edges) : edgeClassOf G he = q :=
  Subtype.ext (classPiece_class_eq G hm)

/-! ### The Shannon member-coloring property, and the two half colors -/

variable (G) in
/-- The property `exists_member_coloring` delivers: distinct members
sharing an M-node get distinct colors. -/
def IsMemberColoring (col : Member G → Fin 6) : Prop :=
  ∀ m m' : Member G, m ≠ m' → ∀ a : MNode G,
    a ∈ mfam G m → a ∈ mfam G m' → col m ≠ col m'

/-- The two halves of a long chain get DISTINCT colors: they share the
class's middle node (this is the l = 3 port-distinctness input of the
fill, valid at every length ≥ 3). -/
lemma col_inl_ne_inr {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    col ⟨Sum.inl q, hc⟩ ≠ col ⟨Sum.inr q, hc, h3⟩ := by
  apply hcol _ _ (by simp) (Sum.inr q.1)
  · simp only [mfam, if_pos h3]
    exact Sym2.mem_mk_right _ _
  · simp only [mfam]
    exact Sym2.mem_mk_left _ _

/-! ### The port-stage coloring -/

/-- `IsCycle` is a decidable degree test. -/
instance (P : Piece G) : Decidable P.IsCycle :=
  inferInstanceAs (Decidable (G.degree P.a = 2))

/-- Port-stage class coloring: slot 0 (the first edge) gets the
whole/L-member color, later slots the R-member color on long chains;
short chains are monochromatic in their whole-member color.  Values on
cycle classes and on interior slots are garbage — no junction ever
reads them. -/
noncomputable def portClassColor (col : Member G → Fin 6)
    (q : EdgeClass G) (i : ℕ) : Fin 6 :=
  if hc : (classPiece G q).IsCycle then 0
  else if h3 : 3 ≤ (classPiece G q).walk.length then
    if i = 0 then col ⟨Sum.inl q, hc⟩ else col ⟨Sum.inr q, hc, h3⟩
  else col ⟨Sum.inl q, hc⟩

/-- **The port-stage coloring**: every edge is colored through its
linkage class by its slot in the canonical piece.  On junction-incident
edges (= ports, `eq_first_or_last`) this is the Shannon color of the
port member; the fill's saturated sets are computed from it, breaking
the fill ↔ satSet circularity. -/
noncomputable def portColor (col : Member G → Fin 6) (e : Sym2 V) :
    Fin 6 :=
  if he : e ∈ G.edgeSet then
    portClassColor col (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

/-! ### The fill's saturated sets -/

/-- The start-end saturated set of a chain class: the port-stage satSet
at the start junction, EMPTY at a pendant/low-degree start (the
`chain_end` field requires degree ≥ 3, so the empty choice is never
consulted there). -/
noncomputable def FxOf (col : Member G → Fin 6) (q : EdgeClass G) :
    Finset (Fin 6) :=
  if 3 ≤ G.degree (classPiece G q).a then
    satSet G (portColor col) (classPiece G q).a (classPiece G q).walk.snd
  else ∅

/-- Mirror of `FxOf` at the far end. -/
noncomputable def FyOf (col : Member G → Fin 6) (q : EdgeClass G) :
    Finset (Fin 6) :=
  if 3 ≤ G.degree (classPiece G q).b then
    satSet G (portColor col) (classPiece G q).b
      (classPiece G q).walk.penultimate
  else ∅

lemma FxOf_card_le (col : Member G → Fin 6) (q : EdgeClass G) :
    #(FxOf col q) ≤ 2 := by
  unfold FxOf
  split_ifs with h
  · have hadj : G.Adj (classPiece G q).a (classPiece G q).walk.snd :=
      G.mem_edgeSet.mp ((classPiece G q).walk.edges_subset_edgeSet
        (classPiece G q).firstEdge_mem)
    exact card_satSet_le_two hadj (by omega)
  · simp

lemma FyOf_card_le (col : Member G → Fin 6) (q : EdgeClass G) :
    #(FyOf col q) ≤ 2 := by
  unfold FyOf
  split_ifs with h
  · have hadj : G.Adj (classPiece G q).walk.penultimate
        (classPiece G q).b :=
      G.mem_edgeSet.mp ((classPiece G q).walk.edges_subset_edgeSet
        (classPiece G q).lastEdge_mem)
    exact card_satSet_le_two hadj.symm (by omega)
  · simp

/-! ### The per-class colorings: fill, cycle pattern, and the composite -/

/-- **The fill of a long chain class** (`isFill_exists` instantiated):
ports pinned to the two half colors, saturated sets `FxOf`/`FyOf`. -/
noncomputable def fillFun {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G)
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) : ℕ → Fin 6 :=
  (isFill_exists (by rw [Fintype.card_fin]; omega) h3
    (col ⟨Sum.inl q, hc⟩) (col ⟨Sum.inr q, hc, h3⟩)
    (fun _ => col_inl_ne_inr hcol hc h3)
    (FxOf_card_le col q) (FyOf_card_le col q)).choose

lemma fillFun_isFill {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G)
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    IsFill (classPiece G q).walk.length (col ⟨Sum.inl q, hc⟩)
      (col ⟨Sum.inr q, hc, h3⟩) (FxOf col q) (FyOf col q)
      (fillFun hcol q hc h3) :=
  (isFill_exists (by rw [Fintype.card_fin]; omega) h3
    (col ⟨Sum.inl q, hc⟩) (col ⟨Sum.inr q, hc, h3⟩)
    (fun _ => col_inl_ne_inr hcol hc h3)
    (FxOf_card_le col q) (FyOf_card_le col q)).choose_spec

/-- **The pure-cycle pattern** (`exists_cycle_distance2`), indexed by
edge-list slots. -/
noncomputable def cycleFun (q : EdgeClass G)
    (hc : (classPiece G q).IsCycle) : ℕ → ℕ :=
  (exists_cycle_distance2 (classPiece G q).walk.edges.length
    (by rw [(classPiece G q).walk.length_edges]
        exact (classPiece G q).three_le_length_of_cycle hc)).choose

lemma cycleFun_spec (q : EdgeClass G) (hc : (classPiece G q).IsCycle) :
    (∀ i, cycleFun q hc i < 3) ∧
      ∀ i < (classPiece G q).walk.edges.length,
        cycleFun q hc i ≠
          cycleFun q hc ((i + 2) % (classPiece G q).walk.edges.length) :=
  (exists_cycle_distance2 (classPiece G q).walk.edges.length
    (by rw [(classPiece G q).walk.length_edges]
        exact (classPiece G q).three_le_length_of_cycle hc)).choose_spec

/-- The 3-color cycle pattern embedded in the 6-color palette. -/
def embed6 (n : ℕ) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by omega)⟩

lemma embed6_ne {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : a ≠ b) :
    embed6 a ≠ embed6 b := by
  intro hab
  apply h
  have h' : a % 6 = b % 6 := congrArg Fin.val hab
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'

/-- The per-class slot coloring of the FINAL coloring: cycle pattern on
pure cycles, fill on long chains, monochromatic whole-member color on
short chains. -/
noncomputable def classColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G) (i : ℕ) : Fin 6 :=
  if hc : (classPiece G q).IsCycle then embed6 (cycleFun q hc i)
  else if h3 : 3 ≤ (classPiece G q).walk.length then fillFun hcol q hc h3 i
  else col ⟨Sum.inl q, hc⟩

/-- **The global coloring** of the ≤ 6 construction. -/
noncomputable def glueColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (e : Sym2 V) : Fin 6 :=
  if he : e ∈ G.edgeSet then
    classColor hcol (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

/-! ### Access lemmas: colors through class and slot -/

lemma glueColor_eq_classColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G} {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hm : e ∈ (classPiece G q).walk.edges) :
    glueColor hcol e =
      classColor hcol q ((classPiece G q).walk.edges.idxOf e) := by
  unfold glueColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

lemma portColor_eq_portClassColor (col : Member G → Fin 6)
    {q : EdgeClass G} {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hm : e ∈ (classPiece G q).walk.edges) :
    portColor col e =
      portClassColor col q ((classPiece G q).walk.edges.idxOf e) := by
  unfold portColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

lemma idxOf_firstEdge (P : Piece G) :
    P.walk.edges.idxOf P.firstEdge = 0 := by
  obtain ⟨h0, he⟩ := P.firstEdge_eq
  exact idxOf_eq_of_getElem P.piece.trail.edges_nodup h0 he

lemma idxOf_lastEdge (P : Piece G) :
    P.walk.edges.idxOf P.lastEdge = P.walk.edges.length - 1 := by
  obtain ⟨hl, he⟩ := P.lastEdge_eq
  exact idxOf_eq_of_getElem P.piece.trail.edges_nodup hl he

lemma classColor_of_short {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) (i : ℕ) :
    classColor hcol q i = col ⟨Sum.inl q, hc⟩ := by
  unfold classColor
  rw [dif_neg hc, dif_neg h3]

lemma classColor_of_fill {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) (i : ℕ) :
    classColor hcol q i = fillFun hcol q hc h3 i := by
  unfold classColor
  rw [dif_neg hc, dif_pos h3]

lemma classColor_of_cycle {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : (classPiece G q).IsCycle) (i : ℕ) :
    classColor hcol q i = embed6 (cycleFun q hc i) := by
  unfold classColor
  rw [dif_pos hc]

/-! ### Port values of the two colorings -/

lemma glueColor_firstEdge {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle) :
    glueColor hcol (classPiece G q).firstEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).firstEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm, idxOf_firstEdge]
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · rw [classColor_of_fill hcol hc h3]
    exact (fillFun_isFill hcol q hc h3).1
  · exact classColor_of_short hcol hc h3 0

lemma glueColor_lastEdge_long {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    glueColor hcol (classPiece G q).lastEdge =
      col ⟨Sum.inr q, hc, h3⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm, idxOf_lastEdge,
    (classPiece G q).walk.length_edges, classColor_of_fill hcol hc h3]
  exact (fillFun_isFill hcol q hc h3).2.1

lemma glueColor_lastEdge_short {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    glueColor hcol (classPiece G q).lastEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm]
  exact classColor_of_short hcol hc h3 _

lemma portColor_firstEdge (col : Member G → Fin 6) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle) :
    portColor col (classPiece G q).firstEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).firstEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm, idxOf_firstEdge]
  unfold portClassColor
  rw [dif_neg hc]
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · rw [dif_pos h3, if_pos rfl]
  · rw [dif_neg h3]

lemma portColor_lastEdge_long (col : Member G → Fin 6) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    portColor col (classPiece G q).lastEdge =
      col ⟨Sum.inr q, hc, h3⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm, idxOf_lastEdge]
  unfold portClassColor
  rw [dif_neg hc, dif_pos h3, if_neg]
  have := (classPiece G q).walk.length_edges
  omega

lemma portColor_lastEdge_short (col : Member G → Fin 6)
    {q : EdgeClass G} (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    portColor col (classPiece G q).lastEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm]
  unfold portClassColor
  rw [dif_neg hc, dif_neg h3]

/-! ### Both colorings give a port its member's Shannon color -/

/-- The final color of a member's port edge is the member's Shannon
color (any member, through any group site it contains). -/
lemma glueColor_portEdge {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {v : V}
    {k : Fin (Fintype.card V + 1)} {m : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    glueColor hcol (portEdge G (Sum.inl (v, k)) m) = col m := by
  obtain ⟨mv, hs⟩ := m
  rcases mv with q | q
  · by_cases hstart : (classPiece G q).startNode = Sum.inl (v, k)
    · simp only [portEdge, if_pos hstart]
      exact glueColor_firstEdge hcol hs
    · have h3 : ¬3 ≤ (classPiece G q).walk.length := by
        intro h3
        simp only [mfam, if_pos h3] at hm
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hstart h.symm
        · exact absurd h (by simp)
      simp only [portEdge, if_neg hstart]
      exact glueColor_lastEdge_short hcol hs h3
  · simp only [portEdge]
    exact glueColor_lastEdge_long hcol hs.1 hs.2

/-- Port-stage mirror of `glueColor_portEdge`. -/
lemma portColor_portEdge (col : Member G → Fin 6) {v : V}
    {k : Fin (Fintype.card V + 1)} {m : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    portColor col (portEdge G (Sum.inl (v, k)) m) = col m := by
  obtain ⟨mv, hs⟩ := m
  rcases mv with q | q
  · by_cases hstart : (classPiece G q).startNode = Sum.inl (v, k)
    · simp only [portEdge, if_pos hstart]
      exact portColor_firstEdge col hs
    · have h3 : ¬3 ≤ (classPiece G q).walk.length := by
        intro h3
        simp only [mfam, if_pos h3] at hm
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hstart h.symm
        · exact absurd h (by simp)
      simp only [portEdge, if_neg hstart]
      exact portColor_lastEdge_short col hs h3
  · simp only [portEdge]
    exact portColor_lastEdge_long col hs.1 hs.2

/-! ### Junction agreement and the satSet agreement -/

/-- On junction-incident edges the final and port-stage colorings
agree (both give the port member's Shannon color). -/
lemma glueColor_eq_portColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {e : Sym2 V} (he : e ∈ G.edgeSet)
    {v : V} (hv : v ∈ e) (hdv : G.degree v ≠ 2) :
    glueColor hcol e = portColor col e := by
  obtain ⟨m, hm, hp⟩ := exists_port_member G hdv he hv
  have hm' : (Sum.inl (v, ⟨glueIx G v e, glueIx_lt v e⟩) : MNode G) ∈
      mfam G m := hm
  have hp' : portEdge G
      (Sum.inl (v, ⟨glueIx G v e, glueIx_lt v e⟩) : MNode G) m = e := hp
  calc glueColor hcol e
      = col m := by rw [← hp']; exact glueColor_portEdge hcol hm'
    _ = portColor col e := by rw [← hp']
                              exact (portColor_portEdge col hm').symm

/-- **The satSet agreement** (C8L3 risk note (i) discharged): the
saturated sets of the final and port-stage colorings agree at every
junction — every side edge there is junction-incident, where the two
colorings agree. -/
lemma satSet_glueColor_eq {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {x w : V} (hdx : G.degree x ≠ 2) :
    satSet G (glueColor hcol) x w = satSet G (portColor col) x w := by
  have hside : ∀ α : Fin 6,
      {f ∈ side G x w | glueColor hcol f = α} =
        {f ∈ side G x w | portColor col f = α} := by
    intro α
    apply filter_congr
    intro f hf
    have hf2 : f ∈ G.incidenceSet x := (mem_side.mp hf).2
    rw [glueColor_eq_portColor hcol hf2.1 hf2.2 hdx]
  unfold satSet
  apply filter_congr
  intro α _
  rw [hside α]

/-! ### The four bundle fields -/

/-- **Rainbow** (field 1): at junctions via port members + Shannon
distinctness at the shared group site; at degree ≤ 2 via singleton
groups. -/
lemma glueColor_rainbow {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) :
    IsRainbow G (glueIx G) (glueColor hcol) := by
  intro v f₁ h₁ f₂ h₂ hix hc
  by_cases hdeg : 3 ≤ G.degree v
  · have hdv : G.degree v ≠ 2 := by omega
    have hf₁ := mem_incFinset.mp h₁
    have hf₂ := mem_incFinset.mp h₂
    obtain ⟨m₁, hm₁, hp₁⟩ := exists_port_member G hdv hf₁.1 hf₁.2
    obtain ⟨m₂, hm₂, hp₂⟩ := exists_port_member G hdv hf₂.1 hf₂.2
    have hnd : nodeAt G v f₁ = nodeAt G v f₂ := by
      unfold nodeAt
      exact congrArg Sum.inl (congrArg (Prod.mk v) (Fin.ext hix))
    have hc₁ : glueColor hcol f₁ = col m₁ := by
      rw [← hp₁]; exact glueColor_portEdge hcol hm₁
    have hc₂ : glueColor hcol f₂ = col m₂ := by
      rw [← hp₂]; exact glueColor_portEdge hcol hm₂
    have hm12 : m₁ = m₂ := by
      by_contra hne
      exact hcol m₁ m₂ hne (nodeAt G v f₁) hm₁ (by rw [hnd]; exact hm₂)
        (by rw [← hc₁, ← hc₂]; exact hc)
    rw [← hp₁, ← hp₂, hnd, hm12]
  · exact glueIx_inj_low hdeg h₁ h₂ hix

/-- **Chain end** (field 3): short chains are monochromatic (left
disjunct); on long chains the inward edge sits at slot 1 (resp.
length − 2), where the fill avoids the port-stage satSet — equal to the
final satSet by the agreement lemma. -/
lemma glueColor_chain_end {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {x w y : V} (hxw : G.Adj x w)
    (hwy : G.Adj w y) (hxy : x ≠ y) (hdw : G.degree w = 2)
    (hdx3 : 3 ≤ G.degree x) :
    glueColor hcol s(x, w) = glueColor hcol s(w, y) ∨
      glueColor hcol s(w, y) ∉ satSet G (glueColor hcol) x w := by
  have he : s(x, w) ∈ G.edgeSet := G.mem_edgeSet.mpr hxw
  have hey : s(w, y) ∈ G.edgeSet := G.mem_edgeSet.mpr hwy
  set q : EdgeClass G := edgeClassOf G he with hq
  have hmem : s(x, w) ∈ (classPiece G q).walk.edges := mem_pieceOf G he
  have hdx2 : G.degree x ≠ 2 := by omega
  have hwsup : w ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.snd_mem_support_of_mem_edges hmem
  have hnc : ¬(classPiece G q).IsCycle := by
    intro hcyc
    have hxsup : x ∈ (classPiece G q).walk.support :=
      (classPiece G q).walk.fst_mem_support_of_mem_edges hmem
    exact hdx2 (((classPiece G q).cycle_spec hcyc).2 x hxsup)
  have hwy_mem : s(w, y) ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two hwsup hdw _
      (mem_incFinset.mpr ⟨hwy, Sym2.mem_mk_left _ _⟩)
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · right
    rcases (classPiece G q).piece.eq_first_or_last hmem
        (Sym2.mem_mk_left x w) hdx2 with ⟨hxa, hef⟩ | ⟨hxb, hel⟩
    · -- x is the start: the inward edge is slot 1, avoiding Fx
      have hw : w = (classPiece G q).walk.snd := by
        rcases Sym2.eq_iff.mp hef with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2
        · exact absurd (hxa.trans h2.symm) (G.ne_of_adj hxw)
      obtain ⟨h1len, he1⟩ := (classPiece G q).piece.edges_one_eq
        (by rw [← hxa]; exact hdx2) (by rw [← hw]; exact hdw)
        (by rw [← hw]; exact hwy) (by rw [← hxa]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) = 1 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          h1len (by rw [he1, ← hw])
      have hcy : glueColor hcol s(w, y) = fillFun hcol q hnc h3 1 := by
        rw [glueColor_eq_classColor hcol hey hwy_mem, hidx,
          classColor_of_fill hcol hnc h3]
      rw [hcy, satSet_glueColor_eq hcol hdx2, hxa, hw]
      have hnotin := (fillFun_isFill hcol q hnc h3).2.2.2.1
      unfold FxOf at hnotin
      rwa [if_pos (hxa ▸ hdx3)] at hnotin
    · -- x is the end: the inward edge is slot length − 2, avoiding Fy
      have hw : w = (classPiece G q).walk.penultimate := by
        rcases Sym2.eq_iff.mp hel with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd (hxb.trans h2.symm) (G.ne_of_adj hxw)
        · exact h2
      obtain ⟨hslen, hes⟩ :=
        (classPiece G q).piece.edges_length_sub_two_eq
          (by rw [← hxb]; exact hdx2) (by rw [← hw]; exact hdw)
          (by rw [← hw]; exact hwy) (by rw [← hxb]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) =
          (classPiece G q).walk.edges.length - 2 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          hslen (by rw [hes, ← hw])
      have hcy : glueColor hcol s(w, y) =
          fillFun hcol q hnc h3 ((classPiece G q).walk.length - 2) := by
        rw [glueColor_eq_classColor hcol hey hwy_mem, hidx,
          (classPiece G q).walk.length_edges,
          classColor_of_fill hcol hnc h3]
      rw [hcy, satSet_glueColor_eq hcol hdx2, hxb, hw]
      have hnotin := (fillFun_isFill hcol q hnc h3).2.2.2.2
      unfold FyOf at hnotin
      rwa [if_pos (hxb ▸ hdx3)] at hnotin
  · -- short chain: monochromatic
    left
    rw [glueColor_eq_classColor hcol he hmem,
      glueColor_eq_classColor hcol hey hwy_mem,
      classColor_of_short hcol hnc h3 _, classColor_of_short hcol hnc h3 _]

/-- **Interior** (field 4): both sides of an all-degree-2 row are the
edges two slots apart on the same piece — distinct under the fill's
(F-a) on chains and under the distance-2 pattern on pure cycles. -/
lemma glueColor_interior {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2) {f : Sym2 V}
    (hf : f ∈ side G u v) {g : Sym2 V} (hg : g ∈ side G v u) :
    glueColor hcol f ≠ glueColor hcol g := by
  have he : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr huv
  set q : EdgeClass G := edgeClassOf G he with hq
  have hmem : s(u, v) ∈ (classPiece G q).walk.edges := mem_pieceOf G he
  have hfside := mem_side.mp hf
  have hgside := mem_side.mp hg
  have husup : u ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.fst_mem_support_of_mem_edges hmem
  have hvsup : v ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.snd_mem_support_of_mem_edges hmem
  have hfP : f ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two husup hdu f
      (mem_incFinset.mpr hfside.2)
  have hgP : g ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two hvsup hdv g
      (mem_incFinset.mpr hgside.2)
  have hfe : f ∈ G.edgeSet := hfside.2.1
  have hge : g ∈ G.edgeSet := hgside.2.1
  have hnd := (classPiece G q).piece.trail.edges_nodup
  have hi : (classPiece G q).walk.edges.idxOf s(u, v) <
      (classPiece G q).walk.edges.length :=
    List.idxOf_lt_length_of_mem hmem
  set i := (classPiece G q).walk.edges.idxOf s(u, v) with hidef
  have hei : (classPiece G q).walk.edges[i] = s(u, v) :=
    List.getElem_idxOf hi
  have heq : s(u, v) = s((classPiece G q).walk.getVert i,
      (classPiece G q).walk.getVert (i + 1)) := by
    rw [← hei]
    exact edges_getElem _ hi
  have hor := Sym2.eq_iff.mp heq
  have hgv_ne : (classPiece G q).walk.getVert i ≠
      (classPiece G q).walk.getVert (i + 1) := by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact G.ne_of_adj huv
    · rw [← h1, ← h2]; exact (G.ne_of_adj huv).symm
  by_cases hcyc : (classPiece G q).IsCycle
  · -- pure cycle: the two sides are the previous and next modular slots
    have h3L : 3 ≤ (classPiece G q).walk.edges.length := by
      rw [(classPiece G q).walk.length_edges]
      exact (classPiece G q).three_le_length_of_cycle hcyc
    have hfslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_left u v) hfP hfside.2.2
      (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_right u v) hgP hgside.2.2
      (by rw [hei, Sym2.eq_swap]; exact hgside.1)
    have hspec := cycleFun_spec q hcyc
    have harith : ∀ j : ℕ,
        ((j + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length + 2) %
          (classPiece G q).walk.edges.length =
        (j + 1) % (classPiece G q).walk.edges.length := by
      intro j
      rw [Nat.mod_add_mod,
        show j + (classPiece G q).walk.edges.length - 1 + 2 =
          j + 1 + (classPiece G q).walk.edges.length by omega,
        Nat.add_mod_right]
    have hcolor : ∀ {h : Sym2 V} (hhP : h ∈ (classPiece G q).walk.edges)
        (hhe : h ∈ G.edgeSet) {j : ℕ}
        (hj : j < (classPiece G q).walk.edges.length)
        (hh : h = (classPiece G q).walk.edges[j]),
        glueColor hcol h = embed6 (cycleFun q hcyc j) := by
      intro h hhP hhe j hj hh
      rw [glueColor_eq_classColor hcol hhe hhP,
        idxOf_eq_of_getElem hnd hj hh.symm, classColor_of_cycle hcol hcyc]
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · -- u near, v far: f = previous slot, g = next slot
      obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨-, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hcontra) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hcontra) hgv_ne.symm
        · exact hh
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      apply embed6_ne (hspec.1 _) (hspec.1 _)
      have := hspec.2 ((i + (classPiece G q).walk.edges.length - 1) %
        (classPiece G q).walk.edges.length)
        (Nat.mod_lt _ (by omega))
      rwa [harith i] at this
    · -- u far, v near: f = next slot, g = previous slot
      obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hcontra) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨-, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hcontra) hgv_ne
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      apply embed6_ne (hspec.1 _) (hspec.1 _)
      have := hspec.2 ((i + (classPiece G q).walk.edges.length - 1) %
        (classPiece G q).walk.edges.length)
        (Nat.mod_lt _ (by omega))
      rw [harith i] at this
      exact (Ne.symm this)
  · -- chain: the two sides are slots i − 1 and i + 1, distinct by (F-a)
    have hends := (classPiece G q).chain_ends hcyc
    have hLe := (classPiece G q).walk.length_edges
    have hfslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_left u v) hdu
      hfP hfside.2.2 (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_right u v) hdv
      hgP hgside.2.2 (by rw [hei, Sym2.eq_swap]; exact hgside.1)
    have hcolor : ∀ {h : Sym2 V} (hhP : h ∈ (classPiece G q).walk.edges)
        (hhe : h ∈ G.edgeSet) {j : ℕ}
        (hj : j < (classPiece G q).walk.edges.length)
        (hh : h = (classPiece G q).walk.edges[j])
        (h3 : 3 ≤ (classPiece G q).walk.length),
        glueColor hcol h = fillFun hcol q hcyc h3 j := by
      intro h hhP hhe j hj hh h3
      rw [glueColor_eq_classColor hcol hhe hhP,
        idxOf_eq_of_getElem hnd hj hh.symm,
        classColor_of_fill hcol hcyc h3]
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · -- u near, v far
      have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hua : u = (classPiece G q).a := by
          rw [hu, hi0, Walk.getVert_zero]
        exact hends.1 (hua ▸ hdu)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hvb : v = (classPiece G q).b := by
          rw [hv', hieq, Walk.getVert_length]
        exact hends.2 (hvb ▸ hdv)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      obtain ⟨hj1, hf1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i - 1] := by
        rcases hfslot with ⟨-, -, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hcontra) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i + 1] := by
        rcases hgslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hcontra) hgv_ne.symm
        · exact hh
      rw [hcolor hfP hfe hj1 hf1 h3, hcolor hgP hge hj2 hg1 h3]
      have hfa := (fillFun_isFill hcol q hcyc h3).2.2.1 (i - 1)
        (by omega)
      rwa [show i - 1 + 2 = i + 1 by omega] at hfa
    · -- u far, v near
      have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hva : v = (classPiece G q).a := by
          rw [hv', hi0, Walk.getVert_zero]
        exact hends.1 (hva ▸ hdv)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hub : u = (classPiece G q).b := by
          rw [hu, hieq, Walk.getVert_length]
        exact hends.2 (hub ▸ hdu)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      obtain ⟨hj1, hf1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i + 1] := by
        rcases hfslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hcontra) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i - 1] := by
        rcases hgslot with ⟨-, -, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hcontra) hgv_ne
      rw [hcolor hfP hfe hj1 hf1 h3, hcolor hgP hge hj2 hg1 h3]
      have hfa := (fillFun_isFill hcol q hcyc h3).2.2.1 (i - 1)
        (by omega)
      rw [show i - 1 + 2 = i + 1 by omega] at hfa
      exact (Ne.symm hfa)

/-! ### The construction theorem and the headline -/

/-- **The glue construction, complete** (steps 3–5 of the C6L3 step
map): EVERY graph — no admissibility needed — admits a 6-color glue
coloring on the glue grouping. -/
theorem exists_isGlueColoring (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 6),
      IsGlueColoring G ix c := by
  obtain ⟨col, hcol⟩ := exists_member_coloring G
  have hcol' : IsMemberColoring G col := hcol
  refine ⟨glueIx G, glueColor hcol', ?_, ?_, ?_, ?_⟩
  · exact glueColor_rainbow hcol'
  · intro v hv
    exact groups_glueIx_le hv
  · intro x w y hxw hwy hxy hdw hdx3
    exact glueColor_chain_end hcol' hxw hwy hxy hdw hdx3
  · intro u v huv hdu hdv f hf g hg
    exact glueColor_interior hcol' huv hdu hdv hf hg

/-- **T1, strong form (the program headline) — THEOREM**: every
admissible graph has a strong majority 6-edge-coloring, `Maj′(G) ≤ 6`,
improving the published 8 (arXiv:2605.23828 Thm 12; ≤ 5 is
arXiv:2607.00212 — this formalization is the independent chain-glue
architecture).  Proof: the (G1)–(G5) construction
(`exists_isGlueColoring`) through the closed row dispatch
(`maj_le_six_of_glue`).  Zero open inputs; the former `proof_wanted`
(SMaj/Six/Targets.lean, campaigns C3–C8) is hereby discharged. -/
theorem maj_le_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ c : Sym2 V → Fin 6, IsStrongMajority G c :=
  maj_le_six_of_glue G hadm (exists_isGlueColoring G)

/-! ### Honest scope note

Banked here: the port/fill/cycle colorings, the satSet agreement, the
four `IsGlueColoring` fields, `exists_isGlueColoring`, and the headline
`maj_le_six` — steps 3–5 of the C6L3/C7L3/C8L3 handoff, completing the
T4 lift of the ≤ 6 theorem.  Still open elsewhere:
`rainbow_of_groupSizes` (SMaj/Master.lean, Vizing Δ ≤ 4 fan — the last
`proof_wanted` of the library, NOT on the `maj_le_six` path). -/

end

/-! ###### ADDED: Maj'(G) ≤ 5 (target: Alon–Przybyło–Solomon, arXiv:2607.00212) ######

This section ADDS the five-color material on top of the frozen ≤ 6
development.  No existing definition or theorem is changed.

Architecture note (why the reduction is cheap but the construction is
not): the row case analysis `strongMajority_of_glue` is **generic over
the color palette** `C` (any `[Fintype C] [DecidableEq C]`).  Hence a
glue coloring valued in `Fin 5` yields a strong-majority `Fin 5`
coloring for free — this is `maj_le_five_of_glue`, proved below with no
new mathematical input.  The ENTIRE remaining distance to `maj_le_five`
is therefore the *construction* of a `Fin 5` glue coloring.

The ≤ 6 construction (`exists_isGlueColoring`) obtains its palette from a
Shannon edge coloring of the contracted multigraph `M`, whose maximum
degree is `≤ 4` (junction groups of size `≤ 4`).  Shannon's bound
`⌊3Δ/2⌋` at `Δ = 4` is exactly `6`, and it is TIGHT (the fat triangle),
so the glue architecture as stated cannot in general be pushed below 6:
`∃ ix c : Fin 5, IsGlueColoring G ix c` is *false* for some admissible
graphs (any `G` whose `M` contains a fat triangle).  Alon–Przybyło–
Solomon reach 5 by a genuinely different argument (not the group-of-4
chain contraction).  That argument is formalized separately by the
Λ-ladder of this artifact and assembled as `SMaj.Synthesis.maj_le_five`
(file `Rung5Lam5.lean`); a placeholder `sorry` that stood here in the
frozen ≤ 6 development has been removed for release (see the release note
below). -/
section

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Row dispatch at palette `Fin 5`** (palette-generic analogue of
`maj_le_six_of_glue`): if an admissible graph admits a glue coloring
valued in `Fin 5`, then it has a strong-majority `Fin 5` coloring.
Proof: `strongMajority_of_glue` is generic over the (finite, decidable)
color type, so no new input beyond the existing row case analysis is
needed.  This isolates the whole remaining difficulty of `maj_le_five`
in the *existence* of a five-color glue coloring. -/
theorem maj_le_five_of_glue (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G)
    (hglue : ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 5),
      IsGlueColoring G ix c) :
    ∃ c : Sym2 V → Fin 5, IsStrongMajority G c := by
  obtain ⟨ix, c, hg⟩ := hglue
  exact ⟨c, strongMajority_of_glue hadm hg⟩

/- RELEASE NOTE (stub removed): the frozen ≤ 6 development shipped here a
placeholder target theorem `SMaj.maj_le_five`, closed by a proof gap, at
this point — a target
statement it could not yet prove (Shannon is tight at 6 on the contracted
multigraph; see the section header).  That placeholder was **dead code**
(a distinct name `SMaj.maj_le_five`, referenced nowhere as a term) and is
removed from this release artifact so the shipped build is entirely
`sorry`-free.  The theorem is proved in full by the Λ-ladder as
`SMaj.Synthesis.maj_le_five` (file `Rung5Lam5.lean`), whose axiom footprint
is exactly `[propext, Classical.choice, Quot.sound]`. -/

/-! ### A proven partial result: `maj_le_five` for maximum degree ≤ 2

For graphs of maximum degree `≤ 2` (disjoint unions of paths, cycles and
single edges) the glue interface collapses: there are no junctions
(`degree ≥ 3`), so the `junction_groups` and `chain_end` fields are
vacuous; taking a per-vertex-injective index makes the `rainbow` field
free for *any* coloring; and the only real content is the `interior`
field — distance-2 distinctness on degree-2–degree-2 edges.  That
reduces to a proper coloring of the "flanking conflict" relation on
edges, whose degree is `≤ 4 < 5` (each edge flanks at most one edge
through each of its two endpoints, in each direction), so a greedy
`Fin 5` coloring exists. -/

/-
Greedy coloring, per-`Finset` form (the induction carrier): a
coloring proper on all `R`-related pairs *inside* `s`, built one vertex
at a time.
-/
lemma exists_proper_coloring_on {E : Type*} [Fintype E] [DecidableEq E]
    (R : E → E → Prop) (n : ℕ) (hn : 0 < n)
    (hirr : ∀ e, ¬ R e e) (hsymm : ∀ a b, R a b → R b a)
    (hdeg : ∀ e, {x | R e x}.ncard < n) :
    ∀ s : Finset E, ∃ col : E → Fin n,
      ∀ a ∈ s, ∀ b ∈ s, R a b → col a ≠ col b := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => ⟨0, hn⟩, by simp⟩
  | @insert a s' ha ih =>
    obtain ⟨ col, hcol ⟩ := ih;
    -- Choose a color c for a that is not used by any vertex in s' that is adjacent to a.
    obtain ⟨ c, hc ⟩ : ∃ c : Fin n, ∀ b ∈ s', R a b → col b ≠ c := by
      contrapose! hdeg;
      use a;
      rw [ Set.ncard_eq_toFinset_card _ ];
      choose f hf using hdeg;
      have h_card : Finset.card (Finset.image f Finset.univ) = n := by
        rw [ Finset.card_image_of_injective _ fun x y hxy => by have := hf x; have := hf y; aesop, Finset.card_fin ];
      exact h_card ▸ Finset.card_le_card ( Finset.image_subset_iff.mpr fun c _ => by aesop );
    use Function.update col a c; simp_all +decide [ Function.update_apply ] ;
    grind

/-- **Greedy coloring** with more colors than the maximum conflict
degree: for a finite type `E` and an irreflexive symmetric relation `R`
such that every element has fewer than `n` `R`-neighbours, there is a
coloring `E → Fin n` giving distinct colors to `R`-related elements. -/
lemma exists_proper_coloring {E : Type*} [Fintype E] [DecidableEq E]
    (R : E → E → Prop) (n : ℕ)
    (hirr : ∀ e, ¬ R e e) (hsymm : ∀ a b, R a b → R b a)
    (hdeg : ∀ e, {x | R e x}.ncard < n) :
    ∃ col : E → Fin n, ∀ a b, R a b → col a ≠ col b := by
  rcases isEmpty_or_nonempty E with hE | hE
  · exact ⟨fun x => (hE.false x).elim, fun a => (hE.false a).elim⟩
  · have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (hdeg hE.some)
    obtain ⟨col, hcol⟩ :=
      exists_proper_coloring_on R n hn hirr hsymm hdeg Finset.univ
    exact ⟨col, fun a b hab =>
      hcol a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩

/-- Per-vertex-injective edge index: assign every edge its own group at
every vertex, so that the `rainbow` field holds for *any* coloring. -/
noncomputable def sepIx : V → Sym2 V → ℕ := fun _ f => (Fintype.equivFin (Sym2 V) f : ℕ)

omit [DecidableEq V] in
lemma sepIx_inj (v : V) : Function.Injective (sepIx (V := V) v) := by
  intro a b h
  simp only [sepIx] at h
  exact (Fintype.equivFin (Sym2 V)).injective (Fin.val_injective h)

/-- `f` and `g` are *flanking* for a degree-2–degree-2 edge `s(u,v)`:
`f` is the other edge at `u`, `g` the other edge at `v`. -/
def flankConflict (G : SimpleGraph V) [DecidableRel G.Adj] (f g : Sym2 V) : Prop :=
  ∃ u v : V, G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 2 ∧
    f ∈ side G u v ∧ g ∈ side G v u

/-- Symmetric closure of `flankConflict`. -/
def flankConflictSymm (G : SimpleGraph V) [DecidableRel G.Adj] (f g : Sym2 V) : Prop :=
  flankConflict G f g ∨ flankConflict G g f

lemma flankConflict_irrefl (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V) :
    ¬ flankConflict G f f := by
  rintro ⟨u, v, huv, _, _, hfu, hfv⟩
  exact (disjoint_left.mp (disjoint_sides huv)) hfu hfv

lemma flankConflictSymm_irrefl (G : SimpleGraph V) [DecidableRel G.Adj] (f : Sym2 V) :
    ¬ flankConflictSymm G f f := by
  rintro (h | h) <;> exact flankConflict_irrefl G f h

lemma flankConflictSymm_symm (G : SimpleGraph V) [DecidableRel G.Adj] (a b : Sym2 V) :
    flankConflictSymm G a b → flankConflictSymm G b a := fun h => h.symm

/-
Under maximum degree `≤ 2`, every edge has at most `4` flanking
conflicts, hence strictly fewer than `5`.
-/
lemma flankConflictSymm_ncard_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg2 : ∀ v, G.degree v ≤ 2) (f : Sym2 V) :
    {g | flankConflictSymm G f g}.ncard < 5 := by
  obtain ⟨a, b, h⟩ : ∃ a b, f = s(a, b) := by
    rcases f with ⟨ a, b ⟩ ; exact ⟨ a, b, rfl ⟩ ;
  -- Define the covering finset T.
  set T := ((G.neighborFinset a).biUnion (fun v => side G v a)) ∪ ((G.neighborFinset b).biUnion (fun v => side G v b)) with hT_def;
  -- Step 1: Show that {g | flankConflictSymm G f g} ⊆ T.
  have h_subset : ∀ g, flankConflictSymm G f g → g ∈ T := by
    rintro g ( ⟨ u, v, huv, hu, hv, hf, hg ⟩ | ⟨ u, v, huv, hu, hv, hf, hg ⟩ ) <;> simp_all +decide;
    · simp_all +decide [ side ];
      simp_all +decide [ SimpleGraph.incidenceSet ];
      grind +qlia;
    · have := SMaj.mem_side.mp hg; simp_all +decide ;
      cases eq_or_ne a v <;> cases eq_or_ne b v <;> simp_all +decide [ SimpleGraph.mem_incidenceSet ];
      · exact Or.inl ⟨ u, huv.symm, hf ⟩;
      · exact Or.inr ⟨ u, huv.symm, hf ⟩;
      · cases this ; aesop;
  -- Step 2: Show that T.card ≤ 4.
  have h_card_T : T.card ≤ 4 := by
    refine' le_trans ( Finset.card_union_le _ _ ) _;
    refine' le_trans ( add_le_add ( Finset.card_biUnion_le ) ( Finset.card_biUnion_le ) ) _;
    refine' le_trans ( add_le_add ( Finset.sum_le_sum fun v hv => show # ( side G v a ) ≤ 1 from _ ) ( Finset.sum_le_sum fun v hv => show # ( side G v b ) ≤ 1 from _ ) ) _;
    · rw [ SMaj.card_side ] <;> simp_all +decide [ SimpleGraph.mem_neighborFinset ];
      exact hv.symm;
    · rw [ SMaj.card_side ] <;> simp_all +decide [ SimpleGraph.mem_neighborFinset ];
      exact hv.symm;
    · simp +decide [ SimpleGraph.neighborFinset ];
      exact le_trans ( add_le_add ( show Finset.card ( Finset.filter ( fun x => G.Adj a x ) Finset.univ ) ≤ 2 by simpa [ SimpleGraph.degree, SimpleGraph.neighborFinset ] using hdeg2 a ) ( show Finset.card ( Finset.filter ( fun x => G.Adj b x ) Finset.univ ) ≤ 2 by simpa [ SimpleGraph.degree, SimpleGraph.neighborFinset ] using hdeg2 b ) ) ( by norm_num );
  exact lt_of_le_of_lt ( Set.ncard_le_ncard ( show { g | flankConflictSymm G f g } ⊆ T from fun g hg => h_subset g hg ) ) ( by rw [ Set.ncard_coe_finset ] ; exact Nat.lt_succ_of_le h_card_T )

/-- **Maj'(G) ≤ 5 for maximum degree ≤ 2** (a proven partial result
toward `maj_le_five`): every admissible graph with all degrees `≤ 2`
has a strong majority 5-edge-coloring. -/
theorem maj_le_five_of_maxDegree_le_two (G : SimpleGraph V)
    [DecidableRel G.Adj] (hadm : Admissible G) (hdeg2 : ∀ v, G.degree v ≤ 2) :
    ∃ c : Sym2 V → Fin 5, IsStrongMajority G c := by
  obtain ⟨col, hcol⟩ := exists_proper_coloring (flankConflictSymm G) 5
    (flankConflictSymm_irrefl G) (flankConflictSymm_symm G)
    (flankConflictSymm_ncard_lt G hdeg2)
  refine maj_le_five_of_glue G hadm ⟨sepIx, col, ?_, ?_, ?_, ?_⟩
  · intro v f₁ _ f₂ _ hix _
    exact sepIx_inj v hix
  · intro v hv
    exact absurd hv (by have := hdeg2 v; omega)
  · intro x w y _ _ _ _ hdx3
    exact absurd hdx3 (by have := hdeg2 x; omega)
  · intro u v huv hdu hdv f hf g hg
    exact hcol f g (Or.inl ⟨u, v, huv, hdu, hdv, hf, hg⟩)

end

end SMaj