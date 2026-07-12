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
import Mathlib

namespace SMaj

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

end SMaj
