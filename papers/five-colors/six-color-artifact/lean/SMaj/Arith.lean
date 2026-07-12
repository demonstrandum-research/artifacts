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
import Mathlib

namespace SMaj

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

end SMaj
