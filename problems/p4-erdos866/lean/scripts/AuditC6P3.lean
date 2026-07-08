-- C6-P3 (T2 Lean instantiation retry) axiom audit: every new declaration
-- must close over exactly [propext, Classical.choice, Quot.sound], NO sorryAx.
-- Run: lake env lean scripts/AuditC6P3.lean   (from lean/)
import Erdos866

-- Statement pins (compile-time checks that the new theorems say what the
-- lens report says they say).

-- [P1] the general-k wrapper on ceslemgeneral_star:
example : ∀ (k : ℕ), 3 ≤ k → ∀ (n : ℕ), 1 ≤ n →
    gFun k n ≤ ⌈Erdos866.fStar k (2 * (n : ℝ)) 0⌉₊ :=
  fun k hk n hn => Erdos866.gk_upper_star k hk n hn

-- [P2] k = 6 instance, T2(g) shape with explicit threshold 2^15:
example : ∀ n : ℕ, 32768 ≤ n → (gFun 6 n : ℝ) < 2 * (n : ℝ) ^ ((15 : ℝ) / 16) :=
  fun n hn => Erdos866.g6upper_t2 n hn

-- [P3] k = 7 instance, T2(g) shape with explicit threshold 2^31:
example : ∀ n : ℕ, 2147483648 ≤ n → (gFun 7 n : ℝ) < 2 * (n : ℝ) ^ ((31 : ℝ) / 32) :=
  fun n hn => Erdos866.g7upper_t2 n hn

-- [P4] the comparison lemma (hygiene carry closed) + the strict h5 corollary:
example : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + 1 ≤ Erdos866.fibCnt n :=
  fun n hn => Erdos866.log2_succ_le_fibCnt n hn
example : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + 1 < hFun 5 n :=
  fun n hn => Erdos866.log2_succ_lt_hFun_five n hn

-- exponent sanity: 15/16 = 1 - 2^(2-6), 31/32 = 1 - 2^(2-7) (alpha_k of T2)
example : (15 : ℝ) / 16 = 1 - (2 : ℝ) ^ ((2 : ℝ) - 6) := by
  rw [show ((2 : ℝ) - 6) = -(((4 : ℕ) : ℝ)) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  norm_num
example : (31 : ℝ) / 32 = 1 - (2 : ℝ) ^ ((2 : ℝ) - 7) := by
  rw [show ((2 : ℝ) - 7) = -(((5 : ℕ) : ℝ)) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  norm_num

-- Axiom audit (expect exactly [propext, Classical.choice, Quot.sound] each):
#print axioms Erdos866.gk_upper_star
#print axioms Erdos866.gk_upper_star_aux
#print axioms Erdos866.g6upper_t2
#print axioms Erdos866.g7upper_t2
#print axioms Erdos866.fStar6_le_poly16
#print axioms Erdos866.fStar7_le_poly32
#print axioms Erdos866.key6_endgame
#print axioms Erdos866.key7_endgame
#print axioms Erdos866.rt16_two
#print axioms Erdos866.rt32_two
#print axioms Erdos866.fib_add_two_le_two_pow
#print axioms Erdos866.log2_succ_le_fibCnt
#print axioms Erdos866.log2_succ_lt_hFun_five
-- consumed kernel anchors (re-pin):
#print axioms Erdos866.ceslemgeneral_star
#print axioms Erdos866.fStar_mono_x
#print axioms Erdos866.fStar_ge_two
#print axioms Erdos866.fibCnt_lt_hFun_five
