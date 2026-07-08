-- C6 SYNTHESIS audit (own file, own selection): C6P3 first-blood theorems
-- + carried program anchors. Expect [propext, Classical.choice, Quot.sound]
-- (or fewer) on every line, zero sorryAx.
-- Run: lake env lean scripts/AuditC6Synth.lean   (from lean/)
import Erdos866

-- === C6P3 statement pins (compile-time) ===
example : ∀ (k : ℕ), 3 ≤ k → ∀ (n : ℕ), 1 ≤ n →
    gFun k n ≤ ⌈Erdos866.fStar k (2 * (n : ℝ)) 0⌉₊ :=
  fun k hk n hn => Erdos866.gk_upper_star k hk n hn
example : ∀ n : ℕ, 32768 ≤ n → (gFun 6 n : ℝ) < 2 * (n : ℝ) ^ ((15 : ℝ) / 16) :=
  fun n hn => Erdos866.g6upper_t2 n hn
example : ∀ n : ℕ, 2147483648 ≤ n → (gFun 7 n : ℝ) < 2 * (n : ℝ) ^ ((31 : ℝ) / 32) :=
  fun n hn => Erdos866.g7upper_t2 n hn
example : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + 1 ≤ Erdos866.fibCnt n :=
  fun n hn => Erdos866.log2_succ_le_fibCnt n hn
example : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + 1 < hFun 5 n :=
  fun n hn => Erdos866.log2_succ_lt_hFun_five n hn

-- === carried program anchors (statement re-pins) ===
example : ∀ n : ℕ, 331777 ≤ n → hFun 4 n = 4 :=
  fun n hn => Erdos866.h4_eq_4 n hn
example : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 1000 :=
  fun n hn => h4_le_1000 n hn
example : ∀ n : ℕ, gFun 5 n < 3519220 :=
  fun n => Erdos866.g5upper_star_charter n
-- threshold sanity: 2^15 and 2^31, 331777 = 24^4 + 1
example : (32768 : ℕ) = 2 ^ 15 := by norm_num
example : (2147483648 : ℕ) = 2 ^ 31 := by norm_num
example : (331777 : ℕ) = 24 ^ 4 + 1 := by norm_num

-- === axiom audit ===
#print axioms Erdos866.gk_upper_star
#print axioms Erdos866.g6upper_t2
#print axioms Erdos866.g7upper_t2
#print axioms Erdos866.log2_succ_le_fibCnt
#print axioms Erdos866.log2_succ_lt_hFun_five
#print axioms Erdos866.h4_eq_4
#print axioms h4_le_1000
#print axioms Erdos866.g5upper_star_charter
#print axioms Erdos866.ceslemgeneral_star
#print axioms Erdos866.lemmaA
