-- C4-SYNTHESIS audit (own file, own selection — not the lenses' scripts).
-- Run: lake env lean scripts/AuditC4Synth.lean
-- Standard: every audited theorem on exactly [propext, Classical.choice,
-- Quot.sound] (decide-backed ones may drop Classical.choice); NO sorryAx.
import Erdos866

-- ===== Statement pins (compile-time; against the byte-pinned upstream) =====
-- C4-P1 headline: the exact-value theorem, kernel constant 331,777 = 24^4+1.
example : ∀ n : ℕ, 331777 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4
example : (331777 : ℕ) = 24 ^ 4 + 1 := by norm_num
example : ∀ n : ℕ, 331777 ≤ n → hFun 4 n ≤ 4 := Erdos866.h4_le_4
example : ∀ n : ℕ, 4593324 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4_charter
example : ∀ n : ℕ, 8 * 10 ^ 7 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4_c2
-- hFun is the upstream sInf definition (pin by rfl, not by trust):
example : hFun = fun (k n : ℕ) => sInf {m : ℕ | ∀ (A : Finset ℤ),
    A ⊆ Finset.Icc (1 : ℤ) (2 * ↑n) → n + m ≤ A.card →
    HasPosPairwiseSums A k} := rfl
-- Carried binding state: both T1 closures + lower-bound suite.
example : ∀ n : ℕ, gFun 5 n < 3519220 := Erdos866.g5upper_star_charter
example : Erdos866.T1TargetG5 3519220 := Erdos866.T1TargetG5_closed_charter
example : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 1000 := fun n h => h4_le_1000 n h
example : Erdos866.T1TargetH4 1000 := Erdos866.T1TargetH4_closed_1000
example : ∀ n : ℕ, 3 ≤ n → 4 ≤ hFun 4 n := Erdos866.four_le_hFun_four
-- T1Target props say what they claim (unfold, no trust):
example (B' : ℕ) (h : Erdos866.T1TargetG5 B') :
    B' < 120000000 ∧ ∀ n, gFun 5 n < B' := h
example (B : ℕ) (h : Erdos866.T1TargetH4 B) :
    B < 2270 ∧ ∀ n, 0 < n → hFun 4 n ≤ B := h
-- Eventual-interval consistency: the exact value meets the lower half.
example (n : ℕ) (h : 331777 ≤ n) : 4 ≤ hFun 4 n :=
  (Erdos866.h4_eq_4 n h).ge

-- ===== Axiom audit =====
-- C4-P1 headline + assembly
#print axioms Erdos866.h4_eq_4
#print axioms Erdos866.h4_le_4
#print axioms Erdos866.h4_eq_4_charter
#print axioms Erdos866.h4_eq_4_c2
-- The closed sorry and the new KC1=2 machinery
#print axioms Erdos866.Dicho.structural_case
#print axioms Erdos866.Dicho.K_epairs_le2
#print axioms Erdos866.Dicho.balanced_kill
#print axioms Erdos866.Dicho.T_star
#print axioms Erdos866.Dicho.hasPPS_of_quad
#print axioms Erdos866.Dicho.tt_aux
#print axioms Erdos866.Dicho.triangle_free_fib
#print axioms Erdos866.Dicho.cap_fib
#print axioms Erdos866.Dicho.fFunPos_four_lt_crossover8
#print axioms Erdos866.Dicho.hasPosPairwiseSums_of_dense8
#print axioms Erdos866.Dicho.dense_case8
-- C3-P2 belt kept (endgame certs + old chain)
#print axioms Erdos866.Dicho.dichoCerts_ok
#print axioms Erdos866.Dicho.endgame_no_survivor
#print axioms Erdos866.Dicho.K_opairs_le
#print axioms Erdos866.Dicho.K_epairs_le
-- Carried T1 closures + lower bounds + general-k core (binding state)
#print axioms Erdos866.g5upper_star_charter
#print axioms Erdos866.T1TargetG5_closed_charter
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000
#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five
#print axioms Erdos866.lemmaA
#print axioms Erdos866.ceslemgeneral_star
