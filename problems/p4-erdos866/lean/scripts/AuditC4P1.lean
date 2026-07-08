-- C4-P1 axiom audit: the exact-value theorem h₄(n) = 4, kernel-grade.
-- Run: lake env lean scripts/AuditC4P1.lean
-- Standard: every audited theorem on exactly [propext, Classical.choice,
-- Quot.sound] (decide-backed ones may drop Classical.choice); NO sorryAx.
import Erdos866

-- Statement pins (compile-time check that the claims say what is claimed,
-- against the upstream byte-pinned hFun — the sole hFun in scope).
example : ∀ n : ℕ, 331777 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4
example : ∀ n : ℕ, 331777 ≤ n → hFun 4 n ≤ 4 := Erdos866.h4_le_4
example : ∀ n : ℕ, 4593324 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4_charter
example : ∀ n : ℕ, 8 * 10 ^ 7 ≤ n → hFun 4 n = 4 := Erdos866.h4_eq_4_c2
-- the lower half consumed (C2-P2), and the eventual-interval consistency:
example : ∀ n : ℕ, 3 ≤ n → 4 ≤ hFun 4 n := Erdos866.four_le_hFun_four
-- hFun is the upstream definition (pin by unfolding type, not by trust):
example : hFun = fun (k n : ℕ) => sInf {m : ℕ | ∀ (A : Finset ℤ),
    A ⊆ Finset.Icc (1 : ℤ) (2 * ↑n) → n + m ≤ A.card →
    HasPosPairwiseSums A k} := rfl

-- The headline and its assembly
#print axioms Erdos866.h4_eq_4
#print axioms Erdos866.h4_le_4
#print axioms Erdos866.h4_eq_4_charter
#print axioms Erdos866.h4_eq_4_c2

-- The corrected-chain machinery (C4-P1, new)
#print axioms Erdos866.Dicho.structural_case
#print axioms Erdos866.Dicho.K_epairs_le2
#print axioms Erdos866.Dicho.T_star
#print axioms Erdos866.Dicho.hasPPS_of_quad
#print axioms Erdos866.Dicho.balanced_kill
#print axioms Erdos866.Dicho.tt_aux
#print axioms Erdos866.Dicho.triangle_free_fib
#print axioms Erdos866.Dicho.cap_fib
#print axioms Erdos866.Dicho.fFunPos_four_lt_crossover8
#print axioms Erdos866.Dicho.hasPosPairwiseSums_of_dense8
#print axioms Erdos866.Dicho.dense_case8

-- The C3-P2 pillars carried (belt: endgame certificates + old chain)
#print axioms Erdos866.Dicho.dichoCerts_ok
#print axioms Erdos866.Dicho.endgame_no_survivor
#print axioms Erdos866.Dicho.K_opairs_le
#print axioms Erdos866.Dicho.K_epairs_le
#print axioms Erdos866.Dicho.dense_case

-- Consumed lower bound
#print axioms Erdos866.four_le_hFun_four
