-- C3 SYNTHESIS axiom audit (own file, not the lens's CheckAxiomsC3P1.lean).
-- Run: lake env lean scripts/AuditC3Synth.lean
-- Standard: every audited theorem on exactly [propext, Classical.choice,
-- Quot.sound] (decide-backed ones may drop Classical.choice); NO sorryAx.
import Erdos866

-- Statement pins (compile-time check that the claims say what is claimed).
example : ∀ n : ℕ, gFun 5 n < 3519220 := Erdos866.g5upper_star_charter
example : Erdos866.T1TargetG5 3519220 := Erdos866.T1TargetG5_closed_charter
example : ∀ n : ℕ, gFun 5 n < 3520600 := Erdos866.g5upper_star
example : Erdos866.T1TargetG5 3520600 := Erdos866.T1TargetG5_closed_3520600
example : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 1000 := fun n h => h4_le_1000 n h
example : Erdos866.T1TargetH4 1000 := Erdos866.T1TargetH4_closed_1000
-- T1TargetG5 B' really is "B' < 120000000 ∧ ∀ n, gFun 5 n < B'":
example (B' : ℕ) (h : Erdos866.T1TargetG5 B') : B' < 120000000 ∧ ∀ n, gFun 5 n < B' := h

-- C3-P1 g₅ port (first blood under audit)
#print axioms Erdos866.g5upper_star_charter
#print axioms Erdos866.T1TargetG5_closed_charter
#print axioms Erdos866.g5upper_star
#print axioms Erdos866.T1TargetG5_closed_3520600
#print axioms Erdos866.lemmaA
#print axioms Erdos866.lemmaA_pigeonhole
#print axioms Erdos866.lemmaA_extend
#print axioms Erdos866.ceslemgeneral_star
#print axioms Erdos866.key_ineq_star_charter
#print axioms Erdos866.key_ineq_star_tuned

-- Program T1 state carried with it (h₄ closure + lower bounds, re-audited)
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000
#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five

-- Upstream baselines being superseded
#print axioms g5upper
#print axioms h4upper
