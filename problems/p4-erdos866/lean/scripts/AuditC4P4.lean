-- C4-P4 (publication) lens's OWN axiom audit, 2026-06-13.
-- Run: lake env lean scripts/AuditC4P4.lean   (after a fresh `lake build`)
-- Standard: every audited declaration on exactly a subset of
-- [propext, Classical.choice, Quot.sound]; NO sorryAx anywhere below.
-- (The quarantined H4Dichotomy module is audited separately — it is NOT
--  imported here, so this file also re-checks that the root needs no sorry.)
import Erdos866

-- ===== Statement pins (compile-time: the claims say what the paper says) =====
-- Paper Thm 1.4 [K]: the g5 charter constant (T1 g5 closure)
example : ∀ n : ℕ, gFun 5 n < 3519220 := Erdos866.g5upper_star_charter
example : Erdos866.T1TargetG5 3519220 := Erdos866.T1TargetG5_closed_charter
example : ∀ n : ℕ, gFun 5 n < 3520600 := Erdos866.g5upper_star
-- T1TargetG5 B' really is "B' < 120000000 ∧ ∀ n, gFun 5 n < B'":
example (B' : ℕ) (h : Erdos866.T1TargetG5 B') :
    B' < 120000000 ∧ ∀ n, gFun 5 n < B' := h
-- Paper Thm 1.1 [K]: h4 ≤ 1000
example : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 1000 := fun n h => h4_le_1000 n h
example : Erdos866.T1TargetH4 1000 := Erdos866.T1TargetH4_closed_1000
-- Paper Thm 1.2 [K]: lower bound + strict g/h separation
example : ∀ n : ℕ, 3 ≤ n → 4 ≤ hFun 4 n := Erdos866.four_le_hFun_four
example : ∀ n : ℕ, 3 ≤ n → gFun 4 n < hFun 4 n := Erdos866.gFun_four_lt_hFun_four
-- Paper Thm 1.5 [K] (family inequality)
example : ∀ n : ℕ, Erdos866.fibCnt n < hFun 5 n := Erdos866.fibCnt_lt_hFun_five

-- ===== Axiom audit: paper [K] claims =====
-- Thm 1.4 (g5 T1 closure, charter constant) + supporting chain
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
#print axioms Erdos866.key_ineq_star
#print axioms Erdos866.fStar5_le_poly

-- Thm 1.1 (h4 T1 closure)
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000

-- Thm 1.2 / 1.5 (lower bounds)
#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five

-- ===== Upstream anchors the claims bind to =====
#print axioms h4upper
#print axioms g5upper
#print axioms h5lower
#print axioms g5lower
#print axioms gFun_le_hFun_le_gFun_succ
#print axioms generalupper
-- upstream ingredients CITED as [K] in the paper body:
#print axioms weak_sidon_key_ineq
#print axioms weak_sidon_bound
#print axioms ceslemgeneral_pos
#print axioms ceslemgeneral
#print axioms g4
