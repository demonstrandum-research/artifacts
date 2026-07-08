-- C3-P4 (hygiene-paper) agent's OWN axiom audit, 2026-06-12.
-- Run: lake env lean scripts/AuditC3P4.lean   (after a fresh `lake build`)
-- Expectation: every line prints a subset of
-- [propext, Classical.choice, Quot.sound], EXCEPT the two marked
-- SORRY-EXPECTED lines (P3 stub, quarantined outside the root module).
import Erdos866
import Erdos866.G5FStar

-- Paper Thm: T1 h4 closure at B = 1000 (kernel-grade upper half)
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000

-- Paper Thm: lower bounds (kernel-grade)
#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five

-- g5 numeric side (sorry-free, feeds the C3-P1 port)
#print axioms Erdos866.key_ineq_star
#print axioms Erdos866.key_ineq_star_tuned
#print axioms Erdos866.fStar5_le_poly

-- P3 stub: SORRY-EXPECTED (documented; NOT a paper claim)
#print axioms Erdos866.lemmaA
#print axioms Erdos866.ceslemgeneral_star

-- upstream anchors the claims bind to
#print axioms h4upper
#print axioms g5upper
#print axioms h5lower
#print axioms g5lower
#print axioms gFun_le_hFun_le_gFun_succ
#print axioms generalupper
-- upstream ingredients CITED as [K] in the paper (Codex C3P4 finding 1):
#print axioms weak_sidon_key_ineq
#print axioms weak_sidon_bound
#print axioms ceslemgeneral_pos
#print axioms g4
