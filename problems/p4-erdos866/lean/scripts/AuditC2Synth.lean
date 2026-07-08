-- C2 synthesis agent's OWN axiom audit (fresh file, not the lenses' scripts).
-- Run: lake env lean scripts/AuditC2Synth.lean
-- Expectation: every line prints only [propext, Classical.choice, Quot.sound]
-- (subsets allowed), EXCEPT the two marked SORRY-EXPECTED lines (P3 stub).
import Erdos866
import Erdos866.G5FStar

-- P1 first blood: T1 h4 closure at B = 1000
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000

-- P2 first blood: lower bounds
#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five

-- P3 numeric side (claimed sorry-free)
#print axioms Erdos866.key_ineq_star
#print axioms Erdos866.key_ineq_star_tuned
#print axioms Erdos866.fStar5_le_poly

-- P3 stub: SORRY-EXPECTED (documented in lens STATUS; not a claim)
#print axioms Erdos866.lemmaA
#print axioms Erdos866.ceslemgeneral_star

-- upstream anchors the claims bind to
#print axioms h4upper
#print axioms g5upper
#print axioms h5lower
