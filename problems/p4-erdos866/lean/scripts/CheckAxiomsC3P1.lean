-- C3-P1 axiom audit: the g₅ port (Lemma A + assembly at B = 3,520,600).
-- Run: lake env lean scripts/CheckAxiomsC3P1.lean
-- Expected: every theorem on exactly [propext, Classical.choice, Quot.sound];
-- NO sorryAx anywhere (the C2-P3 lemmaA sorry is discharged).
import Erdos866

#print axioms Erdos866.fStar_ge_two
#print axioms Erdos866.fStar_mono_x
#print axioms Erdos866.fStar_root_base
#print axioms Erdos866.fStar_root_step
#print axioms Erdos866.lemmaA_pigeonhole
#print axioms Erdos866.lemmaA_base3
#print axioms Erdos866.lemmaA_extend
#print axioms Erdos866.lemmaA
#print axioms Erdos866.ceslemgeneral_star
#print axioms Erdos866.key_ineq_star_tuned
#print axioms Erdos866.g5upper_case_even_star
#print axioms Erdos866.g5upper_aux_star
#print axioms Erdos866.g5upper_star
#print axioms Erdos866.T1TargetG5_closed_3520600
-- Phase D (charter constant)
#print axioms Erdos866.fStar5_le_poly_sharp
#print axioms Erdos866.young_u7_charter
#print axioms Erdos866.key_ineq_star_charter
#print axioms Erdos866.g5upper_star_charter
#print axioms Erdos866.T1TargetG5_closed_charter
-- context: the standing upstream bound this supersedes
#print axioms g5upper
