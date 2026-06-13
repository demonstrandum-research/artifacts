-- Axiom audit. Run with:  lake env lean scripts\CheckAxioms.lean
-- Final acceptance: every theorem below must report ONLY
--   [propext, Classical.choice, Quot.sound]
-- (no sorryAx, no extra axioms). While work packages are open, the
-- package-owned theorems will report sorryAx — that is expected during
-- development and must be gone at the end.
import Borsuk

-- Smoke tests (always sorry-free)
#print axioms Borsuk.Smoke.SA_pairwise_differences_primitive
#print axioms Borsuk.Smoke.card_Icc_int
#print axioms Borsuk.Smoke.seven_not_square

-- Work package 1 (Borsuk/SegmentGcd.lean)
#print axioms Borsuk.ncard_segLatticePts
#print axioms Borsuk.latticeLength_eq_gcd

-- Work package 2 (Borsuk/WitnessA.lean)
#print axioms Borsuk.latticeDiam_SA
#print axioms Borsuk.betaZ_eq_card_of_latticeDiam_eq_one
#print axioms Borsuk.betaZ_SA

-- Work package 3 (Borsuk/HullSeven.lean)
#print axioms Borsuk.mem_hullSA_iff
#print axioms Borsuk.latticeCount_hullSA

-- Work package 4 (Borsuk/Unimodular.lean)
#print axioms Borsuk.UnimodEquiv.latticeCount_eq
#print axioms Borsuk.latticeCount_cube
#print axioms Borsuk.succ_sq_ne_seven

-- Final theorems (Borsuk/Main.lean)
#print axioms Borsuk.witnessA_kills_conjecture3
#print axioms Borsuk.conjecture3_counterexample
#print axioms Borsuk.conjecture3_false
