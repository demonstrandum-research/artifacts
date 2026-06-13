-- Axiom audit for WORK PACKAGE 1 (Borsuk/SegmentGcd.lean) only.
-- Run with:  lake env lean scripts\CheckAxiomsP1.lean
-- Acceptance: every theorem below must report ONLY
--   [propext, Classical.choice, Quot.sound]
-- (no sorryAx, no extra axioms).
import Borsuk.SegmentGcd

#print axioms Borsuk.gcd_smul_primVec
#print axioms Borsuk.primVec_primitive
#print axioms Borsuk.segLatticePts_eq_image
#print axioms Borsuk.ncard_segLatticePts
#print axioms Borsuk.latticeLength_eq_gcd
#print axioms Borsuk.latticeLength_eq_one_iff
#print axioms Borsuk.one_le_latticeLength_of_ne
