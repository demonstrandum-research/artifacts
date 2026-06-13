-- Axiom audit for the main theorem (not part of the library build).
-- Run: lake env lean scripts\AxiomCheck.lean
-- Expected: every #print axioms line lists at most
--   propext, Classical.choice, Quot.sound
import ElizaldeLuo.Main

open ElizaldeLuo

#print axioms ElizaldeLuo.elizalde_luo_1132_3312
#print axioms ElizaldeLuo.conjecture_holds
#print axioms ElizaldeLuo.card_avoiders_eq_card_validPairs
#print axioms ElizaldeLuo.card_validPairs_eq_card_W
#print axioms ElizaldeLuo.card_W
#print axioms ElizaldeLuo.theoremA
#print axioms ElizaldeLuo.contains_1132_iff
#print axioms ElizaldeLuo.contains_3312_iff
