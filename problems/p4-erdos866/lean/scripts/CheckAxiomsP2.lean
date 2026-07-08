-- Axiom audit for Campaign-2 P2 (lower-bound ports), from the built olean.
-- Run from the project root:  lake env lean scripts\CheckAxiomsP2.lean
-- Every theorem below must report only [propext, Classical.choice, Quot.sound].
import Erdos866.LowerBounds

#print axioms Erdos866.four_le_hFun_four
#print axioms Erdos866.gFun_four_lt_hFun_four
#print axioms Erdos866.fibCnt_lt_hFun_five

-- supporting lemmas
#print axioms Erdos866.H4Witness_card
#print axioms Erdos866.H4Witness_no_pps
#print axioms Erdos866.H5Witness_card
#print axioms Erdos866.H5Witness_no_pps
#print axioms Erdos866.fib_triple_bound
#print axioms Erdos866.fib_no_triangle

-- statement-faithfulness guards: the theorems are about the UPSTREAM hFun/gFun
-- (these `example`s fail to elaborate if the statements ever drift)
example : ∀ n : ℕ, 3 ≤ n → 4 ≤ hFun 4 n := Erdos866.four_le_hFun_four
example : ∀ n : ℕ, 3 ≤ n → gFun 4 n < hFun 4 n := Erdos866.gFun_four_lt_hFun_four
example : ∀ n : ℕ, Erdos866.fibCnt n < hFun 5 n := Erdos866.fibCnt_lt_hFun_five
