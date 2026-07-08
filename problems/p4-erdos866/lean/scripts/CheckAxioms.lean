-- Axiom audit for the Erdős #866 extension project.
-- Run from the project root:  lake env lean scripts\CheckAxioms.lean
-- Every theorem below must report only the standard axioms
-- (propext, Classical.choice, Quot.sound) — no sorryAx.
import Erdos866

-- new warm-up results (this project)
#print axioms HasPairwiseSums.mono
#print axioms HasPosPairwiseSums.mono
#print axioms one_le_gFun
#print axioms one_le_hFun
#print axioms Erdos866.not_hps_A95
#print axioms Erdos866.five_le_gFun_five_five

-- Campaign-2 P1: h₄ ≤ 1000 (energy-form asymmetric-central-interval port)
#print axioms h4_le_1000
#print axioms Erdos866.T1TargetH4_closed_1000
#print axioms ErdosH4.has_pps_of_large_1000
#print axioms ErdosH4.chain_phinu
#print axioms ErdosH4.not_weak_sidon_of_phinu
#print axioms ErdosH4.has_pps_central_even_asym
#print axioms ErdosH4.exists_valid_b3_asym
#print axioms cert_lookup
#print axioms ErdosH4Tail.tail_cert

-- dossier §5 standing-bounds index (restatements of upstream)
#print axioms Erdos866.standing_sandwich
#print axioms Erdos866.standing_g3
#print axioms Erdos866.standing_g3small
#print axioms Erdos866.standing_h3
#print axioms Erdos866.standing_g4
#print axioms Erdos866.standing_h4_upper
#print axioms Erdos866.standing_h4_lower
#print axioms Erdos866.standing_g5_upper
#print axioms Erdos866.standing_g5_lower
#print axioms Erdos866.standing_h5_lower
#print axioms Erdos866.standing_hk_upper
#print axioms Erdos866.standing_general_upper
