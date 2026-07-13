import Pins2

-- ============================================================================
-- Closed / kernel-clean declarations: each line must contain ONLY standard
-- axioms [propext, Classical.choice, Quot.sound], never sorryAx.
-- ============================================================================
#print axioms Rung4Moonshot.nColor_add_two_mul
#print axioms Rung4Moonshot.isStrongMajority_of_cnt
#print axioms Rung4Moonshot.E1_of_cnt_le_one
#print axioms Rung4Moonshot.E1_split
#print axioms Rung4Moonshot.classI_strongMajority
#print axioms Rung4Moonshot.classI_arm
#print axioms Rung4Moonshot.IsEdgeSplit.swap
#print axioms Rung4Moonshot.P2_equiv    -- see note: routine pins, sorryAx expected

-- ---- Wave-3 transplants (must be sorry-free / standard axioms only) ----
#print axioms Rung4Moonshot.E1_defect_core        -- from r4w3_p3_conditional
#print axioms Rung4Moonshot.cnt_combine_le_two     -- from r4w3_p3_oddarm
#print axioms Rung4Moonshot.sm_of_offcolor         -- from r4w3_p3_oddarm
-- component-lift helpers (from r4w3_component_lift)
#print axioms Rung4Moonshot.induce_supp_degree
#print axioms Rung4Moonshot.glueAux_symm
#print axioms Rung4Moonshot.glue_mk
#print axioms Rung4Moonshot.glue_edge
#print axioms Rung4Moonshot.cnt_glue_eq
#print axioms Rung4Moonshot.nColor_glue_eq

-- ---- Round-2 transplants (must be sorry-free / standard axioms only) ----
-- odd-cycle/parity toolbox + P2_onlyif (from r4w3_parity_pair)
#print axioms Rung4Moonshot.exists_shorter_odd_closed_walk
#print axioms Rung4Moonshot.exists_odd_cycle_of_odd_closed_walk
#print axioms Rung4Moonshot.closedWalk_even_of_no_odd_cycle
#print axioms Rung4Moonshot.colorable_two_of_no_odd_cycle
#print axioms Rung4Moonshot.even_card_of_two_regular_colorable
#print axioms Rung4Moonshot.even_card_of_two_regular_no_odd_cycle
#print axioms Rung4Moonshot.P2_onlyif
-- ---- Round-4 transplant: the Euler split, attached from rung4_c8_1_a ----
-- exists_edge_split_pin is no longer EXTERNAL-BANKED: kernel-clean required.
#print axioms Rung4Moonshot.adjMat
#print axioms Rung4Moonshot.mdeg_adjMat
#print axioms Rung4Moonshot.exists_edge_split_pin
-- Fintype argmin over the split space (from r4w4_oddmin); consumed
-- exists_edge_split_pin, so this must NOW also be kernel-clean.
#print axioms Rung4Moonshot.exists_oddCycleMinimal_split

-- ---- Round-3 transplants (must be sorry-free / standard axioms only) ----
-- proper-2-edge-coloring chain (from r4w3_proper2_direct)
#print axioms Rung4Moonshot.incidenceFinset_deleteEdges_single
#print axioms Rung4Moonshot.degree_deleteEdges_single
#print axioms Rung4Moonshot.card_edgeFinset_deleteEdges_adj
#print axioms Rung4Moonshot.noOdd_deleteEdges
#print axioms Rung4Moonshot.path_edge_color
#print axioms Rung4Moonshot.reachable_two_odd
#print axioms Rung4Moonshot.epc_leaf_step
#print axioms Rung4Moonshot.epc_cycle_key
#print axioms Rung4Moonshot.epc_cycle_step
#print axioms Rung4Moonshot.epc_aux
#print axioms Rung4Moonshot.exists_proper_two_edge_coloring
-- count-bound extraction + closed P2_equiv_fwd (round 3)
#print axioms Rung4Moonshot.cnt_combine_le_one
#print axioms Rung4Moonshot.P2_equiv_fwd
-- cross/defect calculus helpers (from r4w4_defect_iff; cap_eq_three_iff from r4w5_crux_bricked)
#print axioms Rung4Moonshot.halfCount_true_add_false
#print axioms Rung4Moonshot.halfCount_add_not
#print axioms Rung4Moonshot.halfCount_le_degree
#print axioms Rung4Moonshot.half_degree_bounds
#print axioms Rung4Moonshot.cap_two_or_three
#print axioms Rung4Moonshot.cap_eq_three_iff
#print axioms Rung4Moonshot.cnt_combine_H0_false
#print axioms Rung4Moonshot.cnt_combine_H0_true
#print axioms Rung4Moonshot.cnt_combine_H1_false
#print axioms Rung4Moonshot.cnt_combine_H1_true
#print axioms Rung4Moonshot.same_half_bound
-- the two closed local-calculus pins (from r4w4_defect_iff)
#print axioms Rung4Moonshot.defectSafe_iff_crossSafe
#print axioms Rung4Moonshot.strongMajority_of_crossSafe_split

-- ---- Round-5 transplants (from r4w4_p2equiv; must be standard axioms only) ----
#print axioms Rung4Moonshot.incidenceFinset_colSub
#print axioms Rung4Moonshot.even_length_of_proper
#print axioms Rung4Moonshot.noOddCycle_colSub
#print axioms Rung4Moonshot.isEdgeSplit_colSub
#print axioms Rung4Moonshot.P2_equiv_bwd
-- With both directions closed, the equivalence must now be kernel-clean.
#print axioms Rung4Moonshot.P2_equiv

-- ---- Round-6 merge: Fable crux-lane min-alternating toolbox (48361f2) ----
-- A0 support-closure suite
#print axioms Rung4Moonshot.cycle_edge_mem_of_adj
#print axioms Rung4Moonshot.cycle_support_closed_adj
#print axioms Rung4Moonshot.cycle_support_closed_reachable
#print axioms Rung4Moonshot.degree_eq_two_of_mem_cycle_support
#print axioms Rung4Moonshot.cycle_support_subset_of_mem
-- phase control
#print axioms Rung4Moonshot.halfCount_flipOn_mem
#print axioms Rung4Moonshot.halfCount_flipOn_notMem
#print axioms Rung4Moonshot.DefectProfile.flipOn
#print axioms Rung4Moonshot.DefectProfile.congr_sigma
-- defect-set existence
#print axioms Rung4Moonshot.nonempty_of_mem_oddCycleSupports
#print axioms Rung4Moonshot.exists_isOddCycleDefectSet
-- interior path alternation
#print axioms Rung4Moonshot.path_edge_color_interior
#print axioms Rung4Moonshot.path_end_colors_of_even
-- realizability core
#print axioms Rung4Moonshot.exists_defectProfile_aux
#print axioms Rung4Moonshot.exists_defectProfile
#print axioms Rung4Moonshot.exists_isMinAlternating
#print axioms Rung4Moonshot.exists_minAlternating_data
-- zero-odd discharge trio
#print axioms Rung4Moonshot.noOddCycle_of_oddCycleCount_eq_zero
#print axioms Rung4Moonshot.isOddCycleDefectSet_empty
#print axioms Rung4Moonshot.defectSafe_empty

-- ---- Round-8 transplants (from r4w8_crux_parity; must be standard axioms only) ----
#print axioms Rung4Moonshot.placement_half_of_noOddCycle
#print axioms Rung4Moonshot.placement_on_oddCycleMinimal_split_both_zero
#print axioms Rung4Moonshot.placement_reduce_to_single_half
#print axioms Rung4Moonshot.cap_comm
#print axioms Rung4Moonshot.defectSafe_singleton

-- ---- Round 13: avoidance core + 4-regular case closed (standard-triple) ----
#print axioms Rung4Moonshot.Avoid.hall_slot_sum
#print axioms Rung4Moonshot.Avoid.biUnion_slotTarget_eq
#print axioms Rung4Moonshot.Avoid.exists_slot_matching
#print axioms Rung4Moonshot.Avoid.avoidance_core
#print axioms Rung4Moonshot.oddCycleSupports_pairwise_disjoint
#print axioms Rung4Moonshot.oddCycleSupports_three_le_card
-- Case B (sorryAx via the descent core only):
#print axioms Rung4Moonshot.clean_transversal_case_deg3

-- ---- Round 16: THE UNCONDITIONAL 4-REGULAR THEOREM ----
-- MUST print the standard triple, no sorryAx (parallel chain avoiding the
-- descent pin entirely): the campaign's first unconditional theorem.
#print axioms Rung4Moonshot.R4_four_regular

-- ---- Round 12: Codex descent reduction ----
-- THE single remaining pin (sorry; sole sorryAx source in the file):
#print axioms Rung4Moonshot.strict_descent_of_no_clean_transversal
-- Now PROVED modulo the core (sorryAx solely via it):
#print axioms Rung4Moonshot.clean_transversal_of_minimal

-- ---- Round 11: descent surgery engine (from r4w10_descent_a; standard-triple) ----
#print axioms Rung4Moonshot.oddCycleSupports_deleteEdges_subset
#print axioms Rung4Moonshot.oddCycleCount_deleteEdges_le
#print axioms Rung4Moonshot.oddCycleCount_deleteEdges_lt

-- ---- Round 10: the bridge CLOSED + structure theory ----
-- bridge helpers (from r4w10_bridge_a; must be standard-triple)
#print axioms Rung4Moonshot.crossOnSet_le
#print axioms Rung4Moonshot.crossOnSet_support_subset
#print axioms Rung4Moonshot.crossOnSet_noOddCycle
#print axioms Rung4Moonshot.isOddCycleDefectSet_image_transversal
-- THE BRIDGE — must now be standard-triple:
#print axioms Rung4Moonshot.placement_of_clean_transversal
-- max-degree-2 structure theory (from r4w7_crux_smallfirst; standard-triple)
#print axioms Rung4Moonshot.min_alt_no_odd
#print axioms Rung4Moonshot.cycle_support_deg_ge_two
#print axioms Rung4Moonshot.cycle_support_closed
#print axioms Rung4Moonshot.maxdeg2_component_of_cycle_is_2regular
#print axioms Rung4Moonshot.not_mem_cycle_of_degree_one
#print axioms Rung4Moonshot.deleted_cycle_component_acyclic
-- HEADLINE CHAIN: every row below must show sorryAx inherited SOLELY via
-- clean_transversal_of_minimal (the one remaining sorry).
#print axioms Rung4Moonshot.placement_on_oddCycleMinimal_split
#print axioms Rung4Moonshot.exists_safe_split_placement
#print axioms Rung4Moonshot.classII_arm
#print axioms Rung4Moonshot.R4_three_four_connected
#print axioms Rung4Moonshot.R4_three_four

-- ---- Round 9: clean-transversal kernel target ----
-- PROVED, must be standard-triple:
#print axioms Rung4Moonshot.mem_cleanSet
#print axioms Rung4Moonshot.IsOddCycleMinimalSplit.swap
-- The single descent pin + the bridge (both sorry; sorryAx expected):
#print axioms Rung4Moonshot.clean_transversal_of_minimal
#print axioms Rung4Moonshot.placement_of_clean_transversal
-- Derived modulo the above (sorryAx expected, inherited ONLY from them):
#print axioms Rung4Moonshot.clean_set_nonempty_of_minimal

-- ---- Round 7: quantifier re-thread ----
-- classII_arm now routes through the EXISTENTIAL pin exists_safe_split_placement
-- (Scheme C); the universal crux placement_on_oddCycleMinimal_split remains as a
-- parallel route (sorry, off the critical path). Both expected sorryAx below.
#print axioms Rung4Moonshot.exists_safe_split_placement
#print axioms Rung4Moonshot.placement_on_oddCycleMinimal_split
#print axioms Rung4Moonshot.classII_arm

-- ============================================================================
-- Expected to contain sorryAx until their tagged pins close.
-- R4_three_four's OWN body is now sorry-free (component lift transplanted),
-- but it CALLS R4_three_four_connected, so it inherits sorryAx from the
-- connected-case pins. This is expected; the lift itself adds no new debt.
-- ============================================================================
#print axioms Rung4Moonshot.strongMajority_of_safe_defects
#print axioms Rung4Moonshot.R4_three_four_connected
#print axioms Rung4Moonshot.R4_three_four
