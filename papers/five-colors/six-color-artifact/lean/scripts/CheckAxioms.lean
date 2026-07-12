/- Axiom audit for the SMaj library.  Run with:
   lake env lean scripts\CheckAxioms.lean
   Every theorem must depend only on propext / Classical.choice / Quot.sound
   (no sorryAx, no extra axioms). -/
import SMaj

open SMaj

#print axioms SMaj.counting_lemma
#print axioms SMaj.side_count_le
#print axioms SMaj.card_row
#print axioms SMaj.disjoint_sides
#print axioms SMaj.master_coloring
#print axioms SMaj.master_of_inputs
#print axioms SMaj.corA_coloring
#print axioms SMaj.admissible_of_crit
#print axioms SMaj.hfun_anti
#print axioms SMaj.crit_of_crit_le
#print axioms SMaj.bad3_table
#print axioms SMaj.bad4_table
#print axioms SMaj.bad5_table
#print axioms SMaj.crit3_of_no24
#print axioms SMaj.crit4_of_scope
#print axioms SMaj.crit5_of_scope
#print axioms SMaj.not_crit5_iff
#print axioms SMaj.not_crit_saturated
#print axioms SMaj.crit_admissible

/- Lens C3L4-lean-six (campaign C3): the ≤ 6 elementary core. -/
#print axioms SMaj.g_R1
#print axioms SMaj.crit4_of_ne_two
#print axioms SMaj.g_R2
#print axioms SMaj.g_R3
#print axioms SMaj.g_R4
#print axioms SMaj.g_R4_eq
#print axioms SMaj.exists_avoid
#print axioms SMaj.isFill_exists_of_four_le
#print axioms SMaj.isFill_exists
#print axioms SMaj.side_count_lt_own
#print axioms SMaj.side_eq_singleton_of_degree_two
#print axioms SMaj.count_singleton_le
#print axioms SMaj.count_singleton_eq_zero
#print axioms SMaj.nColor_le_sides
#print axioms SMaj.twoChain_row_le
#print axioms SMaj.mem_satSet_iff
#print axioms SMaj.card_threshold_mul_le
#print axioms SMaj.card_satSet_le_two
#print axioms SMaj.satSet_eq_empty_of_ne
#print axioms SMaj.chainEnd_row_le
#print axioms SMaj.interior_row_le
#print axioms SMaj.l1_row_le

/- Lens C3L4-lean-six (campaign C3): the multigraph coloring engine
   (Shannon route, SMaj/Six/Shannon.lean). -/
#print axioms SMaj.isMulticoloring_of_zero
#print axioms SMaj.card_biUnion_eq_mdeg
#print axioms SMaj.decr_symm
#print axioms SMaj.decr_loopless
#print axioms SMaj.mdeg_decr_le
#print axioms SMaj.mdeg_decr_lt_left
#print axioms SMaj.mdeg_decr_lt_right
#print axioms SMaj.exists_multicoloring_of_le
#print axioms SMaj.exists_seven_coloring_of_mdeg_le_four
#print axioms SMaj.exists_three_coloring_of_mdeg_le_two
#print axioms SMaj.disjoint_loEmb_hiEmb
#print axioms SMaj.disjoint_map_emb
#print axioms SMaj.IsMulticoloring.combine
#print axioms SMaj.shannon_six_of_split
#print axioms SMaj.shannon_six_of_split_hypothesis

/- Lens C3L4-lean-six (campaign C3): the augmentation reduction of the
   2-split to its even-degree case (SMaj/Six/Euler.lean). -/
#print axioms SMaj.mdeg_decr_eq_left
#print axioms SMaj.mdeg_decr_eq_right
#print axioms SMaj.mdeg_decr_eq_other
#print axioms SMaj.sum_mdeg_decr
#print axioms SMaj.even_sum_mdeg
#print axioms SMaj.even_card_odd_mdeg
#print axioms SMaj.pairUnit_symm
#print axioms SMaj.pairUnit_loopless
#print axioms SMaj.mdeg_pairUnit
#print axioms SMaj.exists_pairing
#print axioms SMaj.two_split_restrict
#print axioms SMaj.two_split_of_even_split_hypothesis

/- Lens C4L3-lean-close (campaign C4): the closed Euler 2-split via
   balanced orientations, and Shannon at Δ = 4 (SMaj/Six/Euler.lean,
   SMaj/Six/Targets.lean). -/
#print axioms SMaj.mdeg_add_indeg
#print axioms SMaj.sum_dirUnit_row
#print axioms SMaj.sum_dirUnit_col
#print axioms SMaj.mdeg_add_dirUnit
#print axioms SMaj.indeg_add_dirUnit
#print axioms SMaj.pairUnit_comm
#print axioms SMaj.dirUnit_add_swap
#print axioms SMaj.decr_add_pairUnit
#print axioms SMaj.orient_core
#print axioms SMaj.exists_balanced_orientation
#print axioms SMaj.biMat_symm
#print axioms SMaj.biMat_loopless
#print axioms SMaj.mdeg_biMat_inl
#print axioms SMaj.mdeg_biMat_inr
#print axioms SMaj.exists_two_split_even
#print axioms SMaj.exists_two_split
#print axioms SMaj.shannon_six_of_maxDegree_four

/- Lens C5L3-lean-six (campaign C5): the even grouping (Master input 1,
   SMaj/Master.lean) and the row-dispatch half of the (G1)–(G5) glue
   (SMaj/Six/Glue.lean). -/
#print axioms SMaj.card_div_fiber_le
#print axioms SMaj.exists_even_grouping
#print axioms SMaj.row_comm
#print axioms SMaj.nColor_comm
#print axioms SMaj.exists_other_neighbor
#print axioms SMaj.strongMajority_of_glue
#print axioms SMaj.maj_le_six_of_glue

/- Lens C6L3-lean-construction (campaign C6): construction-half bricks —
   indexed-family Shannon transport and the pure-cycle distance-2
   coloring (SMaj/Six/Construct.lean). -/
#print axioms SMaj.famMatrix_symm
#print axioms SMaj.famMatrix_diag
#print axioms SMaj.mdeg_famMatrix
#print axioms SMaj.shannon_six_indexed
#print axioms SMaj.exists_cycle_distance2

/- Lens C7L3-lean-chaindecomp (campaign C7): chain-decomposition
   existence — pieces (threaded trails), the parity dichotomy, the
   walker, linkage closure, ports (SMaj/Six/ChainDecomp.lean). -/
#print axioms SMaj.end_eq_start_of_saturated
#print axioms SMaj.three_le_length_of_closed
#print axioms SMaj.exists_piece
#print axioms SMaj.IsPiece.three_le_length
#print axioms SMaj.IsPiece.saturated_of_degree_two
#print axioms SMaj.IsPiece.end_of_junction

/- Lens C8L3-lean-assembly (campaign C8): the partition/canonicality
   facts (linkage equivalence, closure, connectivity, edge-set
   uniqueness), the port-POSITION fact, and the slot calculus
   (SMaj/Six/Partition.lean). -/
#print axioms SMaj.edges_getElem
#print axioms SMaj.getVert_mem_internal
#print axioms SMaj.IsPiece.eq_first_or_last
#print axioms SMaj.LinkStep.symm
#print axioms SMaj.Linked.refl
#print axioms SMaj.Linked.symm
#print axioms SMaj.Linked.trans
#print axioms SMaj.Linked.mem_edgeSet
#print axioms SMaj.IsPiece.mem_of_linked
#print axioms SMaj.IsPiece.linked_of_mem
#print axioms SMaj.IsPiece.mem_edges_iff_linked
#print axioms SMaj.IsPiece.mem_edges_iff
#print axioms SMaj.IsPiece.edges_toFinset_eq
#print axioms SMaj.eq_or_eq_of_mem_edges_degree_two
#print axioms SMaj.IsPiece.two_le_length_of_snd
#print axioms SMaj.IsPiece.two_le_length_of_penultimate
#print axioms SMaj.IsPiece.edges_one_eq
#print axioms SMaj.IsPiece.edges_length_sub_two_eq
#print axioms SMaj.IsPiece.other_edge_slot_of_chain
#print axioms SMaj.IsPiece.other_edge_slot_of_cycle

/- Lens C8L3-lean-assembly session 2 (campaign C8): step 2 of the
   assembly — per-vertex grouping facts, the piece choice per linkage
   class, the M-node/member family, the per-node ≤ 4 bound, and the
   Shannon member coloring (SMaj/Six/Assembly.lean). -/
#print axioms SMaj.evenIx_fiber_le
#print axioms SMaj.groups_evenIx_le
#print axioms SMaj.evenIx_one_inj
#print axioms SMaj.glueIx_eq_junction
#print axioms SMaj.glueIx_eq_low
#print axioms SMaj.glueIx_fiber_le
#print axioms SMaj.groups_glueIx_le
#print axioms SMaj.glueIx_inj_low
#print axioms SMaj.glueIx_lt
#print axioms SMaj.Piece.chain_ends
#print axioms SMaj.Piece.cycle_spec
#print axioms SMaj.Piece.edges_length_pos
#print axioms SMaj.Piece.firstEdge_eq
#print axioms SMaj.Piece.lastEdge_eq
#print axioms SMaj.Piece.firstEdge_mem
#print axioms SMaj.Piece.lastEdge_mem
#print axioms SMaj.Piece.firstEdge_ne_lastEdge
#print axioms SMaj.Piece.a_ne_b_of_length_lt_three
#print axioms SMaj.exists_piece_through
#print axioms SMaj.classPiece_mem
#print axioms SMaj.classPiece_class_eq
#print axioms SMaj.out_mem_edgeSet
#print axioms SMaj.mem_pieceOf
#print axioms SMaj.pieceOf_eq_of_linked
#print axioms SMaj.pieceOf_eq_of_mem
#print axioms SMaj.pieceOf_port
#print axioms SMaj.nodeAt_eq_inl_iff
#print axioms SMaj.nodeAt_ne_inr
#print axioms SMaj.Piece.startNode_ne_endNode
#print axioms SMaj.mfam_not_isDiag
#print axioms SMaj.portEdge_mem
#print axioms SMaj.portEdge_spec
#print axioms SMaj.portEdge_inl_of_three_le
#print axioms SMaj.port_member_unique
#print axioms SMaj.mfam_count_junction
#print axioms SMaj.cls_eq_of_inr_mem
#print axioms SMaj.mfam_count_middle
#print axioms SMaj.member_port_start
#print axioms SMaj.member_port_end_long
#print axioms SMaj.member_port_end_short
#print axioms SMaj.exists_port_member
#print axioms SMaj.exists_member_coloring

/- Lens C9L3-lean-assembly (campaign C9): assembly steps 3-5 —
port/fill/cycle colorings, satSet agreement, the IsGlueColoring bundle,
and the headline maj_le_six (SMaj/Six/Final.lean). -/
#print axioms SMaj.idxOf_eq_of_getElem
#print axioms SMaj.Piece.three_le_length_of_cycle
#print axioms SMaj.Piece.cycle_slot
#print axioms SMaj.edgeClassOf_eq
#print axioms SMaj.col_inl_ne_inr
#print axioms SMaj.FxOf_card_le
#print axioms SMaj.FyOf_card_le
#print axioms SMaj.fillFun_isFill
#print axioms SMaj.cycleFun_spec
#print axioms SMaj.embed6_ne
#print axioms SMaj.glueColor_eq_classColor
#print axioms SMaj.portColor_eq_portClassColor
#print axioms SMaj.idxOf_firstEdge
#print axioms SMaj.idxOf_lastEdge
#print axioms SMaj.classColor_of_short
#print axioms SMaj.classColor_of_fill
#print axioms SMaj.classColor_of_cycle
#print axioms SMaj.glueColor_firstEdge
#print axioms SMaj.glueColor_lastEdge_long
#print axioms SMaj.glueColor_lastEdge_short
#print axioms SMaj.portColor_firstEdge
#print axioms SMaj.portColor_lastEdge_long
#print axioms SMaj.portColor_lastEdge_short
#print axioms SMaj.glueColor_portEdge
#print axioms SMaj.portColor_portEdge
#print axioms SMaj.glueColor_eq_portColor
#print axioms SMaj.satSet_glueColor_eq
#print axioms SMaj.glueColor_rainbow
#print axioms SMaj.glueColor_chain_end
#print axioms SMaj.glueColor_interior
#print axioms SMaj.exists_isGlueColoring
#print axioms SMaj.maj_le_six

/- Lens C10L3-lean-rainbow (campaign C10): the greedy rainbow route
   (SMaj/Greedy.lean) — rainbow_of_groupSizes stays the sole proof_wanted
   (it is Vizing); these are the greedy substitute + unconditional
   Master-Theorem corollaries. -/
#print axioms SMaj.isRainbow_of_isRainbowOn_edgeFinset
#print axioms SMaj.exists_rainbowOn
#print axioms SMaj.rainbow_of_groupSizes_greedy
#print axioms SMaj.IsRainbow.comp
#print axioms SMaj.rainbow_of_groupSizes_le_two
#print axioms SMaj.strongMajority_greedy_of_crit
#print axioms SMaj.strongMajority_five_of_no24
