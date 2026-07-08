import UCFrankl

/-!
Axiom audit for the UCFrankl development. Run via
`lake env lean scripts\CheckAxioms.lean` from the project root.
Accept criterion: every theorem depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, nothing else.
-/

#print axioms UCFrankl.card_le_two_mul_freq_of_singleton_mem
#print axioms UCFrankl.frankl_of_singleton_mem
#print axioms UCFrankl.entropy_nonneg
#print axioms UCFrankl.entropy_le_log_card_of_support_subset
#print axioms UCFrankl.isPMF_uniformOn
#print axioms UCFrankl.entropy_uniformOn
#print axioms UCFrankl.isPMF_pushforward₂
#print axioms UCFrankl.pushforward₂_eq_zero
#print axioms UCFrankl.marginal_uniformOn
#print axioms UCFrankl.franklWithConstant_of_gilmerEngine
#print axioms UCFrankl.psi_pos
#print axioms UCFrankl.psi_lt_half
#print axioms UCFrankl.two_mul_psi_sub_sq
#print axioms UCFrankl.binEntropy_at_psi
#print axioms UCFrankl.binEntropy_le_binEntropy_union

-- C2L4 Lean-bridge layer (campaign C2): conditional entropy core
#print axioms UCFrankl.condBit_eq
#print axioms UCFrankl.condBit_nonneg
#print axioms UCFrankl.condBit_add_condBit_le
#print axioms UCFrankl.sum_condBit_le
#print axioms UCFrankl.isPMF_fstMarg
#print axioms UCFrankl.entropy_eq_fstMarg_add_condH
#print axioms UCFrankl.condH_nonneg

-- C2L4 Lean-bridge layer: engine reduction to the WeakBoppana scalar atom
#print axioms UCFrankl.massKey_of_weakBoppana
#print axioms UCFrankl.orPush_apply_false
#print axioms UCFrankl.orPush_apply_true
#print axioms UCFrankl.fstMarg_orPush
#print axioms UCFrankl.condH_orPush_ge
#print axioms UCFrankl.entropy_comp_equiv
#print axioms UCFrankl.isPMF_comp_equiv
#print axioms UCFrankl.pushforward₂_comp_equiv
#print axioms UCFrankl.bitMarginal_zero_eq
#print axioms UCFrankl.bitMarginal_succ_eq
#print axioms UCFrankl.sum_false_eq_one_sub
#print axioms UCFrankl.entropy_orPush_ge
#print axioms UCFrankl.finsetBoolEquiv_union
#print axioms UCFrankl.bitMarginal_finsetBoolEquiv
#print axioms UCFrankl.gilmerEngine_of_weakBoppana
#print axioms UCFrankl.franklWithConstant_of_weakBoppana
#print axioms UCFrankl.franklWithConstant_centile_of_weakBoppana
#print axioms UCFrankl.franklWithConstant_of_forall_lt
#print axioms UCFrankl.franklWithConstant_psi_of_weakBoppana

-- C3L1 layer (campaign C3): the Ho atom (vendored port, arXiv:2601.19327)
#print axioms UCFrankl.HoBoppana.alpha_spec
#print axioms UCFrankl.HoBoppana.generalized_boppana
#print axioms UCFrankl.HoBoppana.generalized_boppana_full

-- C3L1 layer: diagonal reduction + the closed atom + unconditional theorems
#print axioms UCFrankl.continuous_etaCL
#print axioms UCFrankl.hasDerivAt_etaCL
#print axioms UCFrankl.hasDerivAt_etaCL'
#print axioms UCFrankl.etaCL''_nonpos
#print axioms UCFrankl.concaveOn_etaCL
#print axioms UCFrankl.etaCL_add_le
#print axioms UCFrankl.mul_etaCL_neg_log
#print axioms UCFrankl.negMulLog_one_sub_diag
#print axioms UCFrankl.mul_binEntropy_add_le
#print axioms UCFrankl.hoAlpha_two
#print axioms UCFrankl.sharp_boppana_diag
#print axioms UCFrankl.weakBoppana_sharp
#print axioms UCFrankl.weakBoppana_mono
#print axioms UCFrankl.weakBoppana_eleven_twentieths
#print axioms UCFrankl.gilmerEngine_of_lt_psi
#print axioms UCFrankl.franklWithConstant_psi
#print axioms UCFrankl.franklWithConstant_centile

-- C4L4 layer (campaign C4): decide-based census regression tests (N5.5)
#print axioms UCFrankl.fc5_card
#print axioms UCFrankl.fc5_unionClosed
#print axioms UCFrankl.fc5_freq_uniform
#print axioms UCFrankl.fc5_majority
#print axioms UCFrankl.powersetFin3_card
#print axioms UCFrankl.powersetFin3_unionClosed
#print axioms UCFrankl.powersetFin3_freq
#print axioms UCFrankl.gapless3_card
#print axioms UCFrankl.gapless3_unionClosed
#print axioms UCFrankl.gapless3_freq
#print axioms UCFrankl.gapless3_traceShearer

-- C4L4 layer: T-A formalization start (ULC + Gibbs engine identity)
#print axioms UCFrankl.ulcOn_of_unionMonotoneOn
#print axioms UCFrankl.ulcOn_uniformOn
#print axioms UCFrankl.negMulLog_eq_mul_neg_log_sub
#print axioms UCFrankl.entropy_eq_crossEntropy_sub_klDiv
#print axioms UCFrankl.entropy_sub_entropy_eq_inner_sub_klDiv

-- C6L4 layer (campaign C6): leakage scale (LeakageScale.lean)
#print axioms UCFrankl.subMass_nonneg
#print axioms UCFrankl.subMass_mono
#print axioms UCFrankl.subMass_eq_zero_of_forall_le
#print axioms UCFrankl.mem_leakAdmissible
#print axioms UCFrankl.min_budget_minMass_mem
#print axioms UCFrankl.leakAdmissible_nonempty
#print axioms UCFrankl.leakScale_mem
#print axioms UCFrankl.subMass_leakScale_le
#print axioms UCFrankl.leakScale_pos
#print axioms UCFrankl.leakScale_le_budget
#print axioms UCFrankl.min_le_leakScale
#print axioms UCFrankl.leakScale_mono_budget
