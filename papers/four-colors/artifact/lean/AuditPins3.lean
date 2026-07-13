import Pins3

-- ============================================================================
-- Pins3 (STRIKE-A §9 ladder) audit.
-- PROVED items — must be standard axioms only (or sorryAx via tagged pins as
-- annotated).  All LADDER-PINs / the MERGE-PIN are sorry (sorryAx expected).
-- ============================================================================

-- PROVED outright (no pin dependencies):
#print axioms Rung4Moonshot.descent_of_no_bad_minimal
#print axioms Rung4Moonshot.deg3_lightness_parity

-- Ladder pins (sorry; sorryAx expected):
#print axioms Rung4Moonshot.toggle_valid_iff
#print axioms Rung4Moonshot.not_minimal_iff_exists_strict_toggle
-- W12 claws lane (§2 short-toggle laws): C1 + no_three_consecutive_deg3 CLOSED
-- via the r4w12_claws_a return (6 private helpers transplanted; even_path
-- sub-helper reproved to build in-env). Standard axioms only — CLOSED-GATED:
#print axioms Rung4Moonshot.C1_even_copath_of_minimal
#print axioms Rung4Moonshot.no_three_consecutive_deg3
-- W12 claws_b lane (r4w12_claws_b return, 2026-07-12): C2 + at_most_one_deg3_flank
-- CLOSED. C2 body transplanted sorry-free (standard axioms; deps toggle_valid_iff /
-- not_minimal_iff_exists_strict_toggle already closed). Three new helpers
-- transplanted (reachable_deleteEdges_of_cycle_edge, oddCycleSupports_toggled_isolated,
-- oddCycleSupports_toggled_cross); the return's `toggled_adj` COLLIDED (iff- vs
-- disjunction-form) with the canonical `toggled_adj` from the W12-separation lane,
-- so its disjunction form was transplanted as `toggled_adj_split` and the 3 refs
-- renamed. at_most_one_deg3_flank body transplanted sorry-free but INVOKES the still-
-- open pin C3_flank_structure_of_minimal → CLOSED-modulo-C3 (sorryAx via C3 only).
-- C3 (r4w12_claws_b) remained bare-sorry (the deg-4 "ledger" case) → STILL A PIN.
#print axioms Rung4Moonshot.toggled_adj_split
#print axioms Rung4Moonshot.reachable_deleteEdges_of_cycle_edge
#print axioms Rung4Moonshot.oddCycleSupports_toggled_isolated
#print axioms Rung4Moonshot.oddCycleSupports_toggled_cross
#print axioms Rung4Moonshot.C2_poison_target_Hfull_of_minimal
#print axioms Rung4Moonshot.C3_flank_structure_of_minimal
#print axioms Rung4Moonshot.at_most_one_deg3_flank
#print axioms Rung4Moonshot.three_edge_toggle_valid
#print axioms Rung4Moonshot.double_poisoner_separation
#print axioms Rung4Moonshot.poisoned_t2_shape
-- W12-canonical TRANSPLANT+GATE lane (2026-07-12): LADDER-PIN 9
-- canonical_strict_of_ellP_even body PROVED via the r4w12_canonical return
-- (Aristotle §6.2 εH-dichotomy/arc analysis). Statement byte-identical; 21 new
-- helpers transplanted (all axiom-CLEAN). Because the return's sibling pin
-- three_edge_toggle_valid was still a sorry in the return but is now PROVED in
-- this repo, the target is FULLY axiom-CLEAN [propext, Classical.choice,
-- Quot.sound] — NO sorryAx (not merely body-proved-modulo-sibling). Three
-- fragile `grind +suggestions` helper steps reproved in-env (statement byte-
-- identical, quirk): no_cycle_of_path_support via cycle_support_closed_adj /
-- degree_eq_two_of_mem_cycle_support (Pins2); hsep1_H via adj_eq_of_deg2;
-- toggled_H_repr via explicit edge-case ext proof. canonical_strict_of_ellP_even
-- is CLOSED and DROPS OFF the descent-chain sorry-source list (now 2 pins:
-- exists_alternating_euler_trail, strict_of_reach_geo).
#print axioms Rung4Moonshot.canonical_strict_of_ellP_even
#print axioms Rung4Moonshot.nonbip_void_t2

-- W16 pin-correction lane: supply_of_blocked CORRECTED (added hHodd) and
-- CLOSED via the r4w12_supply return; helpers PROVED (standard axioms only):
#print axioms Rung4Moonshot.supply_of_blocked
#print axioms Rung4Moonshot.supply_oddCount_K_of_odd_card
#print axioms Rung4Moonshot.supply_oddCount_H_of_even_card
#print axioms Rung4Moonshot.oddCycleCount_eq_oddComponents_ncard
#print axioms Rung4Moonshot.oddComponent_has_oddCycleSupport
#print axioms Rung4Moonshot.allDeg2_component_oddCycleSupport
#print axioms Rung4Moonshot.oddCycleSupport_fills_oddComponent
#print axioms Rung4Moonshot.path_closure
#print axioms Rung4Moonshot.path_support_eq_component
-- New pin (sorry; sorryAx expected) — the §6.2 even-C law, split out of
-- supply_avoids_anchors, which is now PROVED-modulo this pin:
#print axioms Rung4Moonshot.anchor_Kcycle_even

-- Round 15: routing core (§6.10). Helper PROVED, pins sorryAx, REACH held.
#print axioms Rung4Moonshot.Hfull_of_t2
#print axioms Rung4Moonshot.alt_walk_termination
-- crossing_selection: still a bare-sorry pin (r4w16 retry FAILED — body bare sorry).
#print axioms Rung4Moonshot.crossing_selection
-- W17 TRANSPLANT lane: strict_of_reach (LADDER-PIN 12d) body now PROVED via the
-- r4w13_strict_of_reach return; 5 private helpers transplanted (axiom-CLEAN);
-- one fragile `grind +suggestions` in deathK reproved in-env (statement byte-
-- identical). sorryAx on strict_of_reach is SOLELY via crossing_selection.
#print axioms Rung4Moonshot.strict_of_reach
-- W18a TRANSPLANT lane (2026-07-12): LADDER-PIN 12b-geo maximal_walk_cuts_poisoned
-- body PROVED via the r4w18a_walk_cuts return (statement byte-identical; helpers
-- oddCycleSupports_three_le_card / oddCycleSupport_Hdeg2 / cycle_support_closed_adj
-- already canonical, none transplanted). Axiom-CLEAN. crossing_selection_geo (12bc-geo)
-- consumes it but is itself a bare-sorry pin, so still sorryAx.
#print axioms Rung4Moonshot.maximal_walk_cuts_poisoned
-- Fable finisher lane (2026-07-13): crossing_selection_geo SUPERSEDED (union-
-- card too weak for the ledger); SUM-card pin crossing_selection_geo_sum added.
-- Fable SUM-PIN lane (2026-07-13, later the same day): BOTH walk-level pins
-- FALSIFIED by two independent fresh-look lenses (fresh-strike/
-- LENS-B3-SURGERY.md §1: n=9 counterexample, all 308 maximal walks give
-- new-odd SUM = 2, walk class Δω-parity-locked; fresh-strike/
-- LENS-B3-INVARIANT.md §1: independent CE1 + scalable corridor family CE2;
-- root cause = endpoint maximality forbids the odd-length q-stop). Both decls
-- are now COMMENTED falsification records in Pins3.lean (no longer auditable),
-- as is the equivalent cocircuit pin exists_low_birth_cocircuit authored and
-- falsified the same day. LIVE replacement pin: crossing_selection_toggle_sum
-- (TOGGLE level: ∃ valid toggle, dead-card ≥ 2, born-card ≤ 1; witness routes:
-- LENS-B3-SURGERY quad exchange / LENS-B3-INVARIANT free-stop — sorryAx
-- expected, the ONE open pin of the navigation route). strict_of_reach_geo
-- REWIRED to consume it by pure card accounting; expect sorryAx SOLELY via
-- crossing_selection_toggle_sum, and the same single source on
-- blocked_world_not_minimal / strict_merge_of_blocked /
-- strict_descent_of_no_clean_transversal_t2. The balanced-cocircuit
-- realization machinery (maximal_walk_of_balanced_cocircuit + balanced
-- transition existence + covers-variant) is TRUE and PROVED — expect
-- axiom-CLEAN; it is the realization arm of the free-stop route.
-- Fable TOGGLE lane (2026-07-13, successor prover): route-B/route-A shared
-- infrastructure PROVED (expect axiom-CLEAN [propext, Classical.choice,
-- Quot.sound]): alt_trail_incidence_count (exact per-vertex germ ledger of an
-- alternating trail, no maximality), freestop_toggle_valid (LENS-B3-INVARIANT
-- §4 free-stop validity law — the witness-family widening past endpoint
-- maximality), alt_circuit_toggle_valid (even alternating circuits always
-- valid), toggled_toggled / toggle_compose (toggles compose through symmDiff),
-- quad_valid (LENS-B3-SURGERY §4 primitive, proved as an even alternating
-- 4-circuit). NEW SELECT-pin exists_low_birth_freestop_cocircuit (walk-free,
-- transition-system formalism per the STRIKE-C route preference, hmin-carrying,
-- NO q-germ marks — the falsified cocircuit pin's over-restriction dropped;
-- corpus-validated in fresh-strike/PREVALIDATE-FREESTOP.md: ~12,500 instances,
-- 130 prior-hard cex, 0 failures) — expect sorryAx, THE one live pin of the
-- navigation route. crossing_selection_toggle_sum: statement BYTE-UNTOUCHED,
-- bare sorry replaced by the PROVED route-B assembly
-- (maximal_walk_of_balanced_cocircuit realization + odd length from the
-- odd-card conjunct + freestop_toggle_valid + ledger conjuncts verbatim) —
-- expect sorryAx SOLELY via exists_low_birth_freestop_cocircuit, and the same
-- single source down the chain (strict_of_reach_geo, blocked_world_not_minimal,
-- strict_merge_of_blocked, strict_descent_of_no_clean_transversal_t2).
-- PARITY-SPLIT lane (2026-07-13, after the three wave-21 no-closes):
-- exists_low_birth_freestop_cocircuit's statement is BYTE-UNTOUCHED but its
-- body is now the PROVED parity-split assembly — EVEN p–q H-path discharged
-- via canonical_strict_of_ellP_even + not_minimal_iff_exists_strict_toggle
-- (both PROVED); ODD case reduced to the NEW frozen sub-pin
-- exists_low_birth_freestop_cocircuit_odd (sorry; sorryAx expected — THE one
-- open pin of the t ≤ 2 navigation route; also feeds the general descent
-- alongside genxsel_general + nonbip_pierced_general). The wave-22
-- debris-connectivity strengthening was FALSIFIED computationally BEFORE
-- authoring (fresh-strike/FALSIFY-DEBRIS-CONNECTIVITY.md) and was NOT
-- authored: j_H=1 ∧ j_K=1 (and every connectivity-flavored weakening tested)
-- fails on hypothesis-passing instances; only the ledger-only conclusion
-- survives corpus-wide. Expect: the whole t2 chain's sorryAx flows SOLELY via
-- exists_low_birth_freestop_cocircuit_odd.
#print axioms Rung4Moonshot.alt_trail_incidence_count
#print axioms Rung4Moonshot.freestop_toggle_valid
#print axioms Rung4Moonshot.alt_circuit_toggle_valid
#print axioms Rung4Moonshot.toggled_toggled
#print axioms Rung4Moonshot.toggle_compose
#print axioms Rung4Moonshot.quad_valid
#print axioms Rung4Moonshot.exists_low_birth_freestop_cocircuit_odd
#print axioms Rung4Moonshot.exists_low_birth_freestop_cocircuit
#print axioms Rung4Moonshot.crossing_selection_toggle_sum
#print axioms Rung4Moonshot.strict_of_reach_geo
#print axioms Rung4Moonshot.maximal_walk_of_balanced_cocircuit
#print axioms Rung4Moonshot.isMaximalAltWalk_of_edges_sdiff
#print axioms Rung4Moonshot.cycle_two_distinct_nbrs
#print axioms Rung4Moonshot.strict_of_reach_deathH
#print axioms Rung4Moonshot.strict_of_reach_deathK
#print axioms Rung4Moonshot.walk_incidence_parity
#print axioms Rung4Moonshot.toggled_K_deg_start_le_one

-- Round 17: NAVIGATE sharpening (§6.10.5 pass 4).
-- W14 pin-correction lane (2026-07-12): double_visit_exhaustion CORRECTED
-- (added hup : u ≠ p) and CLOSED. The original statement was FALSE in the
-- corner u = p ∧ u ∉ X (a maximal alt-trail may revisit its own start using
-- both K-germs plus one H-edge, leaving s(p,x) unused and X uncut); it is
-- retained commented-out as double_visit_exhaustion_ORIGINAL. Closure via the
-- r4w14_double_visit return's companion double_visit_exhaustion_of_ne_start
-- + 3 transplanted helpers (all PROVED, standard axioms only). At the sole
-- live call site (reach_of_navchar) hup is discharged from hu4 + hp3.
#print axioms Rung4Moonshot.edge_getVert_mem
#print axioms Rung4Moonshot.walkCuts_of_mem_support_oddK
#print axioms Rung4Moonshot.double_visit_uses_H_edge
#print axioms Rung4Moonshot.double_visit_exhaustion_of_ne_start
#print axioms Rung4Moonshot.double_visit_exhaustion
-- Round 18: attainability law (§6.10.6 pass 5).
#print axioms Rung4Moonshot.anchor_obstruction_analysis
#print axioms Rung4Moonshot.supply_avoids_anchors
#print axioms Rung4Moonshot.germ_flip
-- Round 19 (fresh-strike EULER ROUTE, 2026-07-12): navchar_of_blocked's body
-- is now the PROVED assembly Euler-trail ⇒ cut-the-supply; its sorryAx flows
-- SOLELY via PIN EULER-A (exists_alternating_euler_trail — the one classical
-- Kotzig lemma, Aristotle target). EULER-B (isMaximalAltWalk_of_all_edges)
-- and EULER-C (oddCycleSupport_has_internal_edge) are PROVED (standard
-- axioms only). Route: fresh-strike/LENS-MECHANISM.md + LENS-CYCLESPACE.md
-- + LEAD-TOGGLE.md (three independent derivations, converged).
-- EULER-A CLOSED (2026-07-13, Fable prover lane): both helpers proved —
-- anchorComponent_covers_K_of_maximal (transition-pairing crossover exchange;
-- structural key not_sameCycle_reverse) and walk_of_anchorComponent_covers_K
-- (pure-data orbit extraction with explicit getVert spec), transplanted from
-- the fresh-strike drops (commit d03ee88) plus the walkOfIsChain_edges
-- one-token IH repair. exists_alternating_euler_trail and navchar_of_blocked
-- are now axiom-CLEAN [propext, Classical.choice, Quot.sound] — NO sorryAx.
-- Double-confirmed in an independent harness (r4cdx; the Fable lane built in
-- r4fableeuler + Modal farm): full lake build GREEN, fresh scratch audit +
-- sorry-source walker. The live navigation descent chain now has ONE open
-- pin: strict_of_reach_geo.
#print axioms Rung4Moonshot.exists_alternating_euler_trail
#print axioms Rung4Moonshot.isMaximalAltWalk_of_all_edges
#print axioms Rung4Moonshot.oddCycleSupport_has_internal_edge
#print axioms Rung4Moonshot.navchar_of_blocked
-- W17 TRANSPLANT lane: reach_of_navchar body PROVED via the
-- r4w16_reach_navchar return (proves the CURRENT round-18 disjunction form,
-- token-diff exact; self-contained, +maxHeartbeats 1200000). Its former sole
-- sorryAx source was double_visit_exhaustion; after the W14 pin correction
-- (2026-07-12) reach_of_navchar is axiom-CLEAN [propext, Classical.choice,
-- Quot.sound].
#print axioms Rung4Moonshot.reach_of_navchar
-- REACH + Theorem K: PROVED threads (sorryAx via the pins only):
#print axioms Rung4Moonshot.reach_of_blocked
#print axioms Rung4Moonshot.blocked_world_not_minimal
-- Former MERGE-PIN, now a PROVED thread (sorryAx via routing pins only):
#print axioms Rung4Moonshot.strict_merge_of_blocked

-- PROVED threads (sorryAx solely via the tagged pins):
#print axioms Rung4Moonshot.no_poisoned_of_minimal_t2
#print axioms Rung4Moonshot.strict_descent_of_no_clean_transversal_t2

-- W16 anchor-even TRANSPLANT (2026-07-12): anchor_Kcycle_even CLOSED via the
-- r4w16_anchor_even Aristotle return (14 new helpers, two contiguous blocks;
-- statement token-diff exact; zero name collisions). Expect
-- [propext, Classical.choice, Quot.sound] — NO sorryAx — on all of these; and
-- supply_avoids_anchors flips to fully proved (it was PROVED-modulo-this-pin).
#print axioms Rung4Moonshot.twoReg_oddCycleCount_eq_oddComponents
#print axioms Rung4Moonshot.maxDeg2_oddCycleCount_eq_cycleComponents
#print axioms Rung4Moonshot.oddCycleCount_addEdge_le_succ
#print axioms Rung4Moonshot.no_odd_Kcycle_of_even_component
#print axioms Rung4Moonshot.edge_mem_odd_cycle_of_component_odd
#print axioms Rung4Moonshot.edge_mem_cycle_of_deg2
#print axioms Rung4Moonshot.cycle_two_cut_sep
#print axioms Rung4Moonshot.toggled_H_le
#print axioms Rung4Moonshot.triangle_of_support3
#print axioms Rung4Moonshot.toggled_K_lt
#print axioms Rung4Moonshot.move_contra
#print axioms Rung4Moonshot.anchor_component_even
#print axioms Rung4Moonshot.anchor_Kcycle_even
#print axioms Rung4Moonshot.supply_avoids_anchors

-- MIGRATION ROUTE (fresh-strike LENS-NONEXISTENCE, authored 2026-07-12):
-- pin (a) H-side Δ-ledger = toggled_H_le (PROVED, from the W16 transplant);
-- pin (b) K-side subsumed by canonical_K_count_le + minimality
-- (anchor_Kcycle_even is NOT consumed by this chain even though now proved);
-- pin (c) mig_unpoisons CLOSED 2026-07-13 (W20 transplant, r4w20_mig_direct
-- run 2d03aaed; redundant clean close r4w20_mig_structured run d927c059 gated
-- but not transplanted).  Expect axiom-CLEAN [propext, Classical.choice,
-- Quot.sound] on all four decls below (farm-gated 2026-07-13, walls
-- 447.8s/499.4s; statement byte-identical incl. load-bearing hsel/hR).
-- migration_step / migration_descent / migration_safe_split_placement_t2:
-- now UNCONDITIONAL via mig_unpoisons.  The last is the t ≤ 2 existential
-- placement (what exists_safe_split_placement/strongMajority_of_safe_defects
-- consume) — an ALTERNATIVE route bypassing exists_alternating_euler_trail,
-- strict_of_reach_geo AND strict_descent_of_no_clean_transversal_t2 itself
-- (which is kept intact: its statement fixes the split, the migration cannot
-- feed it — see the migration section header in Pins3.lean).
#print axioms Rung4Moonshot.mig_unpoisons
#print axioms Rung4Moonshot.migration_step
#print axioms Rung4Moonshot.migration_descent
#print axioms Rung4Moonshot.migration_safe_split_placement_t2

-- GENERAL-t LADDER lane (2026-07-13; STRIKE-C §7, referee-adjudicated by
-- STRIKE-C-REFEREE + GL-CENSUS-AUDIT). PROVED items — expect axiom-CLEAN
-- [propext, Classical.choice, Quot.sound]: item 1 (slot profile + parity),
-- item 3 (per-trail + union validity via the SlotBalanced engine; t-uniform,
-- subsumes the freestop witness family), the cocircuit-balance bridge
-- (walk-free validity of E∖F complements), and item 5 (the walk-free death
-- engine generalizing strict_of_reach_deathH/deathK).
#print axioms Rung4Moonshot.slot_profile_parity
#print axioms Rung4Moonshot.numDeg3_even
#print axioms Rung4Moonshot.slotBalanced_valid_toggle
#print axioms Rung4Moonshot.slotBalanced_congr
#print axioms Rung4Moonshot.slotBalanced_union
#print axioms Rung4Moonshot.mt_trail_slotBalanced
#print axioms Rung4Moonshot.mt_trail_valid_toggle
#print axioms Rung4Moonshot.mt_union_valid_toggle
#print axioms Rung4Moonshot.filter_sdiff_incidence_card
#print axioms Rung4Moonshot.slotBalanced_of_cocircuit
#print axioms Rung4Moonshot.cut_supports_die_general
-- General-t pins (sorry; sorryAx expected): item 2 (Theorem MT — with the
-- AP1 merge-to-single constructive sub-obligation named in its docstring),
-- item 6 (Proposition ANCHOR), item 7 (GEN-XSEL — THE HELD PIN, shape-shared
-- with exists_low_birth_freestop_cocircuit; do-not-diverge note in both
-- directions), item 8 (§5 parametric-budget Hall). Item 4 (GL) is FUSED into
-- genxsel_general's ledger conclusion per the header item-11 precedent.
#print axioms Rung4Moonshot.exists_mt_decomposition
#print axioms Rung4Moonshot.anchored_cut_of_poisoned
#print axioms Rung4Moonshot.genxsel_general
#print axioms Rung4Moonshot.nonbip_pierced_general
-- Assembly (item 9; PROVED modulo pins). Expected sorry sources:
-- no_poisoned_of_minimal_general — genxsel_general + the t ≤ 2 chain's pins;
-- nonbip_void_general — nonbip_pierced_general (+ t ≤ 2 leg);
-- strict_descent_of_no_clean_transversal_general — the union of both
-- branches' NAMED pins and nothing else (sorry-source walker is the gate).
#print axioms Rung4Moonshot.no_poisoned_of_minimal_general
#print axioms Rung4Moonshot.nonbip_void_general
#print axioms Rung4Moonshot.strict_descent_of_no_clean_transversal_general

-- CONSUMER-REWIRE lane (2026-07-13): the t ≤ 2 TOP THEOREM. Pins2's final
-- chain consumes clean_transversal_of_minimal at ONE existentially chosen
-- minimal split only (exists_oddCycleMinimal_split, Pins2 L3253); the
-- migration route's migration_safe_split_placement_t2 supplies that exact
-- existential shape at t ≤ 2, so R4_three_four_connected_t2/R4_three_four_t2
-- re-assemble the PROVED Pins2 downstream (strongMajority_of_safe_defects +
-- component lift) with NO use of strict_descent_of_no_clean_transversal and
-- no hII. With mig_unpoisons CLOSED (W20, same day) the theorems are
-- UNCONDITIONAL: expect axiom-CLEAN [propext, Classical.choice, Quot.sound]
-- — NO sorryAx — on all three decls below (walker-gated: zero sorry-sources
-- in the transitive closure). First gate passed 2026-07-13 in r4cdx on the
-- structured-return bytes (superseded by the direct transplant landing in
-- 43f70c9); canonical gate re-run on the merged bytes same day. Scope: at
-- most two degree-3 vertices; NOT the full mixed class (general t open;
-- Pins2 L2932 undischarged; R4_three_four unchanged).
#print axioms Rung4Moonshot.numDeg3_induce_le
#print axioms Rung4Moonshot.R4_three_four_connected_t2
#print axioms Rung4Moonshot.R4_three_four_t2
