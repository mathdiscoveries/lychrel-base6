/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LychrelBase6

/-!
# Axiom Verification Audit for `LychrelBase6`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `LychrelBase6`. A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Definitions, base-6 digit-list bridge, and README hand checks (Defs.lean)
#print axioms LychrelBase6.IsLychrel6.no_pal_pos
#print axioms LychrelBase6.ValidMSB6.validLSB6_reverse
#print axioms LychrelBase6.digits_ofDigits_validLSB6
#print axioms LychrelBase6.digits_ofDigits6MSB
#print axioms LychrelBase6.rev6_ofDigits6MSB
#print axioms LychrelBase6.isPalindrome6_ofDigits6MSB
#print axioms LychrelBase6.ofDigits6MSB_inj
#print axioms LychrelBase6.ofDigits6_append
#print axioms LychrelBase6.ofDigits6_lt_pow_length
#print axioms LychrelBase6.pow_length_sub_one_le_ofDigits6MSB
#print axioms LychrelBase6.ofDigits6MSB_lt_of_length_lt
#print axioms LychrelBase6.ofDigits6_addLSB6Aux
#print axioms LychrelBase6.addLSB6Aux_length
#print axioms LychrelBase6.addLSB6Aux_digits_lt
#print axioms LychrelBase6.addLSB6Aux_carry_le
#print axioms LychrelBase6.addLSB6Aux_append
#print axioms LychrelBase6.ofDigits6MSB_revAddMSB6
#print axioms LychrelBase6.revAddMSB6_valid
#print axioms LychrelBase6.digits_revAdd6_ofDigits6MSB
#print axioms LychrelBase6.revAddMSB6_iterate_valid
#print axioms LychrelBase6.revAdd6_iterate_ofDigits6MSB
#print axioms LychrelBase6.isPalindrome6_revAdd6_iterate_ofDigits6MSB
#print axioms LychrelBase6.revAdd6_1079
#print axioms LychrelBase6.rev6_1079
#print axioms LychrelBase6.digits6_2373
#print axioms LychrelBase6.revAdd6_four_196
#print axioms LychrelBase6.isPalindrome6_revAdd6_four_196

-- Lemma C, Lemma S carry-automaton engine, and induction principles (CarryEngine.lean)
#print axioms LychrelBase6.validForm_of_bool
#print axioms LychrelBase6.ValidForm.validMSB6
#print axioms LychrelBase6.evalForm_length
#print axioms LychrelBase6.evalForm_reverse
#print axioms LychrelBase6.carry_pair_sum_five
#print axioms LychrelBase6.addLSB6Aux_replicate
#print axioms LychrelBase6.stepForm_eval
#print axioms LychrelBase6.stepForm_sound
#print axioms LychrelBase6.form_not_palindrome
#print axioms LychrelBase6.allValidBefore_of_le
#print axioms LychrelBase6.validForm_stepFormN_of_lt
#print axioms LychrelBase6.stepFormN_ov_mono
#print axioms LychrelBase6.stepFormN_sound
#print axioms LychrelBase6.stepFormN_no_pal
#print axioms LychrelBase6.evalForm_regroup
#print axioms LychrelBase6.formVal_regroup
#print axioms LychrelBase6.checkSymbolicPattern_sound
#print axioms LychrelBase6.checkSymbolicPattern_of_chain
#print axioms LychrelBase6.checkDirectCycleAux_sound
#print axioms LychrelBase6.directCycle_sound
#print axioms LychrelBase6.lychrel6_of_period_shift

-- Both infinite base-6 Lychrel families x(m) and y(m) (Families.lean)
#print axioms LychrelBase6.overflowPattern12_prefix_count
#print axioms LychrelBase6.xForm0_valid
#print axioms LychrelBase6.xFam_digits_length
#print axioms LychrelBase6.xForm0_symbolic_cert
#print axioms LychrelBase6.xFam_symbolic
#print axioms LychrelBase6.xFam_cycle_and_no_pal
#print axioms LychrelBase6.xFam_step12
#print axioms LychrelBase6.xFam_no_pal_lt12
#print axioms LychrelBase6.xFam_lychrel
#print axioms LychrelBase6.xFam_lychrel_pos
#print axioms LychrelBase6.xFam_strictMono
#print axioms LychrelBase6.xFam_zero_eq
#print axioms LychrelBase6.yForm0_valid
#print axioms LychrelBase6.yFam_digits_length
#print axioms LychrelBase6.yM_eq_complement_xM
#print axioms LychrelBase6.yForm0_symbolic_cert
#print axioms LychrelBase6.yFam_symbolic
#print axioms LychrelBase6.yFam_cycle_and_no_pal
#print axioms LychrelBase6.yFam_step12
#print axioms LychrelBase6.yFam_no_pal_lt12
#print axioms LychrelBase6.yFam_lychrel
#print axioms LychrelBase6.yFam_lychrel_pos
#print axioms LychrelBase6.yFam_strictMono
#print axioms LychrelBase6.yFam_zero_eq
#print axioms LychrelBase6.xFam_disjoint_yFam
#print axioms LychrelBase6.infinite_lychrel6

-- Complement duality, center-automaton isomorphism φ, six-seed orbits, and counting (DualityAndCounting.lean)
#print axioms LychrelBase6.compDigit6_lt_six
#print axioms LychrelBase6.compDigit6_involutive
#print axioms LychrelBase6.compList6_length
#print axioms LychrelBase6.compList6_digits_lt
#print axioms LychrelBase6.compList6_involutive
#print axioms LychrelBase6.compList6_append
#print axioms LychrelBase6.compList6_reverse
#print axioms LychrelBase6.compList6_replicate
#print axioms LychrelBase6.compList6_runs_swap
#print axioms LychrelBase6.runDigit_of_comp_carry
#print axioms LychrelBase6.column_complement_duality
#print axioms LychrelBase6.addLSB6Aux_compList6
#print axioms LychrelBase6.center_block_complement_duality
#print axioms LychrelBase6.ValidForm.carries_le_one
#print axioms LychrelBase6.stepForm_center_duality
#print axioms LychrelBase6.yForm0_M_eq_compList6
#print axioms LychrelBase6.xChain_yChain_center_duality
#print axioms LychrelBase6.stepFormN_eq_of_chain
#print axioms LychrelBase6.xChain_check
#print axioms LychrelBase6.yChain_check
#print axioms LychrelBase6.stepFormN_xForm0_eq
#print axioms LychrelBase6.stepFormN_yForm0_eq
#print axioms LychrelBase6.stepFormN_xForm0_yForm0_duality
#print axioms LychrelBase6.xForms_yForms_carry_signals
#print axioms LychrelBase6.stepFormN_carries_duality
#print axioms LychrelBase6.sum_complement_div_mod
#print axioms LychrelBase6.phiPhase_valid_and_involutive
#print axioms LychrelBase6.phiCol_valid_and_involutive
#print axioms LychrelBase6.phiState_valid_and_involutive
#print axioms LychrelBase6.phiCenterNode_valid_and_involutive
#print axioms LychrelBase6.startCenterNode_phi
#print axioms LychrelBase6.mem_fullColumn_bounds
#print axioms LychrelBase6.mem_fullColumn_phi_imp
#print axioms LychrelBase6.mem_fullColumn_phi
#print axioms LychrelBase6.mem_advanceAux_valid
#print axioms LychrelBase6.mem_advanceAux_phi_imp
#print axioms LychrelBase6.centerEdge_valid
#print axioms LychrelBase6.centerEdge_phi
#print axioms LychrelBase6.centerPath_phi
#print axioms LychrelBase6.closes_phi
#print axioms LychrelBase6.rev6_pos
#print axioms LychrelBase6.lt_revAdd6
#print axioms LychrelBase6.revAdd6_iterate_pos
#print axioms LychrelBase6.revAdd6_iterate_strictMono
#print axioms LychrelBase6.IsLychrel6.iterate
#print axioms LychrelBase6.digits6_xFam_length
#print axioms LychrelBase6.digits6_yFam_length
#print axioms LychrelBase6.xFam_pow_bounds
#print axioms LychrelBase6.yFam_pow_bounds
#print axioms LychrelBase6.xFam_pos
#print axioms LychrelBase6.yFam_pos
#print axioms LychrelBase6.xFam_iterate_twelve_mul
#print axioms LychrelBase6.yFam_iterate_twelve_mul
#print axioms LychrelBase6.xFam_eq_seed_iterate
#print axioms LychrelBase6.yFam_eq_seed_iterate
#print axioms LychrelBase6.xFam_iterate_lychrel
#print axioms LychrelBase6.yFam_iterate_lychrel
#print axioms LychrelBase6.xFam_iterate_lt12_eq_formVal
#print axioms LychrelBase6.yFam_iterate_lt12_eq_formVal
#print axioms LychrelBase6.digits6_iterate_xFam_length
#print axioms LychrelBase6.digits6_iterate_yFam_length
#print axioms LychrelBase6.iterate_xFam_pow_bounds
#print axioms LychrelBase6.iterate_yFam_pow_bounds
#print axioms LychrelBase6.xSeed_orbits_inj
#print axioms LychrelBase6.ySeed_orbits_inj
#print axioms LychrelBase6.xFam_orbit_ne_yFam_orbit
#print axioms LychrelBase6.xSeed_trajectories_disjoint
#print axioms LychrelBase6.ySeed_trajectories_disjoint
#print axioms LychrelBase6.xFam_yFam_trajectories_disjoint
#print axioms LychrelBase6.sixSeedMap_pos_and_lychrel
#print axioms LychrelBase6.sixSeedMap_length_and_lt_pow
#print axioms LychrelBase6.sixSeedMap_injective
#print axioms LychrelBase6.mem_familyOrbitsFinset_properties
#print axioms LychrelBase6.familyOrbitsFinset_card
#print axioms LychrelBase6.familyOrbitsFinset_card_of_ge
#print axioms LychrelBase6.familyOrbitsFinset_card_even
#print axioms LychrelBase6.familyOrbitsFinset_card_period
#print axioms LychrelBase6.lychrel6_ncard_lt_pow_ge
#print axioms LychrelBase6.lychrel6_ncard_le_pow_ge
#print axioms LychrelBase6.lychrel6_ncard_le_pow_110_add_two_mul
#print axioms LychrelBase6.lychrel6_ncard_le_pow_110_add_six_mul
