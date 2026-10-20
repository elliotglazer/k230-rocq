(** The substantive chosen-level PH step: actual KF, PCf and Dn proofs
    yield a witness in the target carrier via the actual hierarchy subset. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution
 SourceHierarchySyntax SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionProofs
 SourceEwMonotone SourceEwAtSyntax SourceRelativizationBounds SourceRawSubset
 SourceDnEliminationInvariant SourcePieceWitnessParameters SourcePieceConjunctionWitness
 SourceReflectionKFWitness SourceReflectionKFWitnessUse.
Unset Implicit Arguments.
Theorem source_full_reflection_chosen_witness M domain level sb sc count K k w witness X lk Y lw Lb subset goal
 entry params phi pb pC ub uc un phi' gb gc gn bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->
 source_LL_instance M k X lk ->source_LL_instance M w Y lw ->source_raw_subset_graph M Y Lb subset ->
 substitution_lift M pb pC params(zeroM M)ub uc un ->numerical_substitution M phi ub uc un(code_numeral M 1)phi' ->
 source_dn_parameter_proofs M params pb pC X gb gc gn ->source_ew_at M domain phi' Lb goal ->
 context_bounded M gb gc gn bound ->coding_lt M w bound ->coding_lt M X bound ->coding_lt M Y bound ->coding_lt M Lb bound ->
 source_bounded M phi'(succM M bound) ->
 source_full_prv M gb gc gn witness ->source_full_prv M gb gc gn lk ->source_full_prv M gb gc gn lw ->
 source_full_prv M gb gc gn subset ->source_full_prv M gb gc gn goal.
Proof.
 intros HD HL HLg HV HEntry HPair HW HLevelK HLevelW HSubset HU HMatrix HMembers HEGoal
  HC BW BX BY BLb BMatrix PW PLK PLW PS.
 destruct(source_piece_conjunction_total M domain level sb sc count w X)as(all&HAll).
 pose proof(source_full_reflection_KF_witness_pc M domain level sb sc count K k w witness X lk all gb gc gn
  HD HL HV HW HLevelK HAll PW PLK)as PAll.
 destruct(source_pc_instance_total M domain level params phi w X)as(pc&HPC).
 pose proof(source_piece_conjunction_project M count domain level sb sc w X all gb gc gn bound
  HD HL HV BW BX HC HAll PAll entry params phi pc HEntry HPair HPC)as PPC.
 destruct(source_ew_at_total M domain phi' Y)as(ew&HEw).
 pose proof(source_full_pc_parameter_witness M domain level params phi w X pc pb pC ub uc un phi' Y lw ew
  gb gc gn(succM M bound)HD HL HLg(HV entry params phi HEntry HPair)BMatrix HPC HU HMatrix HMembers HLevelW HEw PPC PLW)as PEw.
 exact(source_full_ew_monotone M gb gc gn bound domain phi' Y Lb subset ew goal HC
  (sr_domain_bound_succ M domain bound HD)BMatrix BY BLb HSubset HEw HEGoal PS PEw).
Qed.
Theorem source_full_reflection_chosen_initial_witness M domain level sb sc count K k w witness X lk Y lw Lb subset goal
 entry params phi gb gc gn bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->
 source_LL_instance M k X lk ->source_LL_instance M w Y lw ->source_raw_subset_graph M Y Lb subset ->
 source_ew_at M domain phi Lb goal ->context_bounded M gb gc gn bound ->
 coding_lt M w bound ->coding_lt M X bound ->coding_lt M Y bound ->coding_lt M Lb bound ->
 coding_lt M params(succM M bound) ->
 source_full_prv M gb gc gn witness ->source_full_prv M gb gc gn lk ->source_full_prv M gb gc gn lw ->
 source_full_prv M gb gc gn subset ->
 (forall i member,coding_lt M i params ->sf_relation M SFMember i X member ->source_full_prv M gb gc gn member) ->
 source_full_prv M gb gc gn goal.
Proof.
 intros HD HL HLg HV HE HP HW HLevelK HLevelW HSubset HEGoal HC BW BX BY BLb BParams PW PLK PLW PS PM.
 destruct(source_piece_conjunction_total M domain level sb sc count w X)as(all&HAll).
 pose proof(source_full_reflection_KF_witness_pc M domain level sb sc count K k w witness X lk all gb gc gn
  HD HL HV HW HLevelK HAll PW PLK)as PAll.
 destruct(source_ew_at_total M domain phi Y)as(ew&HEw).
 pose proof(source_full_pcf_initial_parameter_witness M domain level sb sc count w X all entry params phi Y lw ew gb gc gn bound
  HD HL HLg HV BW BX HC HE HP HAll HLevelW HEw PAll PLW PM)as PEw.
 apply(source_full_ew_monotone M gb gc gn bound domain phi Y Lb subset ew goal HC
  (sr_domain_bound_succ M domain bound HD));try assumption.
 apply(SourceBoundMonotone.source_bounded_monotone M phi(succM M params)(succM M bound)(HV entry params phi HE HP)).
 exact(proj2(coding_lt_succ_cancel M params(succM M bound))BParams).
Qed.
Print Assumptions source_full_reflection_chosen_witness.
Print Assumptions source_full_reflection_chosen_initial_witness.
