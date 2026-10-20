(** Free-name bounds and absence for the two actual variable-only prefixes
    used by local definability. These lemmas retain arbitrary internal
    matrices and parameter counts; nested binders are never excluded. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded SourceNumeralLift
 NumericalEnvironments NumericalRenaming NumericalRenamingMaps NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionBounds
 SourceBallSMembershipBlock SourceRoleReopening SourcePrefixSubstitutionVacuity SourceNamedVacuity
 SourceBoundMonotone NumericalContexts SourceNamedElimination SourceDefinabilityBounds SourceNamedVacuityImages RenamingSubstitution.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_local_parameter_prefix_values M count pb pc head hb hc i j:
 balls_offset_assignment M(code_numeral M 1)count pb pc ->
 environment_cons M pb pc count head hb hc(succM M count) ->coding_lt M i(succM M count) ->
 substitution_lookup M hb hc(succM M count)(zeroM M)i j ->j=head \/coding_lt M j(succM M count).
Proof.
 intros HOffset HCons HI HJ.
 pose proof(proj2(environment_lookup_inside M hb hc(succM M count)i j HI)
  (proj1(substitution_lookup_inside M hb hc(succM M count)(zeroM M)i j HI)HJ))as HEnv.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
 as[->|[idx ->]].
 - left. exact(proj1(environment_cons_head M pb pc count head hb hc(succM M count)j HCons)HEnv).
 - pose proof(proj1(coding_lt_succ_cancel M idx count)HI)as HIdx.
   pose proof(proj1(environment_cons_tail M pb pc count head hb hc(succM M count)idx j HCons)HEnv)as HTail.
   pose proof(proj1(environment_lookup_inside M pb pc count idx j HIdx)HTail)as HBeta.
   pose proof(proj1(HOffset idx j HIdx)HBeta)as E.
   change(j=addM M idx(succM M(zeroM M)))in E.
   rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in E. subst j.
   right;exact(proj2(coding_lt_succ_cancel M idx count)HIdx).
Qed.
Theorem source_local_assigned_environment_bound M count environment pb pc head hb hc assigned k:
 source_envf M count environment ->balls_offset_assignment M(code_numeral M 1)count pb pc ->
 environment_cons M pb pc count head hb hc(succM M count) ->
 numerical_substitution M environment hb hc(succM M count)(zeroM M)assigned ->
 coding_lt M head k ->coding_lt M(succM M count)(succM M k) ->source_bounded M assigned k.
Proof.
 intros HE HO HC HS HH HK.
 apply(numerical_substitution_preserves_bound M environment hb hc(succM M count)(zeroM M)assigned(succM M count)k
  (source_envf_bound M count environment HE)HS).
 intros i j HI HJ. destruct(source_local_parameter_prefix_values M count pb pc head hb hc i j HO HC HI HJ)as[->|HJ0].
 - exact HH.
 - exact(source_bound_lt_le M j(succM M count)k HJ0 HK).
Qed.
Theorem source_local_assigned_environment_vacuous M count environment pb pc head hb hc assigned k x:
 source_envf M count environment ->balls_offset_assignment M(code_numeral M 1)count pb pc ->
 environment_cons M pb pc count head hb hc(succM M count) ->
 numerical_substitution M environment hb hc(succM M count)(zeroM M)assigned ->source_bounded M assigned k ->
 head<>x ->coding_lt M(succM M count)(succM M x) ->source_named_vacuous M x assigned.
Proof.
 intros HE HO HC HS BG HH HX.
 apply(source_named_vacuous_prefix_substitution M environment hb hc(succM M count)assigned k x
  (source_envf_bound M count environment HE)HS BG).
 intros i j HI HJ. destruct(source_local_parameter_prefix_values M count pb pc head hb hc i j HO HC HI HJ)as[->|HJ0].
 - exact HH.
 - exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)j x
    (source_bound_lt_le M j(succM M count)x HJ0 HX)).
Qed.
Theorem source_local_reopening_values M carrier representative b c i j:
 source_role_reopening M carrier representative b c ->coding_lt M i(code_numeral M 2) ->
 substitution_lookup M b c(code_numeral M 2)(code_numeral M 2)i j ->j=representative \/j=carrier.
Proof.
 intros[HRep HCarrier]HI HJ.
 destruct(source_numeral_initial_segment M 2 i HI)as[index[HIndex ->]].
 destruct index as[|[|index]];try lia.
 - left. exact(substitution_lookup_functional M b c(code_numeral M 2)(code_numeral M 2)(zeroM M)j representative HJ
    (proj2(substitution_lookup_inside M b c(code_numeral M 2)(code_numeral M 2)(zeroM M)representative(coding_zero_lt_succ M(code_numeral M 1)))
     (proj1(substitution_lookup_inside M b c(code_numeral M 2)(zeroM M)(zeroM M)representative(coding_zero_lt_succ M(code_numeral M 1)))HRep))).
 - right. exact(substitution_lookup_functional M b c(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)j carrier HJ
    (proj2(substitution_lookup_inside M b c(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)carrier(coding_lt_succ M(code_numeral M 1)))
     (proj1(substitution_lookup_inside M b c(code_numeral M 2)(zeroM M)(code_numeral M 1)carrier(coding_lt_succ M(code_numeral M 1)))HCarrier))).
Qed.
Theorem source_local_assigned_representation_bound M rep carrier representative b c assigned k:
 source_bounded M rep(code_numeral M 2) ->source_role_reopening M carrier representative b c ->
 numerical_substitution M rep b c(code_numeral M 2)(code_numeral M 2)assigned ->
 coding_lt M carrier k ->coding_lt M representative k ->source_bounded M assigned k.
Proof.
 intros BR HO HS HC HR.
 apply(numerical_substitution_preserves_bound M rep b c(code_numeral M 2)(code_numeral M 2)assigned(code_numeral M 2)k BR HS).
 intros i j HI HJ. destruct(source_local_reopening_values M carrier representative b c i j HO HI HJ)as[E|E];subst j;assumption.
Qed.
Theorem source_local_assigned_representation_vacuous M rep carrier representative b c assigned x:
 source_bounded M rep(code_numeral M 2) ->source_role_reopening M carrier representative b c ->
 numerical_substitution M rep b c(code_numeral M 2)(code_numeral M 2)assigned ->
 carrier<>x ->representative<>x ->source_named_vacuous M x assigned.
Proof.
 intros BR HO HS HC HR.
 assert(HR':numerical_renaming M rep b c(code_numeral M 2)(zeroM M)assigned).
 { apply(proj2(numerical_renaming_substitution M rep b c(code_numeral M 2)(zeroM M)assigned)).
   now rewrite coding_add_zero_r. }
 apply(source_named_vacuous_renaming_image M rep assigned(code_numeral M 2)b c(code_numeral M 2)(zeroM M)x BR HR').
 intros i j HI HJ.
 assert(HSJ:substitution_lookup M b c(code_numeral M 2)(code_numeral M 2)i j).
 { apply(proj1(renaming_substitution_lookup M b c(code_numeral M 2)(zeroM M)i j))in HJ.
   now rewrite coding_add_zero_r in HJ. }
 destruct(source_local_reopening_values M carrier representative b c i j HO HI HSJ)as[E|E];subst j;assumption.
Qed.
Print Assumptions source_local_parameter_prefix_values.
Print Assumptions source_local_assigned_environment_bound.
Print Assumptions source_local_assigned_environment_vacuous.
Print Assumptions source_local_reopening_values.
Print Assumptions source_local_assigned_representation_bound.
Print Assumptions source_local_assigned_representation_vacuous.
