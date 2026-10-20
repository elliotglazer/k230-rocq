(** The shifted matrix of a representation, assigned through its Dn table,
    is exactly the same original matrix under the lifted parameter table.
    Moving set relativization follows the actual carrier lookup. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SourceBounded NumericalEnvironments NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 RenamingSubstitution SourceSubstitutionComposition SourceDnAssignments SourceSetRelativization
 SourceSetRelativizationSubstitution SourceParameterValueShift.
Unset Implicit Arguments.
Theorem source_representation_assigned_matrix M count phi matrix d X pb pc ab ac lb lc ln ub uc result:
 source_bounded M phi count ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 source_parameter_value_shift M count pb pc ub uc ->
 numerical_substitution M matrix lb lc ln(code_numeral M 1)result ->
 numerical_substitution M phi ub uc count(zeroM M)result.
Proof.
 intros BF HM HA HL HU HResult.
 apply(numerical_substitution_composition M phi count
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)
  lb lc ln(code_numeral M 1)ub uc count(zeroM M)matrix result BF
  (proj1(numerical_renaming_empty_substitution M phi(zeroM M)(zeroM M)(code_numeral M 3)matrix)HM)HResult).
 intros i j value HI HJ HV.
 assert(EJ:j=succM M(succM M(succM M i))).
 { eapply substitution_lookup_functional;[exact HJ|].
   apply substitution_lookup_outside;[apply coding_not_lt_zero|].
   exists i. split;[symmetry;apply Arithmetic.add_zero|].
   cbn[code_numeral]. now rewrite !Arithmetic.add_succ,Arithmetic.add_zero. }
 subst j. destruct(beta_total M pb pc i)as(v&Hv).
 assert(EV:value=succM M v).
 { eapply substitution_lookup_functional;[exact HV|].
   apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
   exact(proj2(source_dn_assignment_parameter M _ _ _ _ _ _ _ _ _ HA HI)Hv). }
 subst value. apply(proj2(substitution_lookup_inside M ub uc count(zeroM M)i(succM M v)HI)).
 exact(HU i v HI Hv).
Qed.
Theorem source_representation_assigned_relative M count phi matrix relative d X pb pc ab ac lb lc ln ub uc
 assignedMatrix assignedRelative:
 source_bounded M phi count ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 source_parameter_value_shift M count pb pc ub uc ->
 numerical_substitution M phi ub uc count(zeroM M)assignedMatrix ->
 numerical_substitution M relative lb lc ln(code_numeral M 1)assignedRelative ->
 source_set_relativization M(succM M X)assignedMatrix assignedRelative.
Proof.
 intros BF HM HR HA HL HU HMatrix HRelative.
 destruct(numerical_substitution_total M matrix lb lc ln(code_numeral M 1))as(candidate&HCandidate).
 pose proof(source_representation_assigned_matrix M count phi matrix d X pb pc ab ac lb lc ln ub uc candidate
  BF HM HA HL HU HCandidate)as HOriginal.
 assert(E:candidate=assignedMatrix)by(eapply numerical_substitution_functional;eassumption). subst candidate.
 apply(source_set_relativization_substitution M(code_numeral M 2)(succM M X)matrix relative
  lb lc ln(code_numeral M 1)assignedMatrix assignedRelative);try assumption.
 apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
 exact(source_dn_assignment_one M _ _ _ _ _ _ _ HA).
Qed.
Print Assumptions source_representation_assigned_matrix.
Print Assumptions source_representation_assigned_relative.
