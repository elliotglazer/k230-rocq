(** An assigned representation matrix uses exactly the whole-shift of
    the requested relative formula, independent of its environment witness. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SourceBounded NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 SourceQuantifierRules SourceDnAssignments SourceParameterValueShift SourceRepresentationAssignedMatrix
 SourceSetRelativization SourceSetRelativizationRenaming SourceSetRelativizationFunctionality.
Unset Implicit Arguments.
Theorem source_representation_assigned_relative_shift M count phi matrix relative d X pb pc ab ac lb lc ln
 assignedPhi assignedRelative shiftedRelative:
 source_bounded M phi count ->
 numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix ->
 source_set_relativization M(code_numeral M 2)matrix relative ->
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 numerical_substitution M phi pb pc count(zeroM M)assignedPhi ->
 source_set_relativization M X assignedPhi assignedRelative ->
 source_formula_shift M assignedRelative shiftedRelative ->
 numerical_substitution M relative lb lc ln(code_numeral M 1)shiftedRelative.
Proof.
 intros BF HM HR HA HL HAssigned HRelative HShift.
 destruct(numerical_renaming_total M assignedPhi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shiftedPhi&HPhiShift).
 destruct(source_parameter_value_shift_total M count pb pc)as(qb&qc&HQ).
 pose proof(source_parameter_value_shift_substitution M count phi assignedPhi shiftedPhi pb pc qb qc
  BF HAssigned HPhiShift HQ)as HShiftedMatrix.
 destruct(numerical_substitution_total M relative lb lc ln(code_numeral M 1))as(candidate&HCandidate).
 pose proof(source_representation_assigned_relative M count phi matrix relative d X pb pc ab ac lb lc ln qb qc
  shiftedPhi candidate BF HM HR HA HL HQ HShiftedMatrix HCandidate)as HCandidateRel.
 assert(HShiftedRel:source_set_relativization M(succM M X)shiftedPhi shiftedRelative).
 { apply(source_set_relativization_renaming M X(succM M X)assignedPhi assignedRelative
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)shiftedPhi shiftedRelative);try assumption.
   right. split;[apply coding_not_lt_zero|]. apply Arithmetic.succ_as_add. }
 assert(E:candidate=shiftedRelative)by(eapply source_set_relativization_functional;eassumption).
 now subst candidate.
Qed.
Print Assumptions source_representation_assigned_relative_shift.
