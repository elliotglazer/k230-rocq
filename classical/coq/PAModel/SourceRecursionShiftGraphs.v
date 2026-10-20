(** Exact ordinary shifts of the varying-matrix recursion predicates. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded
 NumericalSubstitutionMaps NumericalRenamingMaps NumericalRenaming NumericalContextRenaming RenamingSubstitution
 SourceRecursionAttempt SourceRecursionAttemptTransport SourceRecursionAgreement SourceRecursionPrimitiveRelations
 SourceRecursionAttemptStepShell SourceRecursionWitnessTransport SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport
 SourceQuantifierRules.
Unset Implicit Arguments.
Lemma source_rec_shift_lookup M x:
 substitution_lookup M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)x(succM M x).
Proof.
 pose proof(proj1(renaming_substitution_lookup M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)x(succM M x))
  (proj2(context_shift_lookup M x(succM M x))eq_refl))as H.
 rewrite Arithmetic.add_zero in H. exact H.
Qed.
Theorem source_rec_attempt_shift M phi o a N f old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_attempt M phi o a N f old ->
 source_rec_attempt M phi(succM M o)(succM M a)(succM M N)(succM M f)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_rec_attempt_substitution M phi o a N f old(succM M o)(succM M a)(succM M N)(succM M f)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN
  (source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)(source_rec_shift_lookup M f)).
Qed.
Theorem source_rec_agreement_shift M f g z old new:
 source_rec_agreement M f g z old ->source_rec_agreement M(succM M f)(succM M g)(succM M z)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_rec_agreement_substitution M f g z old(succM M f)(succM M g)(succM M z)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN
  (source_rec_shift_lookup M f)(source_rec_shift_lookup M g)(source_rec_shift_lookup M z)).
Qed.
Theorem source_rec_transition_witness_shift M phi f u v old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_transition_witness M phi f u v old ->
 source_rec_transition_witness M phi(succM M f)(succM M u)(succM M v)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_rec_transition_witness_substitution M phi f u v old(succM M f)(succM M u)(succM M v)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN
  (source_rec_shift_lookup M f)(source_rec_shift_lookup M u)(source_rec_shift_lookup M v)).
Qed.
Theorem source_rec_binary_shift M phi u v old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_binary M phi u v old ->
 source_rec_binary M phi(succM M u)(succM M v)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_rec_binary_substitution_graph M phi u v old(succM M u)(succM M v)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M u)(source_rec_shift_lookup M v)).
Qed.
Print Assumptions source_rec_attempt_shift.
Print Assumptions source_rec_agreement_shift.
Print Assumptions source_rec_transition_witness_shift.
Print Assumptions source_rec_binary_shift.
