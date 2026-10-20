(** Actual source shift transport of the sole free ordinal in ordinary Refl. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalRenaming RenamingSubstitution
 SourceBounded SourceQuantifierRules SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionTransport
 SourceRecursionShiftGraphs NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofRenaming.
Unset Implicit Arguments.
Theorem source_ordinary_reflection_shift_to M domain count phi d old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection M domain count phi d old ->source_ordinary_reflection M domain count phi(succM M d)new ->
 source_formula_shift M old new.
Proof.
 intros HD HP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 exact(source_ordinary_reflection_substitution M domain count phi d old(succM M d)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HP HO HN(source_rec_shift_lookup M d)).
Qed.
Theorem source_full_ordinary_reflection_shift M domain count phi d old new b c n u v:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
 source_ordinary_reflection M domain count phi d old ->source_ordinary_reflection M domain count phi(succM M d)new ->
 context_shift M b c n u v ->source_full_prv M b c n old ->source_full_prv M u v n new.
Proof.
 intros HD HP HO HN HC P.
 exact(source_full_prv_renaming M b c n old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)u v new P HC
  (source_ordinary_reflection_shift_to M domain count phi d old new HD HP HO HN)).
Qed.
Print Assumptions source_ordinary_reflection_shift_to.
Print Assumptions source_full_ordinary_reflection_shift.
