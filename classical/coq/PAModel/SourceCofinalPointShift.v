(** Exact shift of an open cofinal common-level point. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift SourceCommonLevelWitness SourceCofinalCommonPoint.
Unset Implicit Arguments.
Theorem source_cofinal_common_point_shift M start count K d y f g:
 source_cofinal_common_point M start count K d y f ->
 source_cofinal_common_point M(succM M start)count(succM M K)(succM M d)(succM M y)g ->source_formula_shift M f g.
Proof.
 intros HF HG. apply(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)(code_numeral M 1)g)).
 apply(source_cofinal_common_point_substitution M start count K d y f(succM M start)(succM M K)(succM M d)(succM M y)g
 (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HF HG).
 - apply source_cutoff_shift_base_lookup.
 - apply source_cutoff_shift_base_lookup.
 - apply source_cutoff_shift_base_lookup.
 - intros i HI. rewrite source_common_add_successor. apply source_cutoff_shift_base_lookup.
Qed.
Print Assumptions source_cofinal_common_point_shift.
