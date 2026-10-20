(** Actual ordinary source shifts of the PH geometry leaves. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalRenaming RenamingSubstitution
 SourceQuantifierRules SourceReflectionGeometryPredicates SourceReflectionGeometryTransport SourceRecursionPrimitiveRelations
 SourceRecursionShiftGraphs.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_PH_subsets_shift M K beta old new:
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)old ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2(succM M K)(succM M beta))new ->
 source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero.
 apply(source_reflection_geometry_substitution M ReflectionSubsets(source_rec_env2 K beta)
  (source_rec_env2(succM M K)(succM M beta))old new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN).
 intros[|[|i]]HI;cbn in HI;try lia;apply source_rec_shift_lookup.
Qed.
Print Assumptions source_PH_subsets_shift.
