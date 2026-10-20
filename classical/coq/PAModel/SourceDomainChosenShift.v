(** Actual ordinary shift between two chosen instances of a unary source predicate. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded NumericalInstantiation
 SourceUnarySubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Theorem source_domain_instance_chosen_shift M domain x old new:
 source_bounded M domain(code_numeral M 1) ->numerical_instantiation M domain x old ->
 numerical_instantiation M domain(succM M x)new ->source_formula_shift M old new.
Proof.
 intros HD HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_domain_instance_substitution_graph M domain x old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)(succM M x)new HD HO(source_rec_shift_lookup M x)HN).
Qed.
Print Assumptions source_domain_instance_chosen_shift.
