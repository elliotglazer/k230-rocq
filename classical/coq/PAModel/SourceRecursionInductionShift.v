(** Genuine ordinary shift of the fixed SInd hypothesis. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceQuantifierRules NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenaming RenamingSubstitution SourceRecursionPrimitiveRelations SourceRecursionInductionGraphs SourceRecursionShiftGraphs
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterTransport.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_induction_substitution M o N old o' N' new rb rc rn base:
 source_rec_induction M o N old ->source_rec_induction M o' N' new ->substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base N N' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HX HY. apply(source_parameter_transport M 2 source_rec_induction_predicate source_rec_induction_finite_bound
  (source_finite_parameter_names 2)(source_finite_parameter_names 2)(source_rec_env2 o N)(source_rec_env2 o' N')rb rc rn base old new);[|exact HO|exact HN].
 intros[|[|i]]x y HI H1 H2;try lia.
 - change(x=o)in H1. change(y=o')in H2. now subst x y.
 - change(x=N)in H1. change(y=N')in H2. now subst x y.
Qed.
Theorem source_rec_induction_shift M o N old new:
 source_rec_induction M o N old ->source_rec_induction M(succM M o)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_induction_substitution M o N old(succM M o)(succM M N)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_induction_substitution.
Print Assumptions source_rec_induction_shift.
