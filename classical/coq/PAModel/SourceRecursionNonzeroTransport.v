(** Exact SNz parameter transport used through existential witness scopes. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded SourceParameterTransport
 SourceFiniteNameParameters SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionShiftGraphs
 SourceQuantifierRules NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_nonzero_substitution M o N old o' N' new rb rc rn base:
 source_rec_nonzero M o N old ->source_rec_nonzero M o' N' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base N N' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HOO HNN. apply(source_parameter_transport M 2 source_rec_nonzero_predicate source_rec_nonzero_finite_bound
  (source_finite_parameter_names 2)(source_finite_parameter_names 2)(source_rec_env2 o N)(source_rec_env2 o' N')rb rc rn base old new);[|exact HO|exact HN].
 intros[|[|i]]x y HI HX HY;try lia.
 - change(x=o)in HX. change(y=o')in HY. now subst x y.
 - change(x=N)in HX. change(y=N')in HY. now subst x y.
Qed.
Theorem source_rec_nonzero_shift M o N old new:
 source_rec_nonzero M o N old ->source_rec_nonzero M(succM M o)(succM M N)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_nonzero_substitution M o N old(succM M o)(succM M N)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M N)).
Qed.
Print Assumptions source_rec_nonzero_substitution.
Print Assumptions source_rec_nonzero_shift.
