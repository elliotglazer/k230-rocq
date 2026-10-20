From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded SourceParameterGraphs SourceParameterTransport SourceFiniteNameParameters
 SourceRecursionPrimitiveRelations SourceRecursionSetOperations SourceRecursionShiftGraphs SourceQuantifierRules
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_rec_adjoin_bounded M f q g out k:coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->source_rec_adjoin M f q g out ->source_bounded M out k.
Proof.
 intros BF BQ BG HO. apply(source_parameter_graph_bounded M 3 source_rec_adjoin_predicate source_rec_adjoin_finite_bound
  (source_finite_parameter_names 3)(source_rec_env3 f q g)k);[|exact HO].
 intros[|[|[|i]]]x HI HX;try lia.
 - change(x=f)in HX. now subst x.
 - change(x=q)in HX. now subst x.
 - change(x=g)in HX. now subst x.
Qed.
Theorem source_rec_adjoin_substitution M f q g old f' q' g' new rb rc rn base:
 source_rec_adjoin M f q g old ->source_rec_adjoin M f' q' g' new ->
 substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base q q' ->substitution_lookup M rb rc rn base g g' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HF HQ HG. apply(source_parameter_transport M 3 source_rec_adjoin_predicate source_rec_adjoin_finite_bound
  (source_finite_parameter_names 3)(source_finite_parameter_names 3)(source_rec_env3 f q g)(source_rec_env3 f' q' g')rb rc rn base old new);[|exact HO|exact HN].
 intros[|[|[|i]]]x y HI HX HY;try lia.
 - change(x=f)in HX. change(y=f')in HY. now subst x y.
 - change(x=q)in HX. change(y=q')in HY. now subst x y.
 - change(x=g)in HX. change(y=g')in HY. now subst x y.
Qed.
Theorem source_rec_adjoin_shift M f q g old new:
 source_rec_adjoin M f q g old ->source_rec_adjoin M(succM M f)(succM M q)(succM M g)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_adjoin_substitution M f q g old(succM M f)(succM M q)(succM M g)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M f)(source_rec_shift_lookup M q)(source_rec_shift_lookup M g)).
Qed.
Print Assumptions source_rec_adjoin_bounded.
Print Assumptions source_rec_adjoin_substitution.
Print Assumptions source_rec_adjoin_shift.
