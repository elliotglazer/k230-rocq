(** Actual parameter substitution and shift of SInj and ordered pairs.
    Used when closing the internally coded recursion-extension point. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded SourceParameterGraphs
 SourceParameterTransport SourceFiniteNameParameters SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs
 SourceRecursionSetOperations SourceRecursionShiftGraphs SourceQuantifierRules
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_rec_injectivity_bounded M N out k :
 coding_lt M N k ->source_rec_injectivity M N out ->source_bounded M out k.
Proof.
 intros BN HO. apply(source_parameter_graph_bounded M 1 source_rec_injectivity_predicate
  source_rec_injectivity_finite_bound(source_finite_parameter_names 1)(fun _=>N)k);[|exact HO].
 intros[|i]x HI HX;[|lia]. change(x=N)in HX. now subst x.
Qed.
Theorem source_rec_injectivity_substitution M N old N' new rb rc rn base :
 source_rec_injectivity M N old ->source_rec_injectivity M N' new ->
 substitution_lookup M rb rc rn base N N' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HLookup.
 apply(source_parameter_transport M 1 source_rec_injectivity_predicate source_rec_injectivity_finite_bound
  (source_finite_parameter_names 1)(source_finite_parameter_names 1)(fun _=>N)(fun _=>N')rb rc rn base old new);
  [|exact HO|exact HN].
 intros[|i]x y HI HX HY;[|lia]. change(x=N)in HX. change(y=N')in HY. now subst x y.
Qed.
Theorem source_rec_injectivity_shift M N old new :
 source_rec_injectivity M N old ->source_rec_injectivity M(succM M N)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_injectivity_substitution M N old(succM M N)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M N)).
Qed.

Theorem source_rec_ordered_pair_bounded M x y q out k :
 coding_lt M x k ->coding_lt M y k ->coding_lt M q k ->source_rec_ordered_pair M x y q out ->source_bounded M out k.
Proof.
 intros BX BY BQ HO. apply(source_parameter_graph_bounded M 3 source_rec_ordered_pair_predicate
  source_rec_ordered_pair_finite_bound(source_finite_parameter_names 3)(source_rec_env3 x y q)k);[|exact HO].
 intros[|[|[|i]]]a HI HA;try lia.
 - change(a=x)in HA. now subst a.
 - change(a=y)in HA. now subst a.
 - change(a=q)in HA. now subst a.
Qed.
Theorem source_rec_ordered_pair_substitution M x y q old x' y' q' new rb rc rn base :
 source_rec_ordered_pair M x y q old ->source_rec_ordered_pair M x' y' q' new ->
 substitution_lookup M rb rc rn base x x' ->substitution_lookup M rb rc rn base y y' ->
 substitution_lookup M rb rc rn base q q' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HX HY HQ. apply(source_parameter_transport M 3 source_rec_ordered_pair_predicate
  source_rec_ordered_pair_finite_bound(source_finite_parameter_names 3)(source_finite_parameter_names 3)
  (source_rec_env3 x y q)(source_rec_env3 x' y' q')rb rc rn base old new);[|exact HO|exact HN].
 intros[|[|[|i]]]a b HI HA HB;try lia.
 - change(a=x)in HA. change(b=x')in HB. now subst a b.
 - change(a=y)in HA. change(b=y')in HB. now subst a b.
 - change(a=q)in HA. change(b=q')in HB. now subst a b.
Qed.
Theorem source_rec_ordered_pair_shift M x y q old new :
 source_rec_ordered_pair M x y q old ->source_rec_ordered_pair M(succM M x)(succM M y)(succM M q)new ->
 source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_ordered_pair_substitution M x y q old(succM M x)(succM M y)(succM M q)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M x)(source_rec_shift_lookup M y)(source_rec_shift_lookup M q)).
Qed.
Print Assumptions source_rec_injectivity_bounded.
Print Assumptions source_rec_injectivity_substitution.
Print Assumptions source_rec_injectivity_shift.
Print Assumptions source_rec_ordered_pair_bounded.
Print Assumptions source_rec_ordered_pair_substitution.
Print Assumptions source_rec_ordered_pair_shift.
