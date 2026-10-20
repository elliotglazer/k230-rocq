(** Exact exterior atomic-operation/numeral condition and its real
    numerical renaming action. The assignment width is always model-valued. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 FixedSourceBounds SourceParameterGraphs SourceFiniteNameParameters NumericalInstantiation NumericalRenamingMaps NumericalRenaming
 NumericalContextRenaming SourceDomainInstances SourceUnaryRenamingGraph SourceAtomicOperationSyntax SourceRepresentationPadding SourceQuantifierRules.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_atomic_condition_names M member numI numJ a x y r out:=exists ni nj op nums,
 numerical_instantiation M numI x ni/\numerical_instantiation M numJ y nj/\source_atomic_operation M member a x y r op/\
 sf_relation M SFAnd ni nj nums/\sf_relation M SFAnd op nums out.
Definition source_atomic_condition M member numI numJ out:=source_atomic_condition_names M member numI numJ
 (code_numeral M 2)(code_numeral M 3)(code_numeral M 4)(zeroM M)out.
Theorem source_atomic_condition_names_total M member numI numJ a x y r:exists out,
 source_atomic_condition_names M member numI numJ a x y r out.
Proof.
 destruct(numerical_instantiation_total M numI x)as(ni&HI).
 destruct(numerical_instantiation_total M numJ y)as(nj&HJ).
 destruct(source_atomic_operation_total M member a x y r)as(op&HOp).
 destruct(sf_relation_total M SFAnd ni nj)as(nums&HNums).
 destruct(sf_relation_total M SFAnd op nums)as(out&HO).
 exists out,ni,nj,op,nums. repeat split;assumption.
Qed.
Theorem source_atomic_condition_names_functional M member numI numJ a x y r out other:
 source_atomic_condition_names M member numI numJ a x y r out->source_atomic_condition_names M member numI numJ a x y r other->out=other.
Proof.
 intros(i&j&o&n&HI&HJ&HO&HN&HF)(i'&j'&o'&n'&HI'&HJ'&HO'&HN'&HF').
 assert(i=i')by(eapply numerical_instantiation_functional;eassumption). subst i'.
 assert(j=j')by(eapply numerical_instantiation_functional;eassumption). subst j'.
 assert(o=o')by(eapply code_relation_functional;eassumption). subst o'.
 assert(n=n')by(eapply sf_relation_functional;eassumption). subst n'. eapply sf_relation_functional;eassumption.
Qed.
Theorem source_atomic_condition_names_renaming M member numI numJ a x y r out a' x' y' r' other rb rc rn delta:
 source_bounded M numI(code_numeral M 1)->source_bounded M numJ(code_numeral M 1)->
 source_atomic_condition_names M member numI numJ a x y r out->source_atomic_condition_names M member numI numJ a' x' y' r' other->
 renaming_lookup M rb rc rn delta a a'->renaming_lookup M rb rc rn delta x x'->renaming_lookup M rb rc rn delta y y'->renaming_lookup M rb rc rn delta r r'->
 numerical_renaming M out rb rc rn delta other.
Proof.
 intros BI BJ(ni&nj&op&nums&HI&HJ&HOp&HNums&HOut)(ni'&nj'&op'&nums'&HI'&HJ'&HOp'&HNums'&HOther)HA HX HY HR.
 pose proof(source_unary_instance_renaming_graph M numI x ni rb rc rn delta x' ni' BI HI HX HI')as RI.
 pose proof(source_unary_instance_renaming_graph M numJ y nj rb rc rn delta y' nj' BJ HJ HY HJ')as RJ.
 pose proof(source_atomic_operation_renaming M member a x y r op a' x' y' r' op' rb rc rn delta HOp HOp' HA HX HY HR)as ROp.
 assert(RNums:numerical_renaming M nums rb rc rn delta nums').
 { apply(proj2(numerical_renaming_binary M SFAnd ni nj nums rb rc rn delta nums'(or_introl eq_refl)HNums)). exists ni',nj'. repeat split;assumption. }
 apply(proj2(numerical_renaming_binary M SFAnd op nums out rb rc rn delta other(or_introl eq_refl)HOut)).
 exists op',nums'. repeat split;assumption.
Qed.
Theorem source_atomic_condition_bound M member numI numJ out:
 source_bounded M numI(code_numeral M 1)->source_bounded M numJ(code_numeral M 1)->
 source_atomic_condition M member numI numJ out->source_bounded M out(code_numeral M 5).
Proof.
 intros BI BJ(ni&nj&op&nums&HI&HJ&HOp&HNums&HOut).
 pose proof(source_domain_instance_bound M numI(code_numeral M 3)ni(code_numeral M 5)BI
  (proj2(fixed_source_numeral_lt_iff M 3 5)ltac:(lia))HI)as BNI.
 pose proof(source_domain_instance_bound M numJ(code_numeral M 4)nj(code_numeral M 5)BJ
  (proj2(fixed_source_numeral_lt_iff M 4 5)ltac:(lia))HJ)as BNJ.
 assert(BOp:source_bounded M op(code_numeral M 5)).
 { apply(source_parameter_graph_bounded M 4(source_atomic_operation_predicate member)(source_atomic_operation_finite_bound member)
   (source_finite_parameter_names 4)(source_atomic_operation_environment(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)(zeroM M))(code_numeral M 5));[|exact HOp].
   intros[|[|[|[|i]]]]v HV HN;try lia.
   - change(v=code_numeral M 2)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 2 5));lia.
   - change(v=code_numeral M 3)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 3 5));lia.
   - change(v=code_numeral M 4)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 4 5));lia.
   - change(v=zeroM M)in HN. subst v. apply(proj2(fixed_source_numeral_lt_iff M 0 5));lia. }
 apply(proj2(source_bounded_accept_binary M SFAnd op nums out(code_numeral M 5)(or_introl eq_refl)HOut)). split;[exact BOp|].
 exact(proj2(source_bounded_accept_binary M SFAnd ni nj nums(code_numeral M 5)(or_introl eq_refl)HNums)(conj BNI BNJ)).
Qed.
Theorem source_atomic_condition_padding_shift M count member numI numJ condition:
 source_bounded M numI(code_numeral M 1)->source_bounded M numJ(code_numeral M 1)->source_atomic_condition M member numI numJ condition->
 exists padded shifted,
 source_atomic_condition_names M member numI numJ(succM M(succM M count))(succM M(succM M(succM M count)))(succM M(succM M(succM M(succM M count))))(zeroM M)padded/\
 source_atomic_condition_names M member numI numJ(succM M(succM M(succM M count)))(succM M(succM M(succM M(succM M count))))(succM M(succM M(succM M(succM M(succM M count)))))(code_numeral M 1)shifted/\
 source_representation_padding M count condition padded/\source_formula_shift M padded shifted.
Proof.
 intros BI BJ HC.
 destruct(source_atomic_condition_names_total M member numI numJ(succM M(succM M count))(succM M(succM M(succM M count)))(succM M(succM M(succM M(succM M count))))(zeroM M))as(padded&HP).
 destruct(source_atomic_condition_names_total M member numI numJ(succM M(succM M(succM M count)))(succM M(succM M(succM M(succM M count))))(succM M(succM M(succM M(succM M(succM M count)))))(code_numeral M 1))as(shifted&HS).
 exists padded,shifted. refine(conj HP(conj HS(conj _ _))).
 - apply(source_atomic_condition_names_renaming M member numI numJ(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)(zeroM M)condition
    (succM M(succM M count))(succM M(succM M(succM M count)))(succM M(succM M(succM M(succM M count))))(zeroM M)padded
    (code_numeral M 6)(code_numeral M 2)(code_numeral M 2)count BI BJ HC HP).
   + pose proof(representation_padding_outside_lookup M count(code_numeral M 2)ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 2 2))in H;lia))as H.
     change(representation_padding_lookup M count(code_numeral M 2)(addM M(succM M(succM M(zeroM M)))count))in H. rewrite!Arithmetic.add_succ,Arithmetic.add_zero in H. exact H.
   + pose proof(representation_padding_outside_lookup M count(code_numeral M 3)ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H;lia))as H.
     change(representation_padding_lookup M count(code_numeral M 3)(addM M(succM M(succM M(succM M(zeroM M))))count))in H. rewrite!Arithmetic.add_succ,Arithmetic.add_zero in H. exact H.
   + pose proof(representation_padding_outside_lookup M count(code_numeral M 4)ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 2))in H;lia))as H.
     change(representation_padding_lookup M count(code_numeral M 4)(addM M(succM M(succM M(succM M(succM M(zeroM M)))))count))in H. rewrite!Arithmetic.add_succ,Arithmetic.add_zero in H. exact H.
   + apply representation_padding_zero_lookup.
 - apply(source_atomic_condition_names_renaming M member numI numJ _ _ _ _ padded _ _ _ _ shifted
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BI BJ HP HS);apply context_shift_lookup;reflexivity.
Qed.
Print Assumptions source_atomic_condition_names_renaming.
Print Assumptions source_atomic_condition_bound.
Print Assumptions source_atomic_condition_padding_shift.
