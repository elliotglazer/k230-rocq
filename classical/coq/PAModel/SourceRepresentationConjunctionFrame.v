(** A fixed hygienic frame for conjunction representatives. The three
    auxiliary sets are names3,4,5; the result is name0 and the carrier1.
    Dn moves exactly the auxiliary names above its assignment slots. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions CodeExpressionPlug
 SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceParameterGraphs
 SourceFiniteParameters SourceFiniteParameterProofs SourceRepresentationPadding
 SourceRepresentationDifferencePoints SourceRepresentationDifferencePadding SourceDifferenceProfile FixedSourceBounds.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition conjunction_outer_environment M i :=match i with
 |0=>code_numeral M 3|1=>code_numeral M 4|2=>code_numeral M 5|_=>zeroM M end.
Definition conjunction_point_environment M count left right guard i :=match i with
 |0=>addM M(code_numeral M 3) count|1=>addM M(code_numeral M 4) count
 |2=>addM M(code_numeral M 5) count|3=>zeroM M|4=>left|5=>right|_=>guard end.
Theorem conjunction_outer_names_bound M i :(i<4)%nat ->coding_lt M(conjunction_outer_environment M i)(code_numeral M 6).
Proof.
 intro HI. destruct i as[|[|[|[|i]]]];try lia;cbn[conjunction_outer_environment].
 - apply(proj2(fixed_source_numeral_lt_iff M 3 6)). lia.
 - apply(proj2(fixed_source_numeral_lt_iff M 4 6)). lia.
 - apply(proj2(fixed_source_numeral_lt_iff M 5 6)). lia.
 - apply coding_zero_lt_succ.
Qed.
Theorem conjunction_point_names_bound M count left right guard i :(i<4)%nat ->
 coding_lt M(conjunction_point_environment M count left right guard i)(addM M count(code_numeral M 6)).
Proof.
 intro HI. destruct i as[|[|[|[|i]]]];try lia;cbn[conjunction_point_environment].
 - rewrite(Arithmetic.add_comm M(code_numeral M 3)count). exact(coding_lt_add_left M count(code_numeral M 3)(code_numeral M 6)(proj2(fixed_source_numeral_lt_iff M 3 6)ltac:(lia))).
 - rewrite(Arithmetic.add_comm M(code_numeral M 4)count). exact(coding_lt_add_left M count(code_numeral M 4)(code_numeral M 6)(proj2(fixed_source_numeral_lt_iff M 4 6)ltac:(lia))).
 - rewrite(Arithmetic.add_comm M(code_numeral M 5)count). exact(coding_lt_add_left M count(code_numeral M 5)(code_numeral M 6)(proj2(fixed_source_numeral_lt_iff M 5 6)ltac:(lia))).
 - rewrite Arithmetic.add_comm. change(coding_lt M(zeroM M)(addM M(succM M(code_numeral M 5)) count)).
   rewrite Arithmetic.add_succ. apply coding_zero_lt_succ.
Qed.
Theorem conjunction_point_names_padding M count left right guard i :(i<4)%nat ->
 representation_padding_lookup M count(conjunction_outer_environment M i)
   (conjunction_point_environment M count left right guard i).
Proof.
 intro HI. destruct i as[|[|[|[|i]]]];try lia;cbn[conjunction_outer_environment conjunction_point_environment].
 - apply representation_padding_outside_lookup. intro H. apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H. lia.
 - apply representation_padding_outside_lookup. intro H. apply(proj1(fixed_source_numeral_lt_iff M 4 2))in H. lia.
 - apply representation_padding_outside_lookup. intro H. apply(proj1(fixed_source_numeral_lt_iff M 5 2))in H. lia.
 - apply representation_padding_zero_lookup.
Qed.
Lemma difference_operation_parameters_bound M x y r k operation :coding_lt M x k ->coding_lt M y k ->coding_lt M r k ->
 code_relation M(difference_values M x y r)source_difference_operation_expression operation ->source_bounded M operation k.
Proof.
 intros HX HY HR HO. apply(source_parameter_graph_bounded M 3 _ source_difference_operation_bounded
   source_three_parameter_names(difference_values M x y r) k);[|exact HO].
 intros[|[|[|i]]] v HI HV;try lia;cbn[source_three_parameter_names code_relation difference_values]in HV;subst v;assumption.
Qed.
Lemma difference_first_operation_parameters M rho operation :code_relation M rho E_double_difference_first_operation operation ->
 code_relation M(difference_values M(rho 0)(rho 1)(rho 2))source_difference_operation_expression operation.
Proof.
 intro HO. apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 1)(rho 2))
  (difference_names(CEvar 0)(CEvar 1)(CEvar 2))source_difference_operation_expression operation
  ltac:(intros[|[|[|i]]];reflexivity))). exact HO.
Qed.
Lemma difference_second_operation_parameters M rho operation :code_relation M rho E_double_difference_second_operation operation ->
 code_relation M(difference_values M(rho 0)(rho 2)(rho 3))source_difference_operation_expression operation.
Proof.
 intro HO. apply(proj1(code_relation_plug M rho(difference_values M(rho 0)(rho 2)(rho 3))
  (difference_names(CEvar 0)(CEvar 2)(CEvar 3))source_difference_operation_expression operation
  ltac:(intros[|[|[|i]]];reflexivity))). exact HO.
Qed.
Theorem conjunction_difference_conditions_total M count left right guard :
 exists first second condition first' second' padded,
 code_relation M(conjunction_outer_environment M) E_double_difference_first_operation first /\
 code_relation M(conjunction_outer_environment M) E_double_difference_second_operation second /\
 sf_relation M SFAnd first second condition /\
 code_relation M(conjunction_point_environment M count left right guard) E_double_difference_first_operation first' /\
 code_relation M(conjunction_point_environment M count left right guard) E_double_difference_second_operation second' /\
 sf_relation M SFAnd first' second' padded /\source_representation_padding M count condition padded /\
 source_bounded M condition(code_numeral M 6) /\source_bounded M padded(addM M count(code_numeral M 6)).
Proof.
 set(outer:=conjunction_outer_environment M). set(inner:=conjunction_point_environment M count left right guard).
 destruct(code_relation_total M E_double_difference_first_operation outer)as(first&HF).
 destruct(code_relation_total M E_double_difference_second_operation outer)as(second&HS).
 destruct(sf_relation_total M SFAnd first second)as(condition&HC).
 destruct(code_relation_total M E_double_difference_first_operation inner)as(first'&HF').
 destruct(code_relation_total M E_double_difference_second_operation inner)as(second'&HS').
 destruct(sf_relation_total M SFAnd first' second')as(padded&HP).
 pose proof(difference_first_operation_parameters M outer first HF)as F.
 pose proof(difference_second_operation_parameters M outer second HS)as S.
 pose proof(difference_first_operation_parameters M inner first' HF')as F'.
 pose proof(difference_second_operation_parameters M inner second' HS')as S'.
 assert(PF:source_representation_padding M count first first').
 { exact(source_representation_difference_padding M count(outer 0)(outer 1)(outer 2)(inner 0)(inner 1)(inner 2) first first'
    (conjunction_point_names_padding M count left right guard 0 ltac:(lia))
    (conjunction_point_names_padding M count left right guard 1 ltac:(lia))
    (conjunction_point_names_padding M count left right guard 2 ltac:(lia)) F F'). }
 assert(PS:source_representation_padding M count second second').
 { exact(source_representation_difference_padding M count(outer 0)(outer 2)(outer 3)(inner 0)(inner 2)(inner 3) second second'
    (conjunction_point_names_padding M count left right guard 0 ltac:(lia))
    (conjunction_point_names_padding M count left right guard 2 ltac:(lia))
    (conjunction_point_names_padding M count left right guard 3 ltac:(lia)) S S'). }
 exists first,second,condition,first',second',padded.
 refine(conj HF(conj HS(conj HC(conj HF'(conj HS'(conj HP(conj
  (source_representation_difference_condition_padding M count first second first' second' condition padded PF PS HC HP)(conj _ _)))))))).
 - apply(proj2(source_bounded_accept_binary M SFAnd first second condition(code_numeral M 6)(or_introl eq_refl) HC)). split.
   + apply(difference_operation_parameters_bound M(outer 0)(outer 1)(outer 2)(code_numeral M 6) first);try exact F;apply conjunction_outer_names_bound;lia.
   + apply(difference_operation_parameters_bound M(outer 0)(outer 2)(outer 3)(code_numeral M 6) second);try exact S;apply conjunction_outer_names_bound;lia.
 - apply(proj2(source_bounded_accept_binary M SFAnd first' second' padded(addM M count(code_numeral M 6))(or_introl eq_refl) HP)). split.
   + apply(difference_operation_parameters_bound M(inner 0)(inner 1)(inner 2)(addM M count(code_numeral M 6)) first');try exact F';apply conjunction_point_names_bound;lia.
   + apply(difference_operation_parameters_bound M(inner 0)(inner 2)(inner 3)(addM M count(code_numeral M 6)) second');try exact S';apply conjunction_point_names_bound;lia.
Qed.
Print Assumptions conjunction_point_names_bound.
Print Assumptions conjunction_point_names_padding.
Print Assumptions conjunction_difference_conditions_total.

