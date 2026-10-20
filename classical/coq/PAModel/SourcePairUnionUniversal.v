(** Actual universal disjunction deduction in the canonical named frame. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceRepresentationDifferencePoints
 SourceRepresentationPointBounds SourcePairUnionProgram SourceUniversalMacro SourceFiniteTelescope
 SourcePropositionalTemplates NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_empty_pair_union_universal M rho k profile point1 point2 target law:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 code_relation M rho(E_double_difference_all pair_union_profile_template)profile ->
 code_relation M rho(E_double_difference_all pair_union_left_template)point1 ->
 code_relation M rho(E_double_difference_all pair_union_right_template)point2 ->
 code_relation M rho(E_double_difference_all pair_union_conclusion)target ->
 source_finite_telescope M[profile;point1;point2]target law ->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)law.
Proof.
 intros HNames B4 B5 B6 HProfile HP1 HP2 HT HTelescope.
 destruct(code_relation_total M(representation_member_expression(CEvar 0))rho)as(a&HA).
 destruct(code_relation_total M(representation_member_expression(CEvar 1))rho)as(b&HB).
 destruct(code_relation_total M(representation_member_expression(CEvar 2))rho)as(c&HC).
 destruct(code_relation_total M(representation_member_expression(CEvar 3))rho)as(d&HD).
 set(values:=double_difference_point_values a b c d(rho 4)(rho 5)(rho 6)).
 assert(HValues:forall i,code_relation M rho(double_difference_point_plug i)(values i)).
 { intros[|[|[|[|[|[|i]]]]]];cbn[double_difference_point_plug values double_difference_point_values];try assumption;reflexivity. }
 assert(BValues:forall i,source_bounded M(values i)(succM M k)).
 { intros[|[|[|[|[|[|i]]]]]];cbn[values double_difference_point_values];try assumption.
   - exact(representation_member_expression_bound M rho 0 k(HNames 0 ltac:(auto))a HA).
   - exact(representation_member_expression_bound M rho 1 k(HNames 1 ltac:(auto))b HB).
   - exact(representation_member_expression_bound M rho 2 k(HNames 2 ltac:(auto))c HC).
   - exact(representation_member_expression_bound M rho 3 k(HNames 3 ltac:(auto))d HD). }
 assert(HAll:forall p f,code_relation M rho(E_double_difference_all p)f ->source_universal_template_graph M values p f).
 { intros p f HF. destruct(code_relation_total M(source_prop_expression p)values)as(body&HBody).
   assert(HGraph:code_relation M rho(code_plug double_difference_point_plug(source_prop_expression p))body).
   { exact(proj2(code_relation_plug M rho values double_difference_point_plug(source_prop_expression p)body HValues)HBody). }
   exists body. split;[exact HBody|].
   exact(proj1(schema_expression_graph M rho SFAll _ (CEconst 0)body(zeroM M)f HGraph eq_refl)HF). }
 destruct(HAll pair_union_conclusion target HT)as(body&HBody&HQuant).
 apply(source_empty_universal_macro M values k pair_union_hypotheses pair_union_conclusion[profile;point1;point2]body target law
  BValues pair_union_representation_program);[|exact HBody|exact HQuant|exact HTelescope].
 constructor;[exact(HAll pair_union_profile_template profile HProfile)|].
 constructor;[exact(HAll pair_union_left_template point1 HP1)|].
 constructor;[exact(HAll pair_union_right_template point2 HP2)|constructor].
Qed.
Print Assumptions source_empty_pair_union_universal.
