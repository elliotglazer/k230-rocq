(** The actual universal implication deduction. Five quantified premises
    give the two difference profiles, assignment-carrier coverage, and the
    two child points. All matrix holes may have nonstandard internal depth. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceRepresentationDifferencePoints
 SourceRepresentationPointBounds SourceImplicationDifferenceProgram SourceUniversalMacro SourceFiniteTelescope
 SourceRepresentationDifferenceProgram SourcePropositionalTemplates NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition implication_difference_point_plug i:=match i with
 |0=>representation_member_expression(CEvar 0)|1=>representation_member_expression(CEvar 1)
 |2=>representation_member_expression(CEvar 2)|3=>representation_member_expression(CEvar 3)
 |4=>CEvar 4|5=>CEvar 5|6=>CEvar 6|_=>representation_member_expression(CEvar 7) end.
Definition E_implication_difference_all p:=E_sf SFAll
 (code_plug implication_difference_point_plug(source_prop_expression p))(CEconst 0).
Definition implication_difference_point_values {A}(a b c d x y g carrier:A)i:=match i with
 |0=>a|1=>b|2=>c|3=>d|4=>x|5=>y|6=>g|_=>carrier end.

Theorem source_empty_implication_difference_universal M rho k profile1 profile2 coverage point1 point2 target law:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->coding_lt M(rho 7)k ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->
 code_relation M rho(E_implication_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))))profile1 ->
 code_relation M rho(E_implication_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2))))profile2 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2 ->
 code_relation M rho(E_implication_difference_all implication_difference_conclusion)target ->
 source_finite_telescope M[profile1;profile2;coverage;point1;point2]target law ->
 source_full_prv M(zeroM M)(zeroM M)(zeroM M)law.
Proof.
 intros HNames HCarrier B4 B5 B6 HP1 HP2 HCoverage HLeft HRight HT HTelescope.
 destruct(code_relation_total M(representation_member_expression(CEvar 0))rho)as(a&HA).
 destruct(code_relation_total M(representation_member_expression(CEvar 1))rho)as(b&HB).
 destruct(code_relation_total M(representation_member_expression(CEvar 2))rho)as(c&HC).
 destruct(code_relation_total M(representation_member_expression(CEvar 3))rho)as(d&HD).
 destruct(code_relation_total M(representation_member_expression(CEvar 7))rho)as(carrier&HCA).
 set(values:=implication_difference_point_values a b c d(rho 4)(rho 5)(rho 6)carrier).
 assert(HValues:forall i,code_relation M rho(implication_difference_point_plug i)(values i)).
 { intros[|[|[|[|[|[|[|i]]]]]]];cbn[implication_difference_point_plug values implication_difference_point_values];try assumption;reflexivity. }
 assert(BValues:forall i,source_bounded M(values i)(succM M k)).
 { intros[|[|[|[|[|[|[|i]]]]]]];cbn[values implication_difference_point_values];try assumption.
   - exact(representation_member_expression_bound M rho 0 k(HNames 0 ltac:(auto))a HA).
   - exact(representation_member_expression_bound M rho 1 k(HNames 1 ltac:(auto))b HB).
   - exact(representation_member_expression_bound M rho 2 k(HNames 2 ltac:(auto))c HC).
   - exact(representation_member_expression_bound M rho 3 k(HNames 3 ltac:(auto))d HD).
   - exact(representation_member_expression_bound M rho 7 k HCarrier carrier HCA). }
 assert(HAll:forall p f,code_relation M rho(E_implication_difference_all p)f ->source_universal_template_graph M values p f).
 { intros p f HF. destruct(code_relation_total M(source_prop_expression p)values)as(body&HBody).
   assert(HGraph:code_relation M rho(code_plug implication_difference_point_plug(source_prop_expression p))body).
   { exact(proj2(code_relation_plug M rho values implication_difference_point_plug(source_prop_expression p)body HValues)HBody). }
   exists body. split;[exact HBody|].
   exact(proj1(schema_expression_graph M rho SFAll _ (CEconst 0)body(zeroM M)f HGraph eq_refl)HF). }
 destruct(HAll implication_difference_conclusion target HT)as(body&HBody&HQuant).
 apply(source_empty_universal_macro M values k implication_difference_hypotheses implication_difference_conclusion
  [profile1;profile2;coverage;point1;point2]body target law BValues implication_difference_representation_program);
  [|exact HBody|exact HQuant|exact HTelescope].
 constructor;[exact(HAll _ _ HP1)|].
 constructor;[exact(HAll _ _ HP2)|].
 constructor;[exact(HAll _ _ HCoverage)|].
 constructor;[exact(HAll _ _ HLeft)|].
 constructor;[exact(HAll _ _ HRight)|constructor].
Qed.
Print Assumptions source_empty_implication_difference_universal.
