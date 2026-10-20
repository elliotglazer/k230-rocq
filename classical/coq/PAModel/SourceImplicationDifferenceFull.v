(** Actual common-context universal implication deduction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceRepresentationDifferencePoints
 SourceRepresentationPointBounds SourceImplicationDifferenceProgram SourceImplicationDifferenceUniversal
 SourceUniversalMacro SourceUniversalPrograms SourceFiniteTelescope SourceRepresentationDifferenceProgram
 SourcePropositionalTemplates NumericalContexts NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_implication_difference_universal M rho k cb cc cn profile1 profile2 coverage point1 point2 target:
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->coding_lt M(rho 7)k ->
 source_bounded M(rho 4)(succM M k) ->source_bounded M(rho 5)(succM M k) ->source_bounded M(rho 6)(succM M k) ->context_bounded M cb cc cn k ->
 code_relation M rho(E_implication_difference_all(SPTIff(SPTSlot 2)(SPTDifference(SPTSlot 0)(SPTSlot 1))))profile1 ->
 code_relation M rho(E_implication_difference_all(SPTIff(SPTSlot 3)(SPTDifference(SPTSlot 7)(SPTSlot 2))))profile2 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))coverage ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 0)(SPTSlot 4))))point1 ->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTIff(SPTSlot 1)(SPTSlot 5))))point2 ->
 code_relation M rho(E_implication_difference_all implication_difference_conclusion)target ->
 source_full_prv M cb cc cn profile1 ->source_full_prv M cb cc cn profile2 ->source_full_prv M cb cc cn coverage ->
 source_full_prv M cb cc cn point1 ->source_full_prv M cb cc cn point2 ->source_full_prv M cb cc cn target.
Proof.
 intros HNames HCarrier B4 B5 B6 HCtx HP1 HP2 HCoverage HLeft HRight HT PP1 PP2 PCoverage PLeft PRight.
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
 apply(source_full_universal_program M implication_difference_hypotheses implication_difference_conclusion
  implication_difference_representation_program values k cb cc cn body target BValues HCtx);[|exact HBody|exact HQuant].
 assert(PUse:forall p all,code_relation M rho(E_implication_difference_all p)all ->source_full_prv M cb cc cn all ->
   forall v av,code_relation M values(source_prop_expression p)v ->sf_relation M SFAll v(zeroM M)av ->source_full_prv M cb cc cn av).
 { intros p all HG PG v av HV HAV. destruct(HAll p all HG)as(other&HOther&HOtherAll).
   assert(E:v=other)by(eapply code_relation_functional;eassumption). subst other.
   assert(E:av=all)by(eapply sf_relation_functional;eassumption). now subst av. }
 intros p HP v av HV HAV. destruct HP as[<-|[<-|[<-|[<-|[<-|[]]]]]].
 - exact(PUse _ _ HP1 PP1 v av HV HAV).
 - exact(PUse _ _ HP2 PP2 v av HV HAV).
 - exact(PUse _ _ HCoverage PCoverage v av HV HAV).
 - exact(PUse _ _ HLeft PLeft v av HV HAV).
 - exact(PUse _ _ HRight PRight v av HV HAV).
Qed.
Print Assumptions source_full_implication_difference_universal.
