(** Actual guarded existential congruence for arbitrary internally coded
    matrices. Named-binder vacuity is derived from the quantifier graphs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceRepresentationDifferenceProgram SourceNamedVacuity SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition GNE_body:=SPTImpl(SPTSlot 0)(SPTIff(SPTSlot 1)(SPTSlot 2)).
Definition GNE_all_use:=SPTImpl(SPTSlot 3)GNE_body.
Definition GNE_forward_goal:=SPTImpl(SPTSlot 3)(SPTSlot 5).
Definition GNE_backward_goal:=SPTImpl(SPTSlot 3)(SPTSlot 4).
Definition GNE_forward:=SPTImpl(SPTSlot 4)GNE_forward_goal.
Definition GNE_backward:=SPTImpl(SPTSlot 5)GNE_backward_goal.
Definition GNE_result:=SPTImpl(SPTSlot 3)(SPTIff(SPTSlot 4)(SPTSlot 5)).
Ltac gne_ctx:=apply SPTCtx;cbn;auto 10.
Lemma GNE_forward_program:source_prop_program[GNE_all_use;SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTSlot 5)]
 (SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))GNE_forward_goal).
Proof.
 unfold GNE_all_use,GNE_body,GNE_forward_goal,SPTIff. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 0)(SPTSlot 2));[gne_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 1);gne_ctx.
 - eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCE2 with(a:=SPTSlot 0);gne_ctx].
   apply SPTCE1 with(b:=SPTImpl(SPTSlot 2)(SPTSlot 1)).
   eapply SPTIE with(a:=SPTSlot 0);[|apply SPTCE1 with(b:=SPTSlot 1);gne_ctx].
   eapply SPTIE with(a:=SPTSlot 3);gne_ctx.
Qed.
Lemma GNE_backward_program:source_prop_program[GNE_all_use;SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 4)]
 (SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 2))GNE_backward_goal).
Proof.
 unfold GNE_all_use,GNE_body,GNE_backward_goal,SPTIff. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 0)(SPTSlot 1));[gne_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 2);gne_ctx.
 - eapply SPTIE with(a:=SPTSlot 2);[|apply SPTCE2 with(a:=SPTSlot 0);gne_ctx].
   apply SPTCE2 with(a:=SPTImpl(SPTSlot 1)(SPTSlot 2)).
   eapply SPTIE with(a:=SPTSlot 0);[|apply SPTCE1 with(b:=SPTSlot 2);gne_ctx].
   eapply SPTIE with(a:=SPTSlot 3);gne_ctx.
Qed.
Lemma GNE_result_program:source_prop_program[GNE_forward;GNE_backward]GNE_result.
Proof.
 unfold GNE_forward,GNE_backward,GNE_forward_goal,GNE_backward_goal,GNE_result,SPTIff.
 apply SPTII,SPTCI;apply SPTII.
 - eapply SPTIE with(a:=SPTSlot 3);[|gne_ctx]. eapply SPTIE with(a:=SPTSlot 4);gne_ctx.
 - eapply SPTIE with(a:=SPTSlot 3);[|gne_ctx]. eapply SPTIE with(a:=SPTSlot 5);gne_ctx.
Qed.
Theorem source_descriptor_guarded_named_existential M T values x body left right result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression GNE_body)body ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 0)(SPTSlot 1)))left ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 0)(SPTSlot 2)))right ->
 source_named_quantifier M true x body(values 3) ->
 source_named_quantifier M false x left(values 4) ->source_named_quantifier M false x right(values 5) ->
 code_relation M values(source_prop_expression GNE_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HBody HLeft HRight HAll HEL HER HResult.
 pose proof(source_prop_template_bound M values GNE_body k HB body HBody)as BB.
 pose proof(source_prop_template_bound M values(SPTAnd(SPTSlot 0)(SPTSlot 1))k HB left HLeft)as BL.
 pose proof(source_prop_template_bound M values(SPTAnd(SPTSlot 0)(SPTSlot 2))k HB right HRight)as BR.
 pose proof(source_named_quantifier_is_vacuous M true x body(values 3)k BB HAll)as VA.
 pose proof(source_named_quantifier_is_vacuous M false x left(values 4)k BL HEL)as VL.
 pose proof(source_named_quantifier_is_vacuous M false x right(values 5)k BR HER)as VR.
 assert(PAll:source_descriptor_template M T values GNE_all_use).
 { intros f HF. destruct(source_prop_template_binary M values SFImpl(SPTSlot 3)GNE_body f HF)
   as(a&b&HA&HBody'&HO). change(a=values 3)in HA. subst a.
   rewrite(code_relation_functional M _ values b body HBody' HBody)in HO.
   exact(source_descriptor_named_all_specialization M T x body(values 3)f k BB HAll HO). }
 assert(PForward:source_descriptor_template M T values GNE_forward).
 { apply(source_descriptor_template_named_exists M T values x(SPTAnd(SPTSlot 0)(SPTSlot 1))4 GNE_forward_goal left HLeft HEL).
   - unfold GNE_forward_goal. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB GNE_forward_program).
     intros p[<-|[<-|[]]];[exact PAll|].
     exact(source_descriptor_template_named_intro M T values x(SPTAnd(SPTSlot 0)(SPTSlot 2))5 right k BR HRight HER). }
 assert(PBackward:source_descriptor_template M T values GNE_backward).
 { apply(source_descriptor_template_named_exists M T values x(SPTAnd(SPTSlot 0)(SPTSlot 2))5 GNE_backward_goal right HRight HER).
   - unfold GNE_backward_goal. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB GNE_backward_program).
     intros p[<-|[<-|[]]];[exact PAll|].
     exact(source_descriptor_template_named_intro M T values x(SPTAnd(SPTSlot 0)(SPTSlot 1))4 left k BL HLeft HEL). }
 exact(source_descriptor_template_program M T values k _ _ HB GNE_result_program
  ltac:(intros p[<-|[<-|[]]];assumption)result HResult).
Qed.
Print Assumptions source_descriptor_guarded_named_existential.
