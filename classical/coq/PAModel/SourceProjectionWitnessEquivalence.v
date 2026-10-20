(** A real source-calculus projection-witness theorem with arbitrary
    internal theta. The equivalence hypothesis is a literal antecedent;
    no completeness or semantic inference is used. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceRepresentationDifferenceProgram SourceNamedVacuity SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EPW_body:=SPTImpl(SPTSlot 0)(SPTIff(SPTSlot 1)(SPTSlot 2)).
Definition EPW_all_use:=SPTImpl(SPTSlot 3)EPW_body.
Definition EPW_intro:=SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 0))(SPTSlot 5).
Definition EPW_forward_goal:=SPTImpl(SPTSlot 3)(SPTSlot 2).
Definition EPW_forward:=SPTImpl(SPTSlot 5)EPW_forward_goal.
Definition EPW_backward_goal:=SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 2)(SPTSlot 5)).
Definition EPW_backward:=SPTImpl(SPTSlot 4)EPW_backward_goal.
Definition EPW_result:=SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTIff(SPTSlot 5)(SPTSlot 2))).
Ltac epw_ctx:=apply SPTCtx;cbn;auto 12.
Lemma EPW_forward_program:source_prop_program[EPW_all_use]
 (SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 0))EPW_forward_goal).
Proof.
 unfold EPW_all_use,EPW_body,SPTIff,EPW_forward_goal. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCE1 with(b:=SPTSlot 0);epw_ctx].
 apply SPTCE1 with(b:=SPTImpl(SPTSlot 2)(SPTSlot 1)).
 eapply SPTIE with(a:=SPTSlot 0);[|apply SPTCE2 with(a:=SPTSlot 1);epw_ctx].
 eapply SPTIE with(a:=SPTSlot 3);epw_ctx.
Qed.
Lemma EPW_backward_program:source_prop_program[EPW_all_use;EPW_intro]
 (SPTImpl(SPTSlot 0)EPW_backward_goal).
Proof.
 unfold EPW_all_use,EPW_body,SPTIff,EPW_intro,EPW_backward_goal. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 1)(SPTSlot 0));[epw_ctx|]. apply SPTCI;[|epw_ctx].
 eapply SPTIE with(a:=SPTSlot 2);[|epw_ctx].
 apply SPTCE2 with(a:=SPTImpl(SPTSlot 1)(SPTSlot 2)).
 eapply SPTIE with(a:=SPTSlot 0);[|epw_ctx]. eapply SPTIE with(a:=SPTSlot 3);epw_ctx.
Qed.
Lemma EPW_result_program:source_prop_program[EPW_forward;EPW_backward]EPW_result.
Proof.
 unfold EPW_forward,EPW_forward_goal,EPW_backward,EPW_backward_goal,EPW_result,SPTIff.
 do 2 apply SPTII. apply SPTCI;apply SPTII.
 - eapply SPTIE with(a:=SPTSlot 3);[|epw_ctx]. eapply SPTIE with(a:=SPTSlot 5);epw_ctx.
 - eapply SPTIE with(a:=SPTSlot 2);[|epw_ctx]. eapply SPTIE with(a:=SPTSlot 3);[|epw_ctx].
   eapply SPTIE with(a:=SPTSlot 4);epw_ctx.
Qed.
Theorem source_descriptor_projection_witness_equivalence M T values z body pair result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression EPW_body)body ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 1)(SPTSlot 0)))pair ->
 source_named_quantifier M true z body(values 3) ->
 source_named_quantifier M false z(values 0)(values 4) ->
 source_named_quantifier M false z pair(values 5) ->
 source_named_vacuous M z(values 2) ->
 code_relation M values(source_prop_expression EPW_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HBody HPair HAll HExt HEx VTheta HResult.
 pose proof(source_prop_template_bound M values EPW_body k HB body HBody)as BBody.
 pose proof(source_prop_template_bound M values(SPTAnd(SPTSlot 1)(SPTSlot 0))k HB pair HPair)as BPair.
 pose proof(source_named_quantifier_is_vacuous M true z body(values 3)k BBody HAll)as VAll.
 pose proof(source_named_quantifier_is_vacuous M false z pair(values 5)k BPair HEx)as VEx.
 assert(PAll:source_descriptor_template M T values EPW_all_use).
 { intros f HF. destruct(source_prop_template_binary M values SFImpl(SPTSlot 3)EPW_body f HF)
   as(a&b&HA&HB'&HO). change(a=values 3)in HA. subst a.
   rewrite(code_relation_functional M _ values b body HB' HBody)in HO.
   exact(source_descriptor_named_all_specialization M T z body(values 3)f k BBody HAll HO). }
 assert(PIntro:source_descriptor_template M T values EPW_intro).
 { exact(source_descriptor_template_named_intro M T values z(SPTAnd(SPTSlot 1)(SPTSlot 0))5 pair k BPair HPair HEx). }
 assert(PForward:source_descriptor_template M T values EPW_forward).
 { apply(source_descriptor_template_named_exists M T values z(SPTAnd(SPTSlot 1)(SPTSlot 0))5 EPW_forward_goal pair HPair HEx).
   - unfold EPW_forward_goal. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB EPW_forward_program).
     intros p[<-|[]]. exact PAll. }
 assert(PBackward:source_descriptor_template M T values EPW_backward).
 { apply(source_descriptor_template_named_exists M T values z(SPTSlot 0)4 EPW_backward_goal(values 0)eq_refl HExt).
   - unfold EPW_backward_goal. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB EPW_backward_program).
     intros p[<-|[<-|[]]];assumption. }
 exact(source_descriptor_template_program M T values k _ _ HB EPW_result_program
  ltac:(intros p[<-|[<-|[]]];assumption)result HResult).
Qed.
Print Assumptions source_descriptor_projection_witness_equivalence.
