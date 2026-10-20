(** The two actual existential eliminations in the An successor proof.
    The old An and newly constructed Op3 set are distinct named witnesses. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceNamedVacuity SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition ECW_point:=SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 5)(SPTSlot 6)).
Definition ECW_op:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 8)))).
Definition ECW_carrier:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)).
Definition ECW_intro:=SPTImpl(SPTAnd(SPTSlot 4)(SPTSlot 6))(SPTSlot 10).
Definition ECW_goal:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 5)(SPTSlot 10))).
Definition ECW_op_use:=SPTImpl(SPTSlot 8)ECW_goal.
Definition ECW_old_goal:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 10)).
Definition ECW_old_use:=SPTImpl(SPTSlot 9)ECW_old_goal.
Definition ECW_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 9)(SPTSlot 10))).
Ltac ecw_ctx:=apply SPTCtx;cbn;auto 12.
Lemma ECW_point_program:source_prop_program[ECW_point;ECW_intro]
 (SPTImpl(SPTAnd(SPTSlot 4)(SPTSlot 7))ECW_goal).
Proof.
 unfold ECW_point,ECW_intro,ECW_goal. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 6));[ecw_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 7);ecw_ctx.
 - eapply SPTIE with(a:=SPTSlot 5);[|ecw_ctx].
   eapply SPTIE with(a:=SPTSlot 7);[ecw_ctx|]. apply SPTCE2 with(a:=SPTSlot 4);ecw_ctx.
Qed.
Lemma ECW_old_program:source_prop_program[ECW_op;ECW_carrier;ECW_op_use]
 (SPTImpl(SPTAnd(SPTSlot 2)(SPTSlot 5))ECW_old_goal).
Proof.
 unfold ECW_op,ECW_carrier,ECW_op_use,ECW_goal,ECW_old_goal. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 5);[|apply SPTCE2 with(a:=SPTSlot 2);ecw_ctx].
 eapply SPTIE with(a:=SPTSlot 1);[|ecw_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|ecw_ctx].
 eapply SPTIE with(a:=SPTSlot 8);[ecw_ctx|].
 eapply SPTIE with(a:=SPTSlot 3).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1);[|ecw_ctx]. eapply SPTIE with(a:=SPTSlot 0);ecw_ctx.
   + apply SPTCE1 with(b:=SPTSlot 5);ecw_ctx.
 - eapply SPTIE with(a:=SPTSlot 1);[|ecw_ctx]. eapply SPTIE with(a:=SPTSlot 0);ecw_ctx.
Qed.
Lemma ECW_result_program:source_prop_program[ECW_old_use]ECW_result.
Proof.
 unfold ECW_old_use,ECW_old_goal,ECW_result. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|ecw_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|ecw_ctx].
 eapply SPTIE with(a:=SPTSlot 9);ecw_ctx.
Qed.
Theorem source_descriptor_environment_witness_shell M T values oldname newname opbody oldbody targetbody result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 7)))opbody ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 2)(SPTSlot 5)))oldbody ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 6)))targetbody ->
 source_named_quantifier M false newname opbody(values 8) ->
 source_named_quantifier M false oldname oldbody(values 9) ->
 source_named_quantifier M false newname targetbody(values 10) ->
 source_named_vacuous M newname(values 0) ->source_named_vacuous M newname(values 1) ->
 source_named_vacuous M newname(values 5) ->source_named_vacuous M newname(values 10) ->
 source_named_vacuous M oldname(values 0) ->source_named_vacuous M oldname(values 1) ->
 source_named_vacuous M oldname(values 10) ->
 source_descriptor_template M T values ECW_point ->source_descriptor_template M T values ECW_op ->
 source_descriptor_template M T values ECW_carrier ->
 code_relation M values(source_prop_expression ECW_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HOp HOld HTarget HQOp HQOld HQTarget VN0 VN1 VN5 VN10 VO0 VO1 VO10 PP POp PC HResult.
 assert(PIntro:source_descriptor_template M T values ECW_intro).
 { exact(source_descriptor_template_named_intro M T values newname(SPTAnd(SPTSlot 4)(SPTSlot 6))10 targetbody k
   (source_prop_template_bound M values _ k HB targetbody HTarget)HTarget HQTarget). }
 assert(POpPoint:source_descriptor_template M T values(SPTImpl(SPTAnd(SPTSlot 4)(SPTSlot 7))ECW_goal)).
 { apply(source_descriptor_template_program M T values k _ _ HB ECW_point_program).
   intros p[<-|[<-|[]]];assumption. }
 assert(POpUse:source_descriptor_template M T values ECW_op_use).
 { apply(source_descriptor_template_named_exists M T values newname(SPTAnd(SPTSlot 4)(SPTSlot 7))8 ECW_goal opbody HOp HQOp).
   - unfold ECW_goal. cbn[source_prop_named_vacuity]. auto.
   - exact POpPoint. }
 assert(POldPoint:source_descriptor_template M T values(SPTImpl(SPTAnd(SPTSlot 2)(SPTSlot 5))ECW_old_goal)).
 { apply(source_descriptor_template_program M T values k _ _ HB ECW_old_program).
   intros p[<-|[<-|[<-|[]]]];assumption. }
 assert(POldUse:source_descriptor_template M T values ECW_old_use).
 { apply(source_descriptor_template_named_exists M T values oldname(SPTAnd(SPTSlot 2)(SPTSlot 5))9 ECW_old_goal oldbody HOld HQOld).
   - unfold ECW_old_goal. cbn[source_prop_named_vacuity]. auto.
   - exact POldPoint. }
 exact(source_descriptor_template_program M T values k _ _ HB ECW_result_program
  ltac:(intros p[<-|[]];exact POldUse)result HResult).
Qed.
Print Assumptions source_descriptor_environment_witness_shell.
