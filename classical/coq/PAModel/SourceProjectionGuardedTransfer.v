(** Quantify the actual projection point over the tested carrier value.
    Every hypothesis required for universal introduction has explicit vacuity. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceRepresentationDifferenceProgram SourceNamedVacuity SourceNamedQuantifierRules SourceProjectionHeadPoint SourceGuardedNamedExistential.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EPG_condition:=SPTAnd(SPTSlot 7)(SPTSlot 0).
Definition EPG_body:=SPTImpl(SPTSlot 4)(SPTIff(SPTSlot 9)(SPTSlot 3)).
Definition EPG_result:=SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 0)(SPTIff(SPTSlot 11)(SPTSlot 12))).
Ltac epg_ctx:=apply SPTCtx;cbn;auto 12.
Lemma EPG_point_program:source_prop_program[EPH_result](SPTImpl EPG_condition EPG_body).
Proof.
 unfold EPH_result,EPG_condition,EPG_body. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 0).
 - eapply SPTIE with(a:=SPTSlot 4);[|epg_ctx]. eapply SPTIE with(a:=SPTSlot 7);[epg_ctx|].
   apply SPTCE1 with(b:=SPTSlot 0);epg_ctx.
 - apply SPTCE2 with(a:=SPTSlot 7);epg_ctx.
Qed.
Lemma EPG_result_program:source_prop_program
 [SPTImpl EPG_condition(SPTSlot 18);SPTImpl(SPTSlot 18)(SPTIff(SPTSlot 11)(SPTSlot 12))]EPG_result.
Proof.
 unfold EPG_condition,EPG_result. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 18);[epg_ctx|].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 7)(SPTSlot 0));[epg_ctx|apply SPTCI;epg_ctx].
Qed.
Definition projection_guarded_values {A}(values:nat->A)i:=match i with
 |0=>values 4|1=>values 9|2=>values 3|3=>values 18|4=>values 11|_=>values 12 end.
Theorem source_descriptor_projection_guarded_transfer M T values a guardedbody left right result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression EPG_body)guardedbody ->
 source_named_quantifier M true a guardedbody(values 18) ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 9)))left ->
 source_named_quantifier M false a left(values 11) ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 4)(SPTSlot 3)))right ->
 source_named_quantifier M false a right(values 12) ->
 source_named_vacuous M a(values 7) ->source_named_vacuous M a(values 0) ->
 source_descriptor_template M T values EPH_result ->
 code_relation M values(source_prop_expression EPG_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HBody HAll HL HExL HR HExR VH VP PPoint HResult.
 assert(PAll:source_descriptor_template M T values(SPTImpl EPG_condition(SPTSlot 18))).
 { apply(source_descriptor_template_named_all M T values a EPG_condition EPG_body 18 guardedbody k HB HBody HAll).
   - unfold EPG_condition. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB EPG_point_program).
     intros p[<-|[]]. exact PPoint. }
 assert(PEquiv:source_descriptor_template M T values(SPTImpl(SPTSlot 18)(SPTIff(SPTSlot 11)(SPTSlot 12)))).
 { intros f HF. apply(source_descriptor_guarded_named_existential M T(projection_guarded_values values)a guardedbody left right f k).
   - intros[|[|[|[|[|i]]]]];apply HB.
   - exact HBody.
   - exact HL.
   - exact HR.
   - exact HAll.
   - exact HExL.
   - exact HExR.
   - exact HF. }
 exact(source_descriptor_template_program M T values k _ _ HB EPG_result_program
  ltac:(intros p[<-|[<-|[]]];assumption)result HResult).
Qed.
Print Assumptions source_descriptor_projection_guarded_transfer.
