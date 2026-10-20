(** Close the new environment and head-assignment roles in the checked
 environment-extension rule. Every eigenname restriction is explicit. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceNamedVacuity SourceNamedQuantifierRules SourceEnvironmentExtensionProgram.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition environment_extension_outer:=SPTAnd(SPTSlot 0)(SPTSlot 6).
Definition environment_extension_inner:=SPTAnd environment_extension_outer(SPTSlot 2).
Definition environment_extension_local_body:=SPTImpl(SPTSlot 7)(SPTSlot 4).
Definition environment_extension_head_body:=SPTImpl(SPTSlot 2)(SPTSlot 8).
Definition environment_extension_all_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 6)(SPTSlot 9)).
Lemma environment_extension_environment_program:source_prop_program[environment_extension_result]
 (SPTImpl environment_extension_inner environment_extension_local_body).
Proof.
 unfold environment_extension_result,environment_extension_inner,environment_extension_outer,environment_extension_local_body.
 do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 7);[|apply SPTCtx;cbn;auto 12].
 eapply SPTIE with(a:=SPTSlot 2).
 - eapply SPTIE with(a:=SPTSlot 6).
   + eapply SPTIE with(a:=SPTSlot 0);[apply SPTCtx;cbn;auto 12|].
     apply SPTCE1 with(b:=SPTSlot 6). apply SPTCE1 with(b:=SPTSlot 2). apply SPTCtx;cbn;auto 12.
   + apply SPTCE2 with(a:=SPTSlot 0). apply SPTCE1 with(b:=SPTSlot 2). apply SPTCtx;cbn;auto 12.
 - apply SPTCE2 with(a:=SPTAnd(SPTSlot 0)(SPTSlot 6)). apply SPTCtx;cbn;auto 12.
Qed.
Lemma environment_extension_head_program:source_prop_program[SPTImpl environment_extension_inner(SPTSlot 8)]
 (SPTImpl environment_extension_outer environment_extension_head_body).
Proof.
 unfold environment_extension_inner,environment_extension_outer,environment_extension_head_body.
 do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 6))(SPTSlot 2));[apply SPTCtx;cbn;auto 12|].
 apply SPTCI;apply SPTCtx;cbn;auto 12.
Qed.
Lemma environment_extension_all_program:source_prop_program[SPTImpl environment_extension_outer(SPTSlot 9)]environment_extension_all_result.
Proof.
 unfold environment_extension_outer,environment_extension_all_result.
 do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 0)(SPTSlot 6));[apply SPTCtx;cbn;auto 12|].
 apply SPTCI;apply SPTCtx;cbn;auto 12.
Qed.
Theorem source_descriptor_environment_extension_quantifiers M T values e a localbody headbody result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression environment_extension_local_body)localbody ->
 code_relation M values(source_prop_expression environment_extension_head_body)headbody ->
 source_named_quantifier M true e localbody(values 8) ->source_named_quantifier M true a headbody(values 9) ->
 source_named_vacuous M e(values 0) ->source_named_vacuous M e(values 6) ->source_named_vacuous M e(values 2) ->
 source_named_vacuous M a(values 0) ->source_named_vacuous M a(values 6) ->
 source_descriptor_template M T values environment_extension_result ->
 code_relation M values(source_prop_expression environment_extension_all_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HLocal HHead HE HA VE0 VE6 VE2 VA0 VA6 PBase HResult.
 assert(PE:source_descriptor_template M T values(SPTImpl environment_extension_inner environment_extension_local_body)).
 { apply(source_descriptor_template_program M T values k _ _ HB environment_extension_environment_program).
   intros p[<-|[]]. exact PBase. }
 assert(PAE:source_descriptor_template M T values(SPTImpl environment_extension_inner(SPTSlot 8))).
 { apply(source_descriptor_template_named_all M T values e environment_extension_inner environment_extension_local_body 8 localbody k HB HLocal HE).
   - unfold environment_extension_inner,environment_extension_outer. cbn[source_prop_named_vacuity]. auto.
   - exact PE. }
 assert(PA:source_descriptor_template M T values(SPTImpl environment_extension_outer environment_extension_head_body)).
 { apply(source_descriptor_template_program M T values k _ _ HB environment_extension_head_program).
   intros p[<-|[]]. exact PAE. }
 assert(PAA:source_descriptor_template M T values(SPTImpl environment_extension_outer(SPTSlot 9))).
 { apply(source_descriptor_template_named_all M T values a environment_extension_outer environment_extension_head_body 9 headbody k HB HHead HA).
   - unfold environment_extension_outer. cbn[source_prop_named_vacuity]. auto.
   - exact PA. }
 exact(source_descriptor_template_program M T values k _ _ HB environment_extension_all_program
  ltac:(intros p[<-|[]];exact PAA)result HResult).
Qed.
Print Assumptions source_descriptor_environment_extension_quantifiers.
