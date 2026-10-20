(** The logical environment-extension step with an arbitrary internal
 EnvF hole. The actual Op3 law is the only nonlogical premise of the generic
 rule; its ZFR wrapper supplies the checked fixed certificate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms
 SourceDescriptorNamedUniversal SourceEnvironmentCarrierFixed SourceZFRProvability SourceSetTheoryDescriptors
 SourceNamedVacuity SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition environment_extension_point_law:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 4)))).
Definition environment_extension_coverage_use:=SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 5)(SPTSlot 1)).
Definition environment_extension_goal:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 2)(SPTSlot 4))).
Definition environment_extension_point_use:=SPTImpl(SPTAnd(SPTSlot 5)(SPTSlot 3))environment_extension_goal.
Definition environment_extension_exists_use:=SPTImpl(SPTSlot 7)environment_extension_goal.
Definition environment_extension_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 7)(SPTSlot 4)))).
Lemma environment_extension_point_program:
 source_prop_program[environment_extension_point_law;environment_extension_coverage_use]environment_extension_point_use.
Proof.
 unfold environment_extension_point_law,environment_extension_coverage_use,environment_extension_point_use,environment_extension_goal.
 do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 3).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 12.
     * eapply SPTIE with(a:=SPTSlot 5).
       -- eapply SPTIE with(a:=SPTSlot 6);apply SPTCtx;cbn;auto 12.
       -- apply SPTCE1 with(b:=SPTSlot 3). apply SPTCtx;cbn;auto 12.
   + apply SPTCtx;cbn;auto 12.
 - apply SPTCE2 with(a:=SPTSlot 5). apply SPTCtx;cbn;auto 12.
Qed.
Lemma environment_extension_result_program:
 source_prop_program[environment_extension_exists_use]environment_extension_result.
Proof.
 unfold environment_extension_exists_use,environment_extension_result,environment_extension_goal.
 do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 2);[|apply SPTCtx;cbn;auto 12].
 eapply SPTIE with(a:=SPTSlot 6);[|apply SPTCtx;cbn;auto 12].
 eapply SPTIE with(a:=SPTSlot 0);[|apply SPTCtx;cbn;auto 12].
 eapply SPTIE with(a:=SPTSlot 7);apply SPTCtx;cbn;auto 12.
Qed.
Theorem source_descriptor_environment_extension M T values witness previousbody newbody law result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression(SPTImpl(SPTSlot 5)(SPTSlot 1)))previousbody ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 5)(SPTSlot 3)))newbody ->
 source_named_quantifier M true witness previousbody(values 6) ->
 source_named_quantifier M false witness newbody(values 7) ->
 source_named_vacuous M witness(values 0) ->source_named_vacuous M witness(values 2) ->
 source_named_vacuous M witness(values 4) ->
 code_relation M values(source_prop_expression environment_extension_point_law)law ->
 code_relation M values(source_prop_expression environment_extension_result)result ->
 source_descriptor_provable M T law ->source_descriptor_provable M T result.
Proof.
 intros HB HPrevious HNew HAll HEx HV0 HV2 HV4 HLaw HResult PLaw.
 assert(BPrevious:source_bounded M previousbody k).
 { exact(source_prop_template_bound M values _ k HB previousbody HPrevious). }
 assert(VAll:source_named_vacuous M witness(values 6)).
 { exact(source_named_quantifier_is_vacuous M true witness previousbody(values 6)k BPrevious HAll). }
 assert(TExt:source_descriptor_template M T values environment_extension_point_law).
 { intros f HF. rewrite(code_relation_functional M _ values f law HF HLaw). exact PLaw. }
 assert(TUse:source_descriptor_template M T values environment_extension_coverage_use).
 { intros f HF. unfold environment_extension_coverage_use in HF.
   destruct(source_prop_template_binary M values SFImpl(SPTSlot 6)(SPTImpl(SPTSlot 5)(SPTSlot 1))f HF)
    as(a&b&HA&HBody&HO). change(a=values 6)in HA. subst a.
   rewrite(code_relation_functional M _ values b previousbody HBody HPrevious)in HO.
   exact(source_descriptor_named_all_specialization M T witness previousbody(values 6)f k BPrevious HAll HO). }
 assert(TPoint:source_descriptor_template M T values environment_extension_point_use).
 { apply(source_descriptor_template_program M T values k _ _ HB environment_extension_point_program).
   intros p[<-|[<-|[]]];assumption. }
 assert(TExists:source_descriptor_template M T values environment_extension_exists_use).
 { apply(source_descriptor_template_named_exists M T values witness(SPTAnd(SPTSlot 5)(SPTSlot 3))7
    environment_extension_goal newbody HNew HEx).
   - unfold environment_extension_goal. cbn[source_prop_named_vacuity]. auto.
   - exact TPoint. }
 exact(source_descriptor_template_program M T values k _ _ HB environment_extension_result_program
  ltac:(intros p[<-|[]];exact TExists) result HResult).
Qed.
Theorem source_zfr_environment_extension M rho values witness previousbody newbody law result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression(SPTImpl(SPTSlot 5)(SPTSlot 1)))previousbody ->
 code_relation M values(source_prop_expression(SPTAnd(SPTSlot 5)(SPTSlot 3)))newbody ->
 source_named_quantifier M true witness previousbody(values 6) ->
 source_named_quantifier M false witness newbody(values 7) ->
 source_named_vacuous M witness(values 0) ->source_named_vacuous M witness(values 2) ->
 source_named_vacuous M witness(values 4) ->
 code_relation M rho source_environment_extension_point_expression law ->
 code_relation M values(source_prop_expression environment_extension_point_law)law ->
 code_relation M values(source_prop_expression environment_extension_result)result ->source_zfr_provable M result.
Proof.
 intros HB HP HN HA HE V0 V2 V4 HFixed HL HR.
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_environment_extension M ZFRSourceDescriptor values witness previousbody newbody law result k
  HB HP HN HA HE V0 V2 V4 HL HR(proj2(source_zfr_descriptor_provable M law)(source_zfr_environment_extension_point M rho law HFixed))).
Qed.
Print Assumptions source_descriptor_environment_extension.
Print Assumptions source_zfr_environment_extension.
