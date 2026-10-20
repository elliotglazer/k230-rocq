(** Actual named universal specialization and conditional introduction.
 The condition's name-vacuity is explicit; descriptor axioms are closed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceSequents SourceContextProofHelpers SourceProofWeakening
 SourceDerivedRules SourceContextTransport SourceTraceBounds SourceDescriptorProvability SourceDescriptorClosure SourceNamedVacuity SourceNamedSelfSpecialization
 SourceNamedElimination SourceNamedQuantifierRules SourceDescriptorNamedPrograms SourcePropositionalTemplates.
Unset Implicit Arguments.
Theorem source_descriptor_named_all_specialization M T x f allf out k:
 source_bounded M f k ->source_named_quantifier M true x f allf ->
 sf_relation M SFImpl allf f out ->source_descriptor_provable M T out.
Proof.
 intros BF HQ HO. pose proof(source_named_quantifier_bound M true x f allf k BF HQ)as BA.
 pose proof(proj2(source_bounded_accept_binary M SFImpl allf f out k(or_intror(or_intror eq_refl))HO)(conj BA BF))as BO.
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)allf)as(b&c&n&HCons).
 assert(HCtx:context_bounded M b c n k).
 { exact(proj2(context_bounded_cons M _ _ _ allf b c n k HCons)(conj BA(context_bounded_empty M _ _ k))). }
 pose proof(source_full_cons_head M _ _ _ allf b c n k HCons BA HCtx)as PA.
 destruct HQ as(rb&rc&body&HMap&HRen&HAll).
 pose proof(source_full_named_self_all_elim M b c n f x rb rc body allf k BF HMap HRen HAll PA)as PF.
 apply(source_descriptor_provable_from_empty M T out).
 exact(full_source_II M _ _ _ allf f out b c n(ex_intro _ k(conj BO(context_bounded_empty M _ _ k)))PF HCons HO).
Qed.
Theorem source_descriptor_named_all_implication M T x condition f allf point out k:
 source_bounded M condition k ->source_bounded M f k ->source_named_vacuous M x condition ->
 source_named_quantifier M true x f allf ->sf_relation M SFImpl condition f point ->
 sf_relation M SFImpl condition allf out ->source_descriptor_provable M T point ->
 source_descriptor_provable M T out.
Proof.
 intros BC BF HV HQ HP HO(b&c&n&HTheory&PP).
 pose proof(source_named_quantifier_bound M true x f allf k BF HQ)as BA.
 pose proof(proj2(source_bounded_accept_binary M SFImpl condition allf out k(or_intror(or_intror eq_refl))HO)(conj BC BA))as BO.
 assert(C0:context_bounded M b c n k).
 { exact(context_bounded_monotone M b c n(zeroM M)k(proj1 HTheory)(coding_zero_lt_succ M k)). }
 destruct(environment_cons_total M b c n condition)as(u&v&l&HCons).
 assert(C1:context_bounded M u v l k).
 { exact(proj2(context_bounded_cons M b c n condition u v l k HCons)(conj BC C0)). }
 pose proof(source_full_cons_weaken M b c n condition u v l k point HCons C1 PP)as PPoint.
 pose proof(source_full_cons_head M b c n condition u v l k HCons BC C1)as PC.
 pose proof(source_full_modus_ponens M u v l condition f point HP PPoint PC)as PF.
 assert(HV0:source_named_context_vacuous M b c n x).
 { intros a HA. exact(source_named_vacuous_above_bound M a x(zeroM M)(proj1 HTheory a HA)(coding_zero_lt_succ M x)). }
 pose proof(source_named_context_vacuous_cons M b c n condition u v l x HCons HV0 HV)as HV1.
 pose proof(source_full_named_quantifier_all_intro M u v l x f allf HV1 HQ PF)as PAll.
 exists b,c,n. split;[exact HTheory|].
 exact(full_source_II M b c n condition allf out u v l(ex_intro _ k(conj BO C0))PAll HCons HO).
Qed.
Print Assumptions source_descriptor_named_all_specialization.
Print Assumptions source_descriptor_named_all_implication.

Theorem source_descriptor_template_named_all M T rho x condition a index body k:
 (forall i,source_bounded M(rho i)k) ->code_relation M rho(source_prop_expression a)body ->
 source_named_quantifier M true x body(rho index) ->source_prop_named_vacuity M rho x condition ->
 source_descriptor_template M T rho(SPTImpl condition a) ->
 source_descriptor_template M T rho(SPTImpl condition(SPTSlot index)).
Proof.
 intros HB HA HQ HV HP f HF.
 destruct(source_prop_template_binary M rho SFImpl condition(SPTSlot index)f HF)as(c&allf&HC&HAll&HR).
 change(allf=rho index)in HAll. subst allf.
 destruct(sf_relation_total M SFImpl c body)as(point&HPoint).
 exact(source_descriptor_named_all_implication M T x c body(rho index)point f k
  (source_prop_template_bound M rho condition k HB c HC)(source_prop_template_bound M rho a k HB body HA)
  (source_prop_named_vacuity_sound M rho x condition c HV HC)HQ HPoint HR
  (HP point(source_prop_template_join M rho SFImpl condition a c body point HC HA HPoint))).
Qed.
Print Assumptions source_descriptor_template_named_all.
