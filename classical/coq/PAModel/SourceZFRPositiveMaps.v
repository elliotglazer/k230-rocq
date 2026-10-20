(** Actual source implication under positive connectives and quantifiers. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded SourceZFRProvability SourceSetTheoryDescriptors
 SourceDescriptorProvability SourceDescriptorClosure SourcePropositionalTemplates SourcePropositionalRebase SourceWitnessProofComposition
 SourceConditionalProofs SourceConditionalBinary SourceUniversalDistribution SourceExistentialDistribution.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_zfr_map M a b:=forall law,sf_relation M SFImpl a b law ->source_zfr_provable M law.
Lemma source_zfr_right_map_program h A B E:sf_binary h ->source_prop_program[SPTImpl B E]
 (SPTImpl(source_binary_prop h A B)(source_binary_prop h A E)).
Proof.
 intros[HH|[HH|HH]];subst h;cbn[source_binary_prop].
 - apply SPTII,SPTCI.
   + apply(SPTCE1 _ A B),SPTCtx;cbn;tauto.
   + apply(SPTIE _ B E);[apply SPTCtx;cbn;tauto|apply(SPTCE2 _ A B),SPTCtx;cbn;tauto].
 - apply SPTII. apply(SPTDE _ A B).
   + apply SPTCtx;cbn;tauto.
   + apply SPTDI1,SPTCtx;cbn;tauto.
   + apply SPTDI2. apply(SPTIE _ B E);apply SPTCtx;cbn;tauto.
 - apply SPTII,SPTII. apply(SPTIE _ B E);[apply SPTCtx;cbn;tauto|].
   apply(SPTIE _ A B);apply SPTCtx;cbn;tauto.
Qed.
Theorem source_zfr_map_right M h a b e old new k:
 sf_binary h ->source_bounded M a k ->source_bounded M b k ->source_bounded M e k ->
 sf_relation M h a b old ->sf_relation M h a e new ->source_zfr_map M b e ->source_zfr_map M old new.
Proof.
 intros HH BA BB BE HO HN IH law HL.
 destruct(sf_relation_total M SFImpl b e)as(point&HP).
 refine(source_zfr_prop_one M(SPTImpl(SPTSlot 1)(SPTSlot 2))
  (SPTImpl(source_binary_prop h(SPTSlot 0)(SPTSlot 1))(source_binary_prop h(SPTSlot 0)(SPTSlot 2)))
  (source_zfr_right_map_program h(SPTSlot 0)(SPTSlot 1)(SPTSlot 2)HH)
  (source_conditional_five M a b e e e)k point law _ _ _ (IH point HP)).
 - intros[|[|[|[|i]]]];cbn[source_conditional_five];assumption.
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 1)(SPTSlot 2)b e point eq_refl eq_refl HP).
 - refine(source_prop_template_join M _ SFImpl _ _ old new law _ _ HL).
   + exact(source_binary_prop_graph M _ h(SPTSlot 0)(SPTSlot 1)a b old HH eq_refl eq_refl HO).
   + exact(source_binary_prop_graph M _ h(SPTSlot 0)(SPTSlot 2)a e new HH eq_refl eq_refl HN).
Qed.
Theorem source_zfr_map_quantifier M h a b qa qb k:
 sf_unary h ->source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
 sf_relation M h a(zeroM M)qa ->sf_relation M h b(zeroM M)qb ->source_zfr_map M a b ->source_zfr_map M qa qb.
Proof.
 intros HH BA BB HQA HQB IH law HL.
 destruct(sf_relation_total M SFImpl a b)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(qpoint&HQP).
 destruct(sf_relation_total M SFImpl qpoint law)as(dist&HDist).
 assert(PQ:source_descriptor_provable M ZFRSourceDescriptor qpoint).
 { exact(source_descriptor_provable_all M ZFRSourceDescriptor point qpoint(proj2(source_zfr_descriptor_provable M point)(IH point HP))HQP). }
 assert(PDist:source_descriptor_provable M ZFRSourceDescriptor dist).
 { apply source_descriptor_provable_from_empty. destruct HH as[EH|EH];subst h.
   - exact(source_universal_distribution M a b point qa qb qpoint law dist(succM M k)BA BB HP HQA HQB HQP HL HDist).
   - exact(source_existential_distribution M a b point qa qb qpoint law dist k BA BB HP HQA HQB HQP HL HDist). }
 exact(proj1(source_zfr_descriptor_provable M law)(source_descriptor_provable_mp M ZFRSourceDescriptor qpoint law dist PQ PDist HDist)).
Qed.
Theorem source_zfr_map_from_false M phi k:source_bounded M phi k ->source_zfr_map M(zeroM M)phi.
Proof.
 intros BP law HL. refine(source_zfr_prop_zero M(SPTImpl SPTFalse(SPTSlot 0))_ (fun _=>phi)k law _ _).
 - apply SPTII,SPTExp,SPTCtx. now left.
 - intro i. exact BP.
 - exact(source_prop_template_join M(fun _=>phi)SFImpl SPTFalse(SPTSlot 0)(zeroM M)phi law eq_refl eq_refl HL).
Qed.
Print Assumptions source_zfr_map_right.
Print Assumptions source_zfr_map_quantifier.
Print Assumptions source_zfr_map_from_false.
