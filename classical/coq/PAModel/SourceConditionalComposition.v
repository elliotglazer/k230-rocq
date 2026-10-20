(** Composition of conditional source certificates. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceConditionalProofs SourceConditionalQuantifiers SourceWitnessProofComposition
 SourcePropositionalTemplates SourcePropositionalRebase SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_conditional_fact_consequence M condition a b imp k:
 source_bounded M condition k ->source_bounded M a k ->source_bounded M b k ->
 sf_relation M SFImpl a b imp ->source_zfr_provable M imp ->
 source_conditional_fact M condition a ->source_conditional_fact M condition b.
Proof.
 intros HC HA HB HI PI PA out HO.
 destruct(sf_relation_total M SFImpl condition a)as(first&HFirst).
 refine(source_zfr_prop_two M (SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 1)(SPTSlot 2))
  (SPTImpl(SPTSlot 0)(SPTSlot 2))(source_conditional_trans_program(SPTSlot 0)(SPTSlot 1)(SPTSlot 2))
  (code_parameters condition a b b)k first imp out _ _ _ _ (PA first HFirst)PI).
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 0)(SPTSlot 1)condition a first eq_refl eq_refl HFirst).
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 1)(SPTSlot 2)a b imp eq_refl eq_refl HI).
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 0)(SPTSlot 2)condition b out eq_refl eq_refl HO).
Qed.

Lemma source_conditional_two_trans_program C A B D:
 source_prop_program[SPTImpl C(SPTImpl A B);SPTImpl C(SPTImpl B D)]
  (SPTImpl C(SPTImpl A D)).
Proof.
 apply SPTII,SPTII. apply(SPTIE _ B D).
 - apply(SPTIE _ C(SPTImpl B D));apply SPTCtx;cbn;tauto.
 - apply(SPTIE _ A B).
   + apply(SPTIE _ C(SPTImpl A B));apply SPTCtx;cbn;tauto.
   + apply SPTCtx;cbn;tauto.
Qed.
Theorem source_conditional_implies_trans M condition a b d k:
 source_bounded M condition k ->source_bounded M a k ->source_bounded M b k ->source_bounded M d k ->
 source_conditional_implies M condition a b ->source_conditional_implies M condition b d ->
 source_conditional_implies M condition a d.
Proof.
 intros HC HA HB HD PAB PBD point HP out HO.
 destruct(sf_relation_total M SFImpl a b)as(ab&HAB).
 destruct(sf_relation_total M SFImpl condition ab)as(first&HFirst).
 destruct(sf_relation_total M SFImpl b d)as(bd&HBD).
 destruct(sf_relation_total M SFImpl condition bd)as(second&HSecond).
 refine(source_zfr_prop_two M (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))
  (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3)))
  (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)))
  (source_conditional_two_trans_program(SPTSlot 0)(SPTSlot 1)(SPTSlot 2)(SPTSlot 3))
  (code_parameters condition a b d)k first second out _ _ _ _ (PAB ab HAB first HFirst)(PBD bd HBD second HSecond)).
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))condition ab first eq_refl
   (source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 1)(SPTSlot 2)a b ab eq_refl eq_refl HAB)HFirst).
 - exact(source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3))condition bd second eq_refl
   (source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 2)(SPTSlot 3)b d bd eq_refl eq_refl HBD)HSecond).
 - exact(source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))condition point out eq_refl
   (source_prop_template_join M (code_parameters condition a b d) SFImpl(SPTSlot 1)(SPTSlot 3)a d point eq_refl eq_refl HP)HO).
Qed.
Print Assumptions source_conditional_fact_consequence.
Print Assumptions source_conditional_implies_trans.
