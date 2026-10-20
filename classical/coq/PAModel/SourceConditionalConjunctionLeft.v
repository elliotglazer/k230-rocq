(** A positive conjunction map retaining an ordinary outer condition. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourceConditionalProofs SourceWitnessProofComposition
 SourcePropositionalTemplates SourcePropositionalRebase SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_conditional_and_left M condition a b d old new k:
 source_bounded M condition k ->source_bounded M a k ->source_bounded M b k ->source_bounded M d k ->
 sf_relation M SFAnd a d old ->sf_relation M SFAnd b d new ->source_conditional_implies M condition a b ->source_conditional_implies M condition old new.
Proof.
 intros BC BA BB BD HO HN IH point HP law HL.
 destruct(sf_relation_total M SFImpl a b)as(ab&HAB).
 destruct(sf_relation_total M SFImpl condition ab)as(input&HInput).
 refine(source_zfr_prop_one M(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)))
  (SPTImpl(SPTSlot 0)(SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTAnd(SPTSlot 2)(SPTSlot 3))))_
  (code_parameters condition a b d)k input law _ _ _ (IH ab HAB input HInput)).
 - apply SPTII,SPTII,SPTCI.
   + apply(SPTIE _ (SPTSlot 1)(SPTSlot 2)).
     * apply(SPTIE _ (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)));apply SPTCtx;cbn;tauto.
     * apply(SPTCE1 _ (SPTSlot 1)(SPTSlot 3)),SPTCtx;cbn;tauto.
   + apply(SPTCE2 _ (SPTSlot 1)(SPTSlot 3)),SPTCtx;cbn;tauto.
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M(code_parameters condition a b d)SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))condition ab input eq_refl
   (source_prop_template_join M _ SFImpl(SPTSlot 1)(SPTSlot 2)a b ab eq_refl eq_refl HAB)HInput).
 - refine(source_prop_template_join M(code_parameters condition a b d)SFImpl(SPTSlot 0)(SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTAnd(SPTSlot 2)(SPTSlot 3)))condition point law eq_refl _ HL).
   refine(source_prop_template_join M(code_parameters condition a b d)SFImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTAnd(SPTSlot 2)(SPTSlot 3))old new point _ _ HP).
   + exact(source_prop_template_join M _ SFAnd(SPTSlot 1)(SPTSlot 3)a d old eq_refl eq_refl HO).
   + exact(source_prop_template_join M _ SFAnd(SPTSlot 2)(SPTSlot 3)b d new eq_refl eq_refl HN).
Qed.
Print Assumptions source_conditional_and_left.
