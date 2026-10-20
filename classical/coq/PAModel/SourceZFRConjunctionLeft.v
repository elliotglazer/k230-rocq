From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourceZFRPositiveMaps SourceConditionalProofs
 SourceWitnessProofComposition SourcePropositionalTemplates SourcePropositionalRebase.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_map_and_left M a b c old new k:
 source_bounded M a k ->source_bounded M b k ->source_bounded M c k ->sf_relation M SFAnd a c old ->sf_relation M SFAnd b c new ->
 source_zfr_map M a b ->source_zfr_map M old new.
Proof.
 intros BA BB BC HO HN IH law HL.
 destruct(sf_relation_total M SFImpl a b)as(point&HP).
 refine(source_zfr_prop_one M(SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTAnd(SPTSlot 1)(SPTSlot 2)))_
  (code_parameters a b c c)k point law _ _ _ (IH point HP)).
 - apply SPTII,SPTCI.
   + apply(SPTIE _ (SPTSlot 0)(SPTSlot 1));[apply SPTCtx;cbn;tauto|apply(SPTCE1 _ (SPTSlot 0)(SPTSlot 2)),SPTCtx;cbn;tauto].
   + apply(SPTCE2 _ (SPTSlot 0)(SPTSlot 2)),SPTCtx;cbn;tauto.
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 0)(SPTSlot 1)a b point eq_refl eq_refl HP).
 - refine(source_prop_template_join M(code_parameters a b c c)SFImpl(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTAnd(SPTSlot 1)(SPTSlot 2))old new law _ _ HL).
   + exact(source_prop_template_join M _ SFAnd(SPTSlot 0)(SPTSlot 2)a c old eq_refl eq_refl HO).
   + exact(source_prop_template_join M _ SFAnd(SPTSlot 1)(SPTSlot 2)b c new eq_refl eq_refl HN).
Qed.
Print Assumptions source_zfr_map_and_left.
