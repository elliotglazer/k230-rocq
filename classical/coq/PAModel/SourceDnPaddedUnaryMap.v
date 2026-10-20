(** Actual implication transport through internally many Dn binders with
    an exterior padded condition. It reuses the checked arbitrary-count
    introduction and distribution engines. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourceDn SourceDnBounds
 SourceRepresentationPadding SourceRepresentationPaddedDn SourceDnPaddedBinaryMap
 SourceDescriptorProvability SourceDescriptorPrograms SourcePropositionalTemplates SourceEnvironmentCarrierClosure.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_descriptor_dn_padded_map M T count condition padded a b da db point proof inner result k:
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M a(addM M count(succM M(succM M k))) ->
 source_bounded M b(addM M count(succM M(succM M k))) ->
 source_representation_padding M count condition padded ->
 source_dn M count a da ->source_dn M count b db ->
 sf_relation M SFImpl a b point ->sf_relation M SFImpl padded point proof ->
 sf_relation M SFImpl da db inner ->sf_relation M SFImpl condition inner result ->
 source_descriptor_provable M T proof ->source_descriptor_provable M T result.
Proof.
 intros BC BA BB HPad HDA HDB HP HProof HInner HResult PProof.
 pose proof(source_dn_bounded M count a da k HDA BA)as BDA.
 pose proof(source_dn_bounded M count b db k HDB BB)as BDB.
 assert(BPoint:source_bounded M point(addM M count(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl a b point _(or_intror(or_intror eq_refl))HP)(conj BA BB)). }
 destruct(source_dn_total M count point)as(dpoint&HDPoint).
 pose proof(source_dn_bounded M count point dpoint k HDPoint BPoint)as BDP.
 destruct(sf_relation_total M SFImpl condition dpoint)as(first&HFirst).
 pose proof(source_descriptor_dn_padded_intro M T count condition padded point dpoint k proof first
  BC BPoint HPad HDPoint HProof HFirst PProof)as PFirst.
 destruct(sf_relation_total M SFImpl dpoint inner)as(second&HSecond).
 pose proof(source_descriptor_dn_distribution M T count a b point da db dpoint inner second k
  BA BB HP HDA HDB HDPoint HInner HSecond)as PSecond.
 assert(BInner:source_bounded M inner(succM M(succM M k))).
 { exact(proj2(source_bounded_accept_binary M SFImpl da db inner _(or_intror(or_intror eq_refl))HInner)(conj BDA BDB)). }
 set(rho:=fun i=>match i with 0=>condition|1=>dpoint|_=>inner end).
 assert(P:source_prop_program[SPTImpl(SPTSlot 0)(SPTSlot 1);SPTImpl(SPTSlot 1)(SPTSlot 2)]
  (SPTImpl(SPTSlot 0)(SPTSlot 2))).
 { apply SPTII. eapply SPTIE with(a:=SPTSlot 1);[apply SPTCtx;cbn;auto 8|].
   eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto 8. }
 assert(GFirst:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 0)(SPTSlot 1)))first).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HFirst]. }
 assert(GSecond:code_relation M rho(source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2)))second).
 { eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HSecond]. }
 apply(source_descriptor_prop_program M T _ _ P rho(succM M(succM M k))result).
 - intros[|[|i]];cbn[rho];assumption.
 - intros p[<-|[<-|[]]]f HF.
   + rewrite(code_relation_functional M _ rho f first HF GFirst). exact PFirst.
   + rewrite(code_relation_functional M _ rho f second HF GSecond). exact PSecond.
 - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HResult].
Qed.
Print Assumptions source_descriptor_dn_padded_map.
