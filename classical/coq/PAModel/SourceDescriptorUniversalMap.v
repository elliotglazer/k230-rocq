(** Pure logical implication congruence for descriptor provability. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceDescriptorProvability SourceDescriptorClosure SourceUniversalDistribution
  SourcePropositionalTemplates SourceDescriptorPrograms SchemaConstructorBounds.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_descriptor_universal_map M T a b implication qa qb out k :
  source_bounded M a k ->source_bounded M b k ->
  sf_relation M SFImpl a b implication ->sf_relation M SFAll a (zeroM M) qa ->
  sf_relation M SFAll b (zeroM M) qb ->sf_relation M SFImpl qa qb out ->
  source_descriptor_provable M T implication ->source_descriptor_provable M T out.
Proof.
  intros HA HB HI HQA HQB HO PI.
  destruct(sf_relation_total M SFAll implication (zeroM M)) as (qimp&HQI).
  destruct(sf_relation_total M SFImpl qimp out) as (distribution&HD).
  pose proof(source_descriptor_provable_all M T implication qimp PI HQI) as PQI.
  pose proof(source_descriptor_provable_from_empty M T distribution
    (source_universal_distribution M a b implication qa qb qimp out distribution k HA HB HI HQA HQB HQI HO HD)) as PD.
  exact(source_descriptor_provable_mp M T qimp out distribution PQI PD HD).
Qed.

Theorem source_descriptor_implication_guard M T guard a b implication ga gb out k :
  source_bounded M guard k ->source_bounded M a k ->source_bounded M b k ->
  sf_relation M SFImpl a b implication ->sf_relation M SFImpl guard a ga ->
  sf_relation M SFImpl guard b gb ->sf_relation M SFImpl ga gb out ->
  source_descriptor_provable M T implication ->source_descriptor_provable M T out.
Proof.
  intros HG HA HB HI HGA HGB HO PI.
  set(rho:=fun i=>match i with 0=>guard|1=>a|_=>b end).
  assert(HP:source_prop_program [SPTImpl(SPTSlot 1)(SPTSlot 2)]
    (SPTImpl(SPTImpl(SPTSlot 0)(SPTSlot 1))(SPTImpl(SPTSlot 0)(SPTSlot 2)))).
  { apply SPTII,SPTII. eapply SPTIE.
    - apply SPTCtx. cbn. auto.
    - eapply SPTIE;apply SPTCtx;cbn;auto. }
  apply(source_descriptor_prop_program M T _ _ HP rho k out).
  - intros [|[|i]];cbn [rho];assumption.
  - intros p [<-|[]] f HF.
    assert(HI':code_relation M rho (source_prop_expression(SPTImpl(SPTSlot 1)(SPTSlot 2))) implication).
    { exact(proj2(schema_expression_graph M rho SFImpl (CEvar 1)(CEvar 2) a b implication eq_refl eq_refl) HI). }
    rewrite(code_relation_functional M _ rho f implication HF HI'). exact PI.
  - assert(HGA':code_relation M rho (E_sf SFImpl (CEvar 0)(CEvar 1)) ga).
    { exact(proj2(schema_expression_graph M rho SFImpl (CEvar 0)(CEvar 1) guard a ga eq_refl eq_refl) HGA). }
    assert(HGB':code_relation M rho (E_sf SFImpl (CEvar 0)(CEvar 2)) gb).
    { exact(proj2(schema_expression_graph M rho SFImpl (CEvar 0)(CEvar 2) guard b gb eq_refl eq_refl) HGB). }
    exact(proj2(schema_expression_graph M rho SFImpl _ _ ga gb out HGA' HGB') HO).
Qed.

Print Assumptions source_descriptor_universal_map.
Print Assumptions source_descriptor_implication_guard.
