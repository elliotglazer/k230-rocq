(** Obtain the negative child equivalence needed by universal TV from the
    actual positive child equivalence; it is not an extra induction premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourcePropositionalTemplates SourceFunctionalityShells SetSchemaConstructors
  SourceIffGraphs SourceEmptyUniversalMap.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition tv_negative_old:=SPTImpl(SPTSlot 0)
  (SPTAnd(SPTImpl(SPTSlot 1)(SPTSlot 2))(SPTImpl(SPTSlot 2)(SPTSlot 1))).
Definition tv_negative_new:=SPTImpl(SPTSlot 0)
  (SPTAnd(SPTImpl(SPTImpl(SPTSlot 1)SPTFalse)(SPTImpl(SPTSlot 2)SPTFalse))
    (SPTImpl(SPTImpl(SPTSlot 2)SPTFalse)(SPTImpl(SPTSlot 1)SPTFalse))).
Ltac tv_negative_ctx:=apply SPTCtx;cbn;tauto.
Lemma tv_negative_program:source_prop_program[](SPTImpl tv_negative_old tv_negative_new).
Proof.
  unfold tv_negative_old,tv_negative_new. do 2 apply SPTII. apply SPTCI.
  - do 2 apply SPTII. eapply(SPTIE _(SPTSlot 1)SPTFalse);[tv_negative_ctx|].
    eapply(SPTIE _(SPTSlot 2)(SPTSlot 1));[|tv_negative_ctx].
    apply(SPTCE2 _(SPTImpl(SPTSlot 1)(SPTSlot 2))).
    eapply(SPTIE _(SPTSlot 0));tv_negative_ctx.
  - do 2 apply SPTII. eapply(SPTIE _(SPTSlot 2)SPTFalse);[tv_negative_ctx|].
    eapply(SPTIE _(SPTSlot 1)(SPTSlot 2));[|tv_negative_ctx].
    apply(SPTCE1 _ _(SPTImpl(SPTSlot 2)(SPTSlot 1))).
    eapply(SPTIE _(SPTSlot 0));tv_negative_ctx.
Qed.

Theorem source_full_guarded_negated_equivalence M cb cc cn guard a b equiv point all negA negB equivNeg pointNeg allNeg k:
  context_bounded M cb cc cn k ->source_bounded M guard(succM M k) ->source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl guard equiv point ->sf_relation M SFAll point(zeroM M)all ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFImpl b(zeroM M)negB ->
  source_iff_graph M negA negB equivNeg ->sf_relation M SFImpl guard equivNeg pointNeg ->sf_relation M SFAll pointNeg(zeroM M)allNeg ->
  source_full_prv M cb cc cn all ->source_full_prv M cb cc cn allNeg.
Proof.
  intros BC BG BA BB HI HP HQ HNA HNB HNI HNP HNQ PA.
  pose proof(source_iff_bounded M a b equiv(succM M k)BA BB HI)as BE.
  pose proof(proj2(source_bounded_accept_binary M SFImpl guard equiv point(succM M k)
    (or_intror(or_intror eq_refl))HP)(conj BG BE))as BP.
  pose proof(proj2(source_bounded_accept_binary M SFImpl a(zeroM M)negA(succM M k)(or_intror(or_intror eq_refl))HNA)
    (conj BA(source_bounded_accept_falsity M(succM M k))))as BNA.
  pose proof(proj2(source_bounded_accept_binary M SFImpl b(zeroM M)negB(succM M k)(or_intror(or_intror eq_refl))HNB)
    (conj BB(source_bounded_accept_falsity M(succM M k))))as BNB.
  pose proof(source_iff_bounded M negA negB equivNeg(succM M k)BNA BNB HNI)as BNE.
  pose proof(proj2(source_bounded_accept_binary M SFImpl guard equivNeg pointNeg(succM M k)
    (or_intror(or_intror eq_refl))HNP)(conj BG BNE))as BNP.
  destruct(sf_relation_total M SFImpl point pointNeg)as(law&HLaw).
  assert(PLaw:source_full_prv M(zeroM M)(zeroM M)(zeroM M)law).
  { assert(BEnv:forall i,source_bounded M(schema_env3 guard a b i)(succM M k)).
    { intros[|[|i]];cbn[schema_env3];assumption. }
    apply(source_prop_program_sound M _ _ tv_negative_program(schema_env3 guard a b)(succM M k)
      (zeroM M)(zeroM M)(zeroM M)law BEnv(context_bounded_empty M(zeroM M)(zeroM M)(succM M k))).
    - intros p H f HF. contradiction.
    - destruct(source_iff_parts M a b equiv HI)as(ab&ba&HAB&HBA&HAnd).
      destruct(source_iff_parts M negA negB equivNeg HNI)as(nab&nba&HNAB&HNBA&HNAnd).
      unfold tv_negative_old,tv_negative_new,source_prop_expression. functionality_graph. }
  exact(source_full_all_map_from_empty M cb cc cn point pointNeg all allNeg law k BC BP BNP HQ HNQ HLaw PLaw PA).
Qed.
Print Assumptions tv_negative_program.
Print Assumptions source_full_guarded_negated_equivalence.
