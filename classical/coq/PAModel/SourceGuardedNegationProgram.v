(** The actual classical source deduction not(G implies A) iff G and not A. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourcePropositionalTemplates SourceFunctionalityShells SetSchemaConstructors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition guarded_negation_left:=SPTImpl(SPTImpl(SPTSlot 0)(SPTSlot 1))SPTFalse.
Definition guarded_negation_right:=SPTAnd(SPTSlot 0)(SPTImpl(SPTSlot 1)SPTFalse).
Ltac guarded_negation_ctx:=apply SPTCtx;cbn;tauto.
Lemma guarded_negation_to_pair_program:source_prop_program[]
  (SPTImpl guarded_negation_left guarded_negation_right).
Proof.
  unfold guarded_negation_left,guarded_negation_right. apply SPTII,SPTCI.
  - eapply SPTIE;[exact(SPTPc _(SPTSlot 0)SPTFalse)|].
    apply SPTII,SPTExp. eapply(SPTIE _(SPTImpl(SPTSlot 0)(SPTSlot 1))SPTFalse).
    + guarded_negation_ctx.
    + apply SPTII,SPTExp. eapply(SPTIE _(SPTSlot 0)SPTFalse);guarded_negation_ctx.
  - apply SPTII. eapply(SPTIE _(SPTImpl(SPTSlot 0)(SPTSlot 1))SPTFalse).
    + guarded_negation_ctx.
    + apply SPTII. guarded_negation_ctx.
Qed.
Lemma guarded_pair_to_negation_program:source_prop_program[]
  (SPTImpl guarded_negation_right guarded_negation_left).
Proof.
  unfold guarded_negation_left,guarded_negation_right. do 2 apply SPTII.
  eapply(SPTIE _(SPTSlot 1)SPTFalse).
  - apply(SPTCE2 _(SPTSlot 0)). guarded_negation_ctx.
  - eapply(SPTIE _(SPTSlot 0)(SPTSlot 1));[guarded_negation_ctx|].
    apply(SPTCE1 _ _(SPTImpl(SPTSlot 1)SPTFalse)). guarded_negation_ctx.
Qed.

Theorem source_guarded_negation_empty M(reverse:bool)guard a implication negImp negA both law k:
  source_bounded M guard k ->source_bounded M a k ->
  sf_relation M SFImpl guard a implication ->sf_relation M SFImpl implication(zeroM M)negImp ->
  sf_relation M SFImpl a(zeroM M)negA ->sf_relation M SFAnd guard negA both ->
  sf_relation M SFImpl(if reverse then both else negImp)(if reverse then negImp else both)law ->
  source_full_prv M(zeroM M)(zeroM M)(zeroM M)law.
Proof.
  intros BG BA HI HNI HNA HB HL.
  assert(BEnv:forall i,source_bounded M(schema_env3 guard a(zeroM M)i)k).
  { intros[|[|i]];cbn[schema_env3];try assumption;apply source_bounded_accept_falsity. }
  assert(P:source_prop_program[](if reverse then SPTImpl guarded_negation_right guarded_negation_left
    else SPTImpl guarded_negation_left guarded_negation_right)).
  { destruct reverse;[apply guarded_pair_to_negation_program|apply guarded_negation_to_pair_program]. }
  apply(source_prop_program_sound M _ _ P(schema_env3 guard a(zeroM M))k(zeroM M)(zeroM M)(zeroM M)law
    BEnv(context_bounded_empty M(zeroM M)(zeroM M)k)).
  - intros p H f HF. contradiction.
  - destruct reverse;unfold guarded_negation_left,guarded_negation_right,source_prop_expression;functionality_graph.
Qed.
Print Assumptions guarded_negation_to_pair_program.
Print Assumptions guarded_pair_to_negation_program.
Print Assumptions source_guarded_negation_empty.
