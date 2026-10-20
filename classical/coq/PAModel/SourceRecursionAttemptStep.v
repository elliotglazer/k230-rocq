(** The actual attempt-successor accessor for a nonstandard binary matrix.
    All three universal eliminations use a checked simultaneous prefix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalSourceFull SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionBinaryInstance
  SourceRecursionAttemptStepShell SourceRecursionAttemptSpecialization SourceTripleSpecialization SourcePieceBoundMaxJoint
  SourceDerivedRules SourceTraceBounds SourceFiniteCutoffShift.
Unset Implicit Arguments.

Theorem source_full_rec_attempt_step M b c l phi o a N f att u u' v' member successor app result:
  source_bounded M phi(code_numeral M 2) ->source_rec_attempt M phi o a N f att ->
  sf_relation M SFMember u N member ->source_rec_successor M u u' successor ->source_rec_app M f u' v' app ->
  source_rec_transition_witness M phi f u v' result ->source_full_prv M b c l att ->
  source_full_prv M b c l member ->source_full_prv M b c l successor ->source_full_prv M b c l app ->
  source_full_prv M b c l result.
Proof.
  intros HB(first&second&HFirst&HSecond&HAtt)HM HS HApp HResult PAtt PM PS PA.
  destruct(source_full_piece_conjunction_components M b c l first second att HAtt PAtt) as[PFirst PSecond].
  destruct(source_rec_attempt_step_shell M phi N f second HSecond)
    as(guard&rawSuccessor&appOut&appIn&body&ex&t3&t2&point&one&two&HG&HRawS&HO&HI&HBody&HEx&H3&H2&HPoint&HOne&HTwo&HOuter).
  destruct(source_triple_prefix_total M v' u' u) as(tb&tc&HPrefix).
  destruct(sf_relation_total M SFImpl app result) as(r3&HR3).
  destruct(sf_relation_total M SFImpl successor r3) as(r2&HR2).
  destruct(sf_relation_total M SFImpl member r2) as(target&HTarget).
  pose proof(source_rec_attempt_point_substitution M phi N f guard rawSuccessor appOut appIn body ex t3 t2 point
    u u' v' tb tc member successor app result r3 r2 target HB HG HRawS HO HI HBody HEx H3 H2 HPoint HPrefix HM HS HApp HResult HR3 HR2 HTarget) as HSub.
  destruct(source_full_prv_wellformed M b c l second PSecond) as(k&BSecond&HContext).
  pose proof(proj1(source_bounded_accept_unary M SFAll two second k(or_introl eq_refl)HOuter)BSecond) as BTwo.
  pose proof(proj1(source_bounded_accept_unary M SFAll one two(succM M k)(or_introl eq_refl)HTwo)BTwo) as BOne.
  pose proof(proj1(source_bounded_accept_unary M SFAll point one(succM M(succM M k))(or_introl eq_refl)HOne)BOne) as BPoint.
  pose proof(source_full_triple_specialize M b c l point one two second u u' v' tb tc target
    (source_succ_iter M 3 k)BPoint HOne HTwo HOuter HPrefix HSub PSecond) as PTarget.
  pose proof(source_full_modus_ponens M b c l member r2 target HTarget PTarget PM) as PR2.
  pose proof(source_full_modus_ponens M b c l successor r3 r2 HR2 PR2 PS) as PR3.
  exact(source_full_modus_ponens M b c l app result r3 HR3 PR3 PA).
Qed.

Print Assumptions source_full_rec_attempt_step.
