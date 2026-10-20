(** Change the guard of an existential using an actual universally
    quantified guard implication in the same context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
  SourceRelativizationRules SourceConjunctionRules SourceDerivedRules SourceQuantifierRules
  SourceUniversalPropositional SourceContextProofHelpers SourceExistentialMap.
Unset Implicit Arguments.
Theorem source_full_guarded_exists_guard_map M cb cc cn guard guard' a point all old new k:
  context_bounded M cb cc cn k ->source_bounded M guard(succM M k) ->
  source_bounded M guard'(succM M k) ->source_bounded M a(succM M k) ->
  sf_relation M SFImpl guard guard' point ->sf_relation M SFAll point(zeroM M)all ->
  sr_quantifier M false guard a old ->sr_quantifier M false guard' a new ->
  source_full_prv M cb cc cn all ->source_full_prv M cb cc cn old ->source_full_prv M cb cc cn new.
Proof.
  intros BC BG BG' BA HP HAll(body&HB&HOld)(body'&HB'&HNew)PAll POld.
  pose proof(proj2(source_bounded_accept_binary M SFAnd guard a body(succM M k)(or_introl eq_refl)HB)(conj BG BA))as BOldBody.
  pose proof(proj2(source_bounded_accept_binary M SFAnd guard' a body'(succM M k)(or_introl eq_refl)HB')(conj BG' BA))as BNewBody.
  pose proof(proj2(source_bounded_accept_unary M SFEx body' new k(or_intror eq_refl)HNew)BNewBody)as BNew.
  destruct(context_shift_total M cb cc cn)as(sb&sc&HShift).
  pose proof(source_full_all_shift M cb cc cn point all sb sc HAll PAll HShift)as PPointS.
  destruct(environment_cons_total M sb sc cn body)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M sb sc cn body ub uc un(succM M k)HCons)
    (conj BOldBody(context_shift_preserves_bound M cb cc cn sb sc k HShift BC)))as BU.
  pose proof(source_full_cons_head M sb sc cn body ub uc un(succM M k)HCons BOldBody BU)as PBody.
  pose proof(source_full_conjunction_left M ub uc un guard a body HB PBody)as PG.
  pose proof(source_full_conjunction_right M ub uc un guard a body HB PBody)as PA.
  pose proof(source_full_cons_weaken M sb sc cn body ub uc un(succM M k)point HCons BU PPointS)as PPoint.
  pose proof(source_full_modus_ponens M ub uc un guard guard' point HP PPoint PG)as PG'.
  pose proof(full_source_CI M ub uc un guard' a body'(ex_intro _ (succM M k)(conj BNewBody BU))PG' PA HB')as PNewBody.
  destruct(numerical_renaming_total M new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
  exact(source_full_exists_map M cb cc cn body body' old new sb sc ub uc un shifted
    (ex_intro _ k(conj BNew BC))HOld HNew HShift HCons HS POld PNewBody).
Qed.
Print Assumptions source_full_guarded_exists_guard_map.
