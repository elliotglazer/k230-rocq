(** Transform bounded existential witnesses using an actual universally
    guarded equivalence in the same ordinary source context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
  SourceRelativizationRules SourceConjunctionRules SourceIffGraphs SourceDerivedRules SourceQuantifierRules
  SourceUniversalPropositional SourceContextProofHelpers SourceExistentialMap.
Unset Implicit Arguments.

Theorem source_full_guarded_exists_congruence M cb cc cn(reverse:bool)guard a b equiv point all old new k:
  context_bounded M cb cc cn k ->source_bounded M guard(succM M k) ->
  source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  source_iff_graph M a b equiv ->sf_relation M SFImpl guard equiv point ->
  sf_relation M SFAll point(zeroM M)all ->
  sr_quantifier M false guard(if reverse then b else a)old ->
  sr_quantifier M false guard(if reverse then a else b)new ->
  source_full_prv M cb cc cn all ->source_full_prv M cb cc cn old ->
  source_full_prv M cb cc cn new.
Proof.
  intros BC BG BA BB HI HP HAll(body&HB&HOld)(body'&HB'&HNew)PAll POld.
  assert(BOldBody:source_bounded M body(succM M k)).
  { apply(proj2(source_bounded_accept_binary M SFAnd guard(if reverse then b else a)body(succM M k)(or_introl eq_refl)HB)).
    split;[exact BG|destruct reverse;assumption]. }
  assert(BNewBody:source_bounded M body'(succM M k)).
  { apply(proj2(source_bounded_accept_binary M SFAnd guard(if reverse then a else b)body'(succM M k)(or_introl eq_refl)HB')).
    split;[exact BG|destruct reverse;assumption]. }
  pose proof(proj2(source_bounded_accept_unary M SFEx body' new k(or_intror eq_refl)HNew)BNewBody)as BNew.
  destruct(context_shift_total M cb cc cn)as(sb&sc&HShift).
  pose proof(source_full_all_shift M cb cc cn point all sb sc HAll PAll HShift)as PPointS.
  destruct(environment_cons_total M sb sc cn body)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M sb sc cn body ub uc un(succM M k)HCons)
    (conj BOldBody(context_shift_preserves_bound M cb cc cn sb sc k HShift BC)))as BU.
  pose proof(source_full_cons_head M sb sc cn body ub uc un(succM M k)HCons BOldBody BU)as PBody.
  pose proof(source_full_conjunction_left M ub uc un guard _ body HB PBody)as PG.
  pose proof(source_full_conjunction_right M ub uc un guard _ body HB PBody)as PMatrix.
  pose proof(source_full_cons_weaken M sb sc cn body ub uc un(succM M k)point HCons BU PPointS)as PPoint.
  pose proof(source_full_modus_ponens M ub uc un guard equiv point HP PPoint PG)as PEquiv.
  destruct(source_iff_parts M a b equiv HI)as(forward&backward&HF&HR&HBoth).
  assert(PMatrixNew:source_full_prv M ub uc un(if reverse then a else b)).
  { destruct reverse.
    - exact(source_full_modus_ponens M ub uc un b a backward HR
        (source_full_conjunction_right M ub uc un forward backward equiv HBoth PEquiv)PMatrix).
    - exact(source_full_modus_ponens M ub uc un a b forward HF
        (source_full_conjunction_left M ub uc un forward backward equiv HBoth PEquiv)PMatrix). }
  pose proof(full_source_CI M ub uc un guard _ body'(ex_intro _ (succM M k)(conj BNewBody BU))PG PMatrixNew HB')as PNewBody.
  destruct(numerical_renaming_total M new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
  exact(source_full_exists_map M cb cc cn body body' old new sb sc ub uc un shifted
    (ex_intro _ k(conj BNew BC))HOld HNew HShift HCons HS POld PNewBody).
Qed.
Print Assumptions source_full_guarded_exists_congruence.
