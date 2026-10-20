(** Lift a genuine empty-context matrix implication through Ex, including
    its contravariant use under negation. No quantifier equivalence is assumed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
  SourceProofWeakening SourceContextProofHelpers SourceQuantifierRules SourceDerivedRules SourceExistentialMap.
Unset Implicit Arguments.
Theorem source_full_exists_map_from_empty M cb cc cn a b exa exb point k:
  context_bounded M cb cc cn k ->source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFEx a(zeroM M)exa ->sf_relation M SFEx b(zeroM M)exb ->sf_relation M SFImpl a b point ->
  source_full_prv M(zeroM M)(zeroM M)(zeroM M)point ->source_full_prv M cb cc cn exa ->
  source_full_prv M cb cc cn exb.
Proof.
  intros BC BA BB HA HB HP PP PEx.
  pose proof(proj2(source_bounded_accept_unary M SFEx b exb k(or_intror eq_refl)HB)BB)as BEx.
  destruct(context_shift_total M cb cc cn)as(sb&sc&HShift).
  destruct(environment_cons_total M sb sc cn a)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M sb sc cn a ub uc un(succM M k)HCons)
    (conj BA(context_shift_preserves_bound M cb cc cn sb sc k HShift BC)))as BU.
  assert(PPoint:source_full_prv M ub uc un point).
  { apply(source_full_prv_weaken_bounded M(zeroM M)(zeroM M)(zeroM M)ub uc un point(succM M k)PP);
      [intros f H;exfalso;exact(context_empty M(zeroM M)(zeroM M)f H)|exact BU]. }
  pose proof(source_full_cons_head M sb sc cn a ub uc un(succM M k)HCons BA BU)as PA.
  pose proof(source_full_modus_ponens M ub uc un a b point HP PPoint PA)as PB.
  destruct(numerical_renaming_total M exb(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
  exact(source_full_exists_map M cb cc cn a b exa exb sb sc ub uc un shifted
    (ex_intro _ k(conj BEx BC))HA HB HShift HCons HS PEx PB).
Qed.

Theorem source_full_not_exists_contravariant_from_empty M cb cc cn a b exa exb point notA notB k:
  context_bounded M cb cc cn k ->source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFEx a(zeroM M)exa ->sf_relation M SFEx b(zeroM M)exb ->sf_relation M SFImpl a b point ->
  sf_relation M SFImpl exa(zeroM M)notA ->sf_relation M SFImpl exb(zeroM M)notB ->
  source_full_prv M(zeroM M)(zeroM M)(zeroM M)point ->source_full_prv M cb cc cn notB ->
  source_full_prv M cb cc cn notA.
Proof.
  intros BC BA BB HA HB HP HNA HNB PP PN.
  pose proof(proj2(source_bounded_accept_unary M SFEx a exa k(or_intror eq_refl)HA)BA)as BExA.
  pose proof(proj2(source_bounded_accept_binary M SFImpl exa(zeroM M)notA k
    (or_intror(or_intror eq_refl))HNA)(conj BExA(source_bounded_accept_falsity M k)))as BNotA.
  destruct(environment_cons_total M cb cc cn exa)as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M cb cc cn exa ub uc un k HCons)(conj BExA BC))as BU.
  pose proof(source_full_cons_head M cb cc cn exa ub uc un k HCons BExA BU)as PExA.
  pose proof(source_full_exists_map_from_empty M ub uc un a b exa exb point k BU BA BB HA HB HP PP PExA)as PExB.
  pose proof(source_full_cons_weaken M cb cc cn exa ub uc un k notB HCons BU PN)as PNotB.
  pose proof(source_full_modus_ponens M ub uc un exb(zeroM M)notB HNB PNotB PExB)as PFalse.
  exact(full_source_II M cb cc cn exa(zeroM M)notA ub uc un(ex_intro _ k(conj BNotA BC))PFalse HCons HNA).
Qed.
Print Assumptions source_full_exists_map_from_empty.
Print Assumptions source_full_not_exists_contravariant_from_empty.
