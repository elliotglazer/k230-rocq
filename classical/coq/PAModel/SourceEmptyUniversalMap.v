(** Lift an actual empty-context implication through a universal binder. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes SourceBounded
  NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofWeakening SourceUniversalPropositional.
Unset Implicit Arguments.
Theorem source_full_all_map_from_empty M cb cc cn a b alla allb point k:
  context_bounded M cb cc cn k ->source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
  sf_relation M SFAll a(zeroM M)alla ->sf_relation M SFAll b(zeroM M)allb ->sf_relation M SFImpl a b point ->
  source_full_prv M(zeroM M)(zeroM M)(zeroM M)point ->source_full_prv M cb cc cn alla ->source_full_prv M cb cc cn allb.
Proof.
  intros BC BA BB HA HB HP PP PA.
  pose proof(proj2(source_bounded_accept_unary M SFAll b allb k(or_introl eq_refl)HB)BB)as BAll.
  destruct(context_shift_total M cb cc cn)as(sb&sc&HShift).
  pose proof(context_shift_preserves_bound M cb cc cn sb sc k HShift BC)as BS.
  assert(PPoint:source_full_prv M sb sc cn point).
  { apply(source_full_prv_weaken_bounded M(zeroM M)(zeroM M)(zeroM M)sb sc cn point(succM M k)PP);
      [intros f H;exfalso;exact(context_empty M(zeroM M)(zeroM M)f H)|exact BS]. }
  exact(source_full_universal_map M cb cc cn a b alla allb point sb sc(ex_intro _ k(conj BAll BC))HA HB HP HShift PA PPoint).
Qed.
Print Assumptions source_full_all_map_from_empty.
