(** Named quantifier graphs and proof rules. Equivalent numerical
    closing maps are reconciled explicitly before existential mapping. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
  NumericalRenamingMaps NumericalRenaming RawBinderRenaming SourceNamedSelfSpecialization
  SourceNamedVacuity SourceNamedProofRules NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.

Definition source_named_quantifier M (universal:bool) x f result :=exists rb rc body,
  raw_binder_renaming M x rb rc /\
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body /\
  sf_relation M (if universal then SFAll else SFEx) body (zeroM M) result.

Theorem source_named_quantifier_total M universal x f :
  exists result,source_named_quantifier M universal x f result.
Proof.
  destruct (raw_binder_renaming_total M x) as (rb&rc&HM).
  destruct (numerical_renaming_total M f rb rc (succM M x)(succM M (zeroM M))) as (body&HR).
  destruct (sf_relation_total M (if universal then SFAll else SFEx) body (zeroM M)) as (result&HQ).
  exists result,rb,rc,body. auto.
Qed.

Theorem source_named_quantifier_functional M universal x f result other :
  source_named_quantifier M universal x f result ->source_named_quantifier M universal x f other ->result=other.
Proof.
  intros (rb&rc&body&HM&HR&HQ)(sb&sc&otherbody&HS&HT&HO).
  assert (HT':numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) otherbody).
  { apply (proj1 (numerical_renaming_extensional M f sb sc (succM M x) rb rc
      (succM M x)(succM M (zeroM M)) otherbody
      (raw_binder_renaming_equivalent M x sb sc rb rc HS HM))). exact HT. }
  rewrite (numerical_renaming_functional M f rb rc _ _ body otherbody HR HT') in HQ.
  exact (sf_relation_functional M _ _ _ result other HQ HO).
Qed.

Theorem source_named_quantifier_bound M universal x f result k :
  source_bounded M f k ->source_named_quantifier M universal x f result ->source_bounded M result k.
Proof.
  intros HF (rb&rc&body&HM&HR&HQ).
  apply (proj2 (source_bounded_accept_unary M (if universal then SFAll else SFEx) body result k
    ltac:(destruct universal;unfold sf_unary;auto) HQ)).
  exact (source_named_closure_bounded M f x rb rc body k HF HM HR).
Qed.

Theorem source_named_quantifier_is_vacuous M universal x f result k :
  source_bounded M f k ->source_named_quantifier M universal x f result ->source_named_vacuous M x result.
Proof.
  intros HF (rb&rc&body&HM&HR&HQ).
  exact (source_named_quantifier_vacuous M universal f x rb rc body result k HF HM HR HQ).
Qed.

Theorem source_full_named_quantifier_all_intro M b c n x f result :
  source_named_context_vacuous M b c n x ->source_named_quantifier M true x f result ->
  source_full_prv M b c n f ->source_full_prv M b c n result.
Proof.
  intros HC (rb&rc&body&HM&HR&HQ) HP.
  exact (source_full_named_all_intro M b c n f x rb rc body result HC HM HR HQ HP).
Qed.

Theorem source_full_named_quantifier_ex_intro M b c n x f result :
  source_named_quantifier M false x f result ->
  source_full_prv M b c n f ->source_full_prv M b c n result.
Proof.
  intros (rb&rc&body&HM&HR&HQ) HP.
  exact (source_full_named_self_exists_intro M b c n f x rb rc body result HM HR HQ HP).
Qed.

Theorem source_full_named_quantifier_ex_map M b c n x f g exf exg imp :
  source_named_context_vacuous M b c n x ->source_named_quantifier M false x f exf ->
  source_named_quantifier M false x g exg ->sf_relation M SFImpl f g imp ->
  source_full_prv M b c n imp ->source_full_prv M b c n exf ->source_full_prv M b c n exg.
Proof.
  intros HC (rb&rc&fb&HM&HF&HEF)(sb&sc&gb&HS&HG&HEG) HI PI PEF.
  assert (HG':numerical_renaming M g rb rc (succM M x)(succM M (zeroM M)) gb).
  { apply (proj1 (numerical_renaming_extensional M g sb sc (succM M x) rb rc
      (succM M x)(succM M (zeroM M)) gb
      (raw_binder_renaming_equivalent M x sb sc rb rc HS HM))). exact HG. }
  exact (source_full_named_exists_map M b c n f g x rb rc fb gb exf exg imp
    HC HM HF HG' HEF HEG HI PI PEF).
Qed.

Print Assumptions source_named_quantifier_is_vacuous.
Print Assumptions source_full_named_quantifier_ex_map.
