(** The selected-singleton request yields Collection coverage. Every input
    is one of the numerical lemmas proved separately in this development. *)
From PAModel Require Import CodeExpressions ProofTemplates ProofMacros QuantifierMacros
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests NumericalBootstrap
  NumericalSingleton NumericalTaggedComprehension QuotientAtomTemplates
  CollectionSupportCleanup CollectionKernel CollectionFullSpecialization
  CollectionSelectedCleanup CollectionSelectedOutput.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition collection_coverage_inputs T A B R C X P W V ThetaW ThetaX Z :=
  E_wim (E_wa (E_wel T X) (E_wel X A)) (E_wel X B) ::
  E_wim (E_wa (E_raw_singleton X P Z) (E_wel X B)) (E_ksubset P B C) ::
  E_wim (E_wa (E_wel B C) (E_ksubset P B C)) (E_kp_eligible R V C P) ::
  E_wim (E_wa (E_raw_singleton X P Z) (E_wa (E_wel T X) (E_wel X A)))
    (E_wim (E_wex V (E_wa (E_wel T V) ThetaX))
      (E_wex V (E_collection_choices T A B R P W V ThetaW Z))) ::
  E_wim (E_collection_selected_hyp T R X P Z)
    (E_wim (E_wex V (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z)))
      (E_wex V (E_collection_selected_result T C V ThetaX))) :: nil.

Lemma collection_coverage_program T A B R C X P W V ThetaW ThetaX Z :
  proof_macro nil (collection_coverage_inputs T A B R C X P W V ThetaW ThetaX Z)
    (E_wim (E_collection_selected_hyp T R X P Z)
      (E_wim (E_wel B C)
        (E_wim (E_collection_request_at T A B R C P W V ThetaW Z)
          (E_wim (E_wa (E_wel T X) (E_wel X A))
            (E_wim (E_wex V (E_wa (E_wel T V) ThetaX))
              (E_wex V (E_collection_selected_result T C V ThetaX))))))).
Proof.
  set (inputs:=collection_coverage_inputs T A B R C X P W V ThetaW ThetaX Z).
  set (H:=E_collection_selected_hyp T R X P Z).
  set (D:=E_wa (E_wel T X) (E_wel X A)).
  set (L:=E_collection_request_at T A B R C P W V ThetaW Z).
  set (I:=E_wex V (E_wa (E_wel T V) ThetaX)).
  set (ctx:=I :: D :: L :: E_wel B C :: H :: nil).
  apply macro_discharge. do 5 apply macro_deduction.
  assert (HS:macro_derivation nil inputs ctx (E_raw_singleton X P Z)).
  { unfold ctx,H,E_collection_selected_hyp. apply tagged_md_left with
      (b:=E_wa (E_wn (E_weq P R)) (E_wn (E_weq P T))),md_hyp;cbn;tauto. }
  assert (HXB:macro_derivation nil inputs ctx (E_wel X B)).
  { eapply md_mp with (a:=D);[unfold ctx;apply md_hyp;cbn;tauto|].
    apply md_global,PM_input;unfold inputs,collection_coverage_inputs;now left. }
  assert (HElig:macro_derivation nil inputs ctx (E_kp_eligible R V C P)).
  { eapply md_mp with (a:=E_wa (E_wel B C) (E_ksubset P B C)).
    - apply kp0_md_conjunction.
      + unfold ctx. apply md_hyp;cbn;tauto.
      + eapply md_mp with (a:=E_wa (E_raw_singleton X P Z) (E_wel X B)).
        * apply kp0_md_conjunction;assumption.
        * apply md_global,PM_input;unfold inputs,collection_coverage_inputs;now right;left.
    - apply md_global,PM_input;unfold inputs,collection_coverage_inputs;now right;right;left. }
  assert (HOut:macro_derivation nil inputs ctx (E_wex V (E_collection_choices T A B R P W V ThetaW Z))).
  { eapply md_mp with (a:=I);[unfold ctx;apply md_hyp;now left|].
    eapply md_mp with (a:=E_wa (E_raw_singleton X P Z) D).
    - apply kp0_md_conjunction;[exact HS|unfold ctx;apply md_hyp;now right;left].
    - apply md_global,PM_input;unfold inputs,collection_coverage_inputs;now right;right;right;left. }
  eapply md_mp with (a:=E_wex V (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z))).
  - eapply md_mp;[exact HOut|]. eapply md_mp;[exact HElig|].
    unfold ctx. apply md_hyp;now right;right;left.
  - eapply md_mp with (a:=H);[unfold ctx;apply md_hyp;cbn;tauto|].
    apply md_global,PM_input;unfold inputs,collection_coverage_inputs;now right;right;right;right;left.
Qed.

Print Assumptions collection_coverage_program.
