(** Finite assembly of the selected-singleton request. Every input below
    has a separate numerical proof: singleton profile/subset, eligibility,
    witness introduction, and the already checked witness cleanup. *)
From PAModel Require Import CodeExpressions ProofTemplates TemplatePropositional
  ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Eligibility NumericalBootstrap
  NumericalSingleton NumericalTaggedComprehension QuotientAtomTemplates.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_selected_exclusions X P T R Z :=
  E_wa (E_wn (E_weq P R)) (E_wa (E_wn (E_weq P T)) (E_raw_singleton X P Z)).

Definition selected_request_inputs Y X P B T R K Theta ThetaX Z :=
  E_wim (E_raw_singleton X P Z)
    (E_wal Y (E_wim (E_raw_singleton Y P Z) (E_weq Y X))) ::
  E_wim (E_wa (E_raw_singleton X P Z) (E_wel X B)) (E_ksubset P B K) ::
  E_wim (E_wa (E_wel B K) (E_ksubset P B K)) (E_kp_eligible R Y K P) ::
  E_wim (E_wa (E_raw_singleton X P Z) (E_wa (E_wel X B) ThetaX))
    (E_wex Y (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z))) ::
  E_wim (E_tagged_witness_hyp Y X P T R (E_raw_singleton Y P Z))
    (E_wim (E_wex Y (E_wa (E_wel Y K)
      (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z)))) (E_wel X K)) :: nil.

Lemma tagged_selected_request_program Y X P B T R K Theta ThetaX Z :
  proof_macro nil (selected_request_inputs Y X P B T R K Theta ThetaX Z)
    (E_wim (E_selected_exclusions X P T R Z)
      (E_wim (E_wel B K)
        (E_wim (E_tagged_local_request Y P B T R K Theta (E_raw_singleton Y P Z))
          (E_wim (E_wa (E_wel X B) ThetaX) (E_wel X K))))).
Proof.
  set (inputs:=selected_request_inputs Y X P B T R K Theta ThetaX Z).
  set (H:=E_selected_exclusions X P T R Z).
  set (L:=E_tagged_local_request Y P B T R K Theta (E_raw_singleton Y P Z)).
  set (Sel:=E_wa (E_wel X B) ThetaX).
  set (ctx:=Sel :: L :: E_wel B K :: H :: nil).
  apply macro_discharge. do 4 apply macro_deduction.
  assert (HS:macro_derivation nil inputs ctx (E_raw_singleton X P Z)).
  { unfold ctx,H,E_selected_exclusions. apply tagged_md_right with (a:=E_wn (E_weq P T)).
    apply tagged_md_right with (a:=E_wn (E_weq P R)),md_hyp;cbn;tauto. }
  assert (HCond:macro_derivation nil inputs ctx
    (E_tagged_witness_hyp Y X P T R (E_raw_singleton Y P Z))).
  { unfold E_tagged_witness_hyp. apply kp0_md_conjunction.
    - unfold ctx,H,E_selected_exclusions.
      apply tagged_md_left with (b:=E_wa (E_wn (E_weq P T)) (E_raw_singleton X P Z)),md_hyp;cbn;tauto.
    - apply kp0_md_conjunction.
      + unfold ctx,H,E_selected_exclusions.
        apply tagged_md_left with (b:=E_raw_singleton X P Z).
        apply tagged_md_right with (a:=E_wn (E_weq P R)),md_hyp;cbn;tauto.
      + eapply md_mp;[exact HS|]. apply md_global,PM_input.
        unfold inputs,selected_request_inputs;now left. }
  assert (HElig:macro_derivation nil inputs ctx (E_kp_eligible R Y K P)).
  { eapply md_mp with (a:=E_wa (E_wel B K) (E_ksubset P B K)).
    - apply kp0_md_conjunction.
      + unfold ctx. apply md_hyp;cbn;tauto.
      + eapply md_mp with (a:=E_wa (E_raw_singleton X P Z) (E_wel X B)).
        * apply kp0_md_conjunction;[exact HS|].
          unfold ctx,Sel. apply tagged_md_left with (b:=ThetaX),md_hyp;now left.
        * apply md_global,PM_input. unfold inputs,selected_request_inputs;now right;left.
    - apply md_global,PM_input. unfold inputs,selected_request_inputs;now right;right;left. }
  assert (HOut:macro_derivation nil inputs ctx
    (E_wex Y (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z)))).
  { eapply md_mp with (a:=E_wa (E_raw_singleton X P Z) Sel).
    - apply kp0_md_conjunction;[exact HS|]. unfold ctx. apply md_hyp;now left.
    - apply md_global,PM_input. unfold inputs,selected_request_inputs;now right;right;right;left. }
  eapply md_mp with (a:=E_wex Y (E_wa (E_wel Y K)
    (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z)))).
  - eapply md_mp;[exact HOut|].
    eapply md_mp;[exact HElig|]. unfold ctx. apply md_hyp;now right;left.
  - eapply md_mp;[exact HCond|]. apply md_global,PM_input.
    unfold inputs,selected_request_inputs;now right;right;right;right;left.
Qed.

Print Assumptions tagged_selected_request_program.
