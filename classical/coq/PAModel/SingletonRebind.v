(** Reconcile a chosen singleton's profile binder with the binder used by
    the tagged matrix. The singleton container itself is unchanged. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros QuantifierMacros NumericalVacuitySteps NamedLeibnizSteps
  TemplateFormulaFresh NumericalKP0 NumericalKP0Eligibility NumericalSingleton
  NumericalTaggedComprehension RawMarkerQuantifiers.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_singleton_rebind M rho X P Z W xv pv zv wv :
  code_relation M rho X xv -> code_relation M rho P pv ->
  code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>wv -> pv<>zv -> xv<>zv -> pv<>wv -> xv<>wv ->
  ns_proof M rho (E_wim (E_raw_singleton X P Z) (E_raw_singleton X P W)).
Proof.
  intros HX HP HZ HW HZW HPZ HXZ HPW HXW.
  set (AZ:=E_wal Z (E_wim (E_wel Z P) (E_weq Z X))).
  set (AW:=E_wal W (E_wim (E_wel W P) (E_weq W X))).
  assert (HProfile:ns_proof M rho (E_wim AZ AW)).
  { apply marker_generalize_one.
    - apply (kp0_expression_fresh_vacuity M rho W AZ wv HW).
      unfold AZ. apply expression_fresh_universal.
      + exact (marker_name_avoids M rho Z zv wv HZ HZW).
      + apply expression_fresh_implication.
        * apply expression_fresh_atom;[now left| |];eapply marker_name_avoids;eassumption.
        * apply expression_fresh_atom;[now right| |];eapply marker_name_avoids;eassumption.
    - exact (singleton_profile_specialization M rho Z W X P zv wv xv pv HZ HW HX HP HZW HPZ HXZ). }
  apply (ns_proof_macro M rho (E_wim AZ AW :: nil)).
  - intros e [<-|[]]. exact HProfile.
  - change (proof_macro nil (E_wim AZ AW :: nil)
      (E_wim (E_wa (E_wel X P) AZ) (E_wa (E_wel X P) AW))).
    apply macro_discharge,macro_deduction,kp0_md_conjunction.
    + apply tagged_md_left with (b:=AZ),md_hyp;now left.
    + eapply md_mp with (a:=AZ).
      * apply tagged_md_right with (a:=E_wel X P),md_hyp;now left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_singleton_exists_rebind M rho X P Z W xv pv zv wv :
  code_relation M rho X xv -> code_relation M rho P pv ->
  code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>wv -> pv<>zv -> xv<>zv -> pv<>wv -> xv<>wv ->
  ns_proof M rho
    (E_wim (E_wex P (E_raw_singleton X P Z)) (E_wex P (E_raw_singleton X P W))).
Proof.
  intros HX HP HZ HW HZW HPZ HXZ HPW HXW.
  apply (ns_proof_macro M rho (E_wim (E_raw_singleton X P Z) (E_raw_singleton X P W) :: nil)).
  - intros e [<-|[]]. exact (numerical_singleton_rebind M rho X P Z W xv pv zv wv
      HX HP HZ HW HZW HPZ HXZ HPW HXW).
  - apply macro_exists_monotone,PM_input;now left.
Qed.

Print Assumptions numerical_singleton_rebind.
Print Assumptions numerical_singleton_exists_rebind.
