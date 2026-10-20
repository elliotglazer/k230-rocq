(** Remove the two exceptional tags from the exact comprehension profile
    at a domain element. The envelope supplies the reverse inclusion. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros TemplatePropositional QuantifierMacros NumericalKP0
  NamedLeibnizSteps RawMarkerExclusions NumericalTaggedComprehension
  EnvelopeSpecializations QuotientSeparationWitness ContextualPropositional QuotientAtomTemplates.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_raw_separation_tagged_point T A B C X Theta :=
  E_selection_iff (E_wel X C)
    (E_tagged_profile X B T (E_wa (E_wel X A) Theta)).
Definition E_raw_separation_clean_point T A C X Theta :=
  E_wim (E_wel T X) (E_selection_iff (E_wel X C) (E_wa (E_wel X A) Theta)).

Theorem numerical_raw_separation_point M rho T A B C X Z Theta tv zv :
  code_relation M rho T tv -> code_relation M rho Z zv ->
  zv<>zeroM M -> zv<>tv ->
  ns_proof M rho
    (E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B))
      (E_wim (E_envelope_point T A B X)
        (E_wim (E_raw_separation_tagged_point T A B C X Theta)
          (E_raw_separation_clean_point T A C X Theta))))).
Proof.
  intros HT HZ H0 HZT.
  set (Emp:=E_marker_empty T Z). set (DX:=E_wel T X).
  set (DB:=E_wel T B). set (DT:=E_wel T T).
  set (XA:=E_wel X A). set (XB:=E_wel X B). set (XC:=E_wel X C).
  set (Sel:=E_wa XA Theta).
  set (Case:=E_or (E_weq X B) (E_or (E_weq X T) (E_wa XB Sel))).
  set (EnvCase:=E_or (E_weq X A) (E_wa XA DX)).
  set (Env:=E_selection_iff XB EnvCase).
  set (Exact:=E_selection_iff XC Case).
  set (inputs:=E_wim Emp (E_wn DT) ::
    E_wim (E_weq X B) (E_wim DX DB) ::
    E_wim (E_weq X T) (E_wim DX DT) :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (marker_empty_specialization M rho T Z T tv zv tv HT HZ HT H0 HZT (not_eq_sym HZT)).
    + exact (marker_membership_transport M rho T X B).
    + exact (marker_membership_transport M rho T X T).
  - change (proof_macro nil inputs
      (E_wim Emp (E_wim (E_wn DB) (E_wim Env (E_wim Exact
        (E_wim DX (E_selection_iff XC Sel))))))).
    apply macro_discharge. do 5 apply macro_deduction.
    apply kp0_md_conjunction.
    + apply macro_deduction.
      apply (tagged_md_cases _ _ _ (E_weq X B) (E_or (E_weq X T) (E_wa XB Sel)) Sel).
      * eapply md_mp with (a:=XC);[apply md_hyp;now left|].
        apply tagged_md_left with (b:=E_wim Case XC).
        apply md_hyp;cbn;tauto.
      * apply macro_deduction. eapply md_mp with (a:=CEconst 1).
        -- eapply md_mp with (a:=DB).
           ++ eapply md_mp with (a:=DX);[apply md_hyp;cbn;tauto|].
              eapply md_mp with (a:=E_weq X B);[apply md_hyp;now left|].
              apply md_global,PM_input;unfold inputs;now right;left.
           ++ apply md_hyp;cbn;tauto.
        -- apply md_global,PM_template,template_F.
      * apply macro_deduction.
        apply (tagged_md_cases _ _ _ (E_weq X T) (E_wa XB Sel) Sel).
        -- apply md_hyp;now left.
        -- apply macro_deduction. eapply md_mp with (a:=CEconst 1).
           ++ eapply md_mp with (a:=DT).
              ** eapply md_mp with (a:=DX);[apply md_hyp;cbn;tauto|].
                 eapply md_mp with (a:=E_weq X T);[apply md_hyp;now left|].
                 apply md_global,PM_input;unfold inputs;now right;right;left.
              ** eapply md_mp with (a:=Emp);[apply md_hyp;cbn;tauto|].
                 apply md_global,PM_input;unfold inputs;now left.
           ++ apply md_global,PM_template,template_F.
        -- apply macro_deduction. apply tagged_md_right with (a:=XB).
           apply md_hyp;now left.
    + apply macro_deduction.
      eapply md_mp with (a:=Case).
      * eapply md_mp with (a:=E_or (E_weq X T) (E_wa XB Sel)).
        -- eapply md_mp with (a:=E_wa XB Sel).
           ++ apply kp0_md_conjunction.
              ** eapply md_mp with (a:=EnvCase).
                 --- eapply md_mp with (a:=E_wa XA DX).
                     +++ apply kp0_md_conjunction.
                         *** apply tagged_md_left with (b:=Theta),md_hyp;now left.
                         *** apply md_hyp;cbn;tauto.
                     +++ apply md_global,PM_template,template_or_right.
                 --- apply tagged_md_right with (a:=E_wim XB EnvCase).
                     apply md_hyp;cbn;tauto.
              ** apply md_hyp;now left.
           ++ apply md_global,PM_template,template_or_right.
        -- apply md_global,PM_template,template_or_right.
      * apply tagged_md_right with (a:=E_wim XC Case).
        apply md_hyp;cbn;tauto.
Qed.

Print Assumptions numerical_raw_separation_point.
