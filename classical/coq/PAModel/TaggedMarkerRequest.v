(** The marker request returns the marker once it is eligible. As with
    the root branch, the witness needs no substitution into theta. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NumericalEquality TemplatePropositional
  ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility
  NumericalBootstrap NumericalTaggedComprehension TemplateFormulaFresh
  NumericalVacuitySteps BoundVariableVacuityRules StoppingSpecialization
  QuotientAtomTemplates ContextualPropositional TaggedRootRequest.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_marker_exclusions y marker root singleton :=
  E_wa (E_wn (E_weq marker root)) (E_wal y (E_wn singleton)).

Lemma tagged_marker_output_program y carrier marker root theta singleton :
  proof_macro nil (E_vac y (E_weq marker marker) :: E_weq marker marker :: nil)
    (E_wex y (E_tagged_choices y marker carrier marker root theta singleton)).
Proof.
  assert (H:proof_macro nil (E_vac y (E_weq marker marker) :: E_weq marker marker :: nil)
    (E_wim (E_weq marker marker)
      (E_wim (E_wex y (E_weq y marker))
        (E_wex y (E_tagged_choices y marker carrier marker root theta singleton))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_or (E_wa (E_weq marker marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta))).
    - eapply md_mp with (a:=E_wa (E_weq marker marker) (E_weq y marker)).
      + apply kp0_md_conjunction;apply md_hyp;cbn;tauto.
      + apply md_global,PM_template,template_or_left.
    - apply md_global,PM_template,template_or_right. }
  eapply PM_mp.
  - exact (PM_template _ (TP_row LR1 y marker (CEconst 0) (CEconst 0))).
  - eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Theorem numerical_tagged_marker_output M rho y carrier marker root theta singleton yv :
  code_relation M rho y yv -> expression_name_avoids M rho yv marker ->
  ns_proof M rho (E_wex y (E_tagged_choices y marker carrier marker root theta singleton)).
Proof.
  intros HY HT. apply (ns_proof_macro M rho (E_vac y (E_weq marker marker) :: E_weq marker marker :: nil)).
  - intros e [<-|[<-|[]]].
    + apply (kp0_expression_fresh_vacuity M rho y (E_weq marker marker) yv HY).
      apply expression_fresh_atom;[now right|exact HT|exact HT].
    + apply ns_proof_reflexivity.
  - apply tagged_marker_output_program.
Qed.

Lemma tagged_marker_point_program y carrier marker root container theta singleton :
  proof_macro nil
    (E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
     E_wim (E_weq y marker) (E_wim (E_wel y container) (E_wel marker container)) :: nil)
    (E_wim (E_marker_exclusions y marker root singleton)
      (E_wim (E_wa (E_wel y container)
        (E_tagged_choices y marker carrier marker root theta singleton))
        (E_wel marker container))).
Proof.
  set (H:=E_marker_exclusions y marker root singleton).
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq marker root) (E_weq y carrier))
    (E_or (E_wa (E_weq marker marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta)))).
  - apply tagged_md_right with (a:=E_wel y container),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=CEconst 1).
    + eapply md_mp with (a:=E_weq marker root).
      * apply tagged_md_left with (b:=E_weq y carrier),md_hyp;now left.
      * unfold H,E_marker_exclusions. apply tagged_md_left with (b:=E_wal y (E_wn singleton)),
          md_hyp;cbn;tauto.
    + apply md_global,PM_template,template_F.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq marker marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta))).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=E_wel y container).
      * apply tagged_md_left with (b:=E_tagged_choices y marker carrier marker root theta singleton),
          md_hyp;cbn;tauto.
      * eapply md_mp with (a:=E_weq y marker).
        -- apply tagged_md_right with (a:=E_weq marker marker),md_hyp;now left.
        -- apply md_global,PM_input;now right;left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1).
      * eapply md_mp with (a:=singleton).
        -- apply tagged_md_left with (b:=E_wa (E_wel y carrier) theta),md_hyp;now left.
        -- eapply md_mp with (a:=E_wal y (E_wn singleton)).
           ++ unfold H,E_marker_exclusions. apply tagged_md_right with (a:=E_wn (E_weq marker root)),
                md_hyp;cbn;tauto.
           ++ apply md_global,PM_input;now left.
      * apply md_global,PM_template,template_F.
Qed.

Theorem numerical_tagged_marker_cleanup M rho y carrier marker root container theta singleton :
  ns_proof M rho (E_vac y (E_marker_exclusions y marker root singleton)) ->
  ns_proof M rho (E_vac y (E_wel marker container)) ->
  ns_proof M rho (E_wim (E_marker_exclusions y marker root singleton)
    (E_wim (E_wex y (E_wa (E_wel y container)
      (E_tagged_choices y marker carrier marker root theta singleton))) (E_wel marker container))).
Proof.
  intros HH HM. apply (ns_proof_macro M rho
    (E_vac y (E_marker_exclusions y marker root singleton) :: E_vac y (E_wel marker container) ::
     E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
     E_wim (E_weq y marker) (E_wim (E_wel y container) (E_wel marker container)) :: nil)).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact HH.
    + exact HM.
    + apply ns_stopping_self_specialization.
    + apply numerical_tagged_membership_transport.
  - eapply macro_syl.
    + apply kp0_parameter_exists;[apply PM_input;now left|].
      eapply (tagged_macro_inputs nil
        (E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
         E_wim (E_weq y marker) (E_wim (E_wel y container) (E_wel marker container)) :: nil)
        _ _);[|apply tagged_marker_point_program].
      intros e He. now right;right.
    + apply kp0_implication_map,request_existential_collapse,PM_input;now right;left.
Qed.

Theorem numerical_tagged_marker_request M rho y carrier marker root container theta singleton yv :
  code_relation M rho y yv -> yv<>zeroM M ->
  expression_name_avoids M rho yv root -> expression_name_avoids M rho yv marker ->
  expression_name_avoids M rho yv container ->
  ns_proof M rho (E_wim (E_marker_exclusions y marker root singleton)
    (E_wim (E_tagged_local_request y marker carrier marker root container theta singleton)
      (E_wim (E_kp_eligible root y container marker) (E_wel marker container)))).
Proof.
  intros HY H0 HR HT HK.
  assert (HC:ns_proof M rho (E_wim (E_marker_exclusions y marker root singleton)
    (E_wim (E_wex y (E_wa (E_wel y container)
      (E_tagged_choices y marker carrier marker root theta singleton))) (E_wel marker container)))).
  { apply numerical_tagged_marker_cleanup.
    - apply (ns_proof_macro M rho
        (E_vac y (E_wn (E_weq marker root)) :: E_vac y (E_wal y (E_wn singleton)) :: nil)).
      + intros e [<-|[<-|[]]].
        * apply (kp0_expression_fresh_vacuity M rho y (E_wn (E_weq marker root)) yv HY).
          apply expression_fresh_negation;[exact H0|].
          apply expression_fresh_atom;[now right|exact HT|exact HR].
        * apply ns_bound_universal_vacuity.
      + unfold E_marker_exclusions. apply kp0_vacuous_conjunction;apply PM_input;cbn;tauto.
    - apply (kp0_expression_fresh_vacuity M rho y (E_wel marker container) yv HY).
      apply expression_fresh_atom;[now left|exact HT|exact HK]. }
  apply (ns_proof_macro M rho
    (E_wim (E_marker_exclusions y marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y marker carrier marker root theta singleton))) (E_wel marker container)) ::
     E_wex y (E_tagged_choices y marker carrier marker root theta singleton) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact HC.
    + exact (numerical_tagged_marker_output M rho y carrier marker root theta singleton yv HY HT).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_wex y (E_wa (E_wel y container)
      (E_tagged_choices y marker carrier marker root theta singleton))).
    + eapply md_mp with (a:=E_wex y (E_tagged_choices y marker carrier marker root theta singleton)).
      * apply md_global,PM_input;now right;left.
      * eapply md_mp with (a:=E_kp_eligible root y container marker).
        -- apply md_hyp;now left.
        -- apply md_hyp;now right;left.
    + eapply md_mp with (a:=E_marker_exclusions y marker root singleton).
      * apply md_hyp;cbn;tauto.
      * apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_tagged_marker_output.
Print Assumptions numerical_tagged_marker_request.
