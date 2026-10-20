(** The root request puts the original carrier into the tagged container.
    Its proof does not substitute into the arbitrary predicate: a witness
    is introduced through the first disjunct alone. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NumericalEquality TemplatePropositional
  ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Requests
  NumericalKP0Eligibility NumericalBootstrap NumericalSingleton NumericalTaggedComprehension
  TemplateFormulaFresh NumericalVacuitySteps BoundVariableVacuityRules StoppingSpecialization QuotientAtomTemplates
  ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_root_exclusions y marker root singleton :=
  E_wa (E_wn (E_weq root marker)) (E_wal y (E_wn singleton)).

Lemma tagged_root_output_program y carrier marker root theta singleton :
  proof_macro nil (E_vac y (E_weq root root) :: E_weq root root :: nil)
    (E_wex y (E_tagged_choices y root carrier marker root theta singleton)).
Proof.
  assert (H:proof_macro nil (E_vac y (E_weq root root) :: E_weq root root :: nil)
    (E_wim (E_weq root root)
      (E_wim (E_wex y (E_weq y carrier))
        (E_wex y (E_tagged_choices y root carrier marker root theta singleton))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wa (E_weq root root) (E_weq y carrier));
      [apply kp0_md_conjunction;apply md_hyp;cbn;tauto|].
    apply md_global,PM_template,template_or_left. }
  eapply PM_mp.
  - exact (PM_template _ (TP_row LR1 y carrier (CEconst 0) (CEconst 0))).
  - eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Theorem numerical_tagged_root_output M rho y carrier marker root theta singleton yv :
  code_relation M rho y yv -> expression_name_avoids M rho yv root ->
  ns_proof M rho (E_wex y (E_tagged_choices y root carrier marker root theta singleton)).
Proof.
  intros HY HR. apply (ns_proof_macro M rho (E_vac y (E_weq root root) :: E_weq root root :: nil)).
  - intros e [<-|[<-|[]]].
    + apply (kp0_expression_fresh_vacuity M rho y (E_weq root root) yv HY).
      apply expression_fresh_atom;[now right|exact HR|exact HR].
    + apply ns_proof_reflexivity.
  - apply tagged_root_output_program.
Qed.

Lemma tagged_root_point_program y carrier marker root container theta singleton :
  proof_macro nil
    (E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
     E_wim (E_weq y carrier) (E_wim (E_wel y container) (E_wel carrier container)) :: nil)
    (E_wim (E_root_exclusions y marker root singleton)
      (E_wim (E_wa (E_wel y container)
        (E_tagged_choices y root carrier marker root theta singleton))
        (E_wel carrier container))).
Proof.
  set (H:=E_root_exclusions y marker root singleton).
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq root root) (E_weq y carrier))
    (E_or (E_wa (E_weq root marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta)))).
  - apply tagged_md_right with (a:=E_wel y container),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=E_wel y container).
    + apply tagged_md_left with (b:=E_tagged_choices y root carrier marker root theta singleton),
        md_hyp;cbn;tauto.
    + eapply md_mp with (a:=E_weq y carrier).
      * apply tagged_md_right with (a:=E_weq root root),md_hyp;now left.
      * apply md_global,PM_input;now right;left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq root marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta))).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1).
      * eapply md_mp with (a:=E_weq root marker).
        -- apply tagged_md_left with (b:=E_weq y marker),md_hyp;now left.
        -- unfold H,E_root_exclusions. apply tagged_md_left with (b:=E_wal y (E_wn singleton)),
             md_hyp;cbn;tauto.
      * apply md_global,PM_template,template_F.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1).
      * eapply md_mp with (a:=singleton).
        -- apply tagged_md_left with (b:=E_wa (E_wel y carrier) theta),md_hyp;now left.
        -- eapply md_mp with (a:=E_wal y (E_wn singleton)).
           ++ unfold H,E_root_exclusions. apply tagged_md_right with (a:=E_wn (E_weq root marker)),
                md_hyp;cbn;tauto.
           ++ apply md_global,PM_input;now left.
      * apply md_global,PM_template,template_F.
Qed.

Lemma tagged_root_cleanup_program y carrier marker root container theta singleton :
  proof_macro nil
    (E_vac y (E_root_exclusions y marker root singleton) ::
     E_vac y (E_wel carrier container) ::
     E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
     E_wim (E_weq y carrier) (E_wim (E_wel y container) (E_wel carrier container)) :: nil)
    (E_wim (E_root_exclusions y marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y root carrier marker root theta singleton))) (E_wel carrier container))).
Proof.
  eapply macro_syl.
  - apply kp0_parameter_exists;[apply PM_input;now left|].
    eapply (tagged_macro_inputs nil
      (E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
       E_wim (E_weq y carrier) (E_wim (E_wel y container) (E_wel carrier container)) :: nil)
      _ _);[|apply tagged_root_point_program].
    intros e He. now right;right.
  - apply kp0_implication_map,request_existential_collapse,PM_input;now right;left.
Qed.

Theorem numerical_tagged_root_request M rho y carrier marker root container theta singleton yv :
  code_relation M rho y yv -> yv<>zeroM M ->
  expression_name_avoids M rho yv root -> expression_name_avoids M rho yv marker ->
  expression_name_avoids M rho yv carrier -> expression_name_avoids M rho yv container ->
  ns_proof M rho (E_wim (E_root_exclusions y marker root singleton)
    (E_wim (E_tagged_local_request y root carrier marker root container theta singleton)
      (E_wel carrier container))).
Proof.
  intros HY H0 HR HT HB HK.
  assert (HC:ns_proof M rho
    (E_wim (E_root_exclusions y marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y root carrier marker root theta singleton))) (E_wel carrier container)))).
  { apply (ns_proof_macro M rho
      (E_vac y (E_root_exclusions y marker root singleton) :: E_vac y (E_wel carrier container) ::
       E_wim (E_wal y (E_wn singleton)) (E_wn singleton) ::
       E_wim (E_weq y carrier) (E_wim (E_wel y container) (E_wel carrier container)) :: nil)).
    - intros e [<-|[<-|[<-|[<-|[]]]]].
      + apply (ns_proof_macro M rho
          (E_vac y (E_wn (E_weq root marker)) :: E_vac y (E_wal y (E_wn singleton)) :: nil)).
        * intros e [<-|[<-|[]]].
          -- apply (kp0_expression_fresh_vacuity M rho y (E_wn (E_weq root marker)) yv HY).
             apply expression_fresh_negation;[exact H0|].
             apply expression_fresh_atom;[now right|exact HR|exact HT].
          -- apply ns_bound_universal_vacuity.
        * unfold E_root_exclusions. apply kp0_vacuous_conjunction;apply PM_input;cbn;tauto.
      + apply (kp0_expression_fresh_vacuity M rho y (E_wel carrier container) yv HY).
        apply expression_fresh_atom;[now left|exact HB|exact HK].
      + apply ns_stopping_self_specialization.
      + apply numerical_tagged_membership_transport.
    - apply tagged_root_cleanup_program. }
  apply (ns_proof_macro M rho
    (E_wim (E_root_exclusions y marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y root carrier marker root theta singleton))) (E_wel carrier container)) ::
     E_wex y (E_tagged_choices y root carrier marker root theta singleton) ::
     E_kp_eligible root y container root :: nil)).
  - intros e [<-|[<-|[<-|[]]]].
    + exact HC.
    + exact (numerical_tagged_root_output M rho y carrier marker root theta singleton yv HY HR).
    + apply (ns_proof_macro M rho (E_weq root root :: nil)).
      * intros e [<-|[]]. apply ns_proof_reflexivity.
      * unfold E_kp_eligible. eapply PM_mp;[apply PM_input;now left|].
        apply PM_template,template_or_left.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wex y (E_wa (E_wel y container)
      (E_tagged_choices y root carrier marker root theta singleton))).
    + eapply md_mp with (a:=E_wex y (E_tagged_choices y root carrier marker root theta singleton)).
      * apply md_global,PM_input;now right;left.
      * eapply md_mp with (a:=E_kp_eligible root y container root).
        -- apply md_global,PM_input;now right;right;left.
        -- apply md_hyp;now left.
    + eapply md_mp with (a:=E_root_exclusions y marker root singleton).
      * apply md_hyp;now right;left.
      * apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_tagged_root_output.
Print Assumptions numerical_tagged_root_request.
