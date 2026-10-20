(** Clean the output of a singleton-tagged binary Collection request.
    The supplied transport proof is later instantiated by actual raw
    matrix substitution; the two exceptional tags are explicitly excluded. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  TemplateCD TemplatePropositional ProofMacros QuantifierMacros NumericalVacuitySteps
  NamedLeibnizSteps NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility NumericalSingleton
  NumericalTaggedComprehension NumericalBootstrap QuotientAtomTemplates
  ContextualPropositional CollectionSupportCleanup.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_selected_hyp T R X P Z :=
  E_wa (E_raw_singleton X P Z) (E_wa (E_wn (E_weq P R)) (E_wn (E_weq P T))).
Definition E_collection_selected_result T C V ThetaX :=
  E_wa (E_wel T V) (E_wa (E_wel V C) ThetaX).

Lemma collection_selected_elimination_program T A C X P W V ThetaW ThetaX Z :
  proof_macro nil
    (E_vac W (E_wa (E_raw_singleton X P Z) (E_wel V C)) ::
     E_vac W (E_collection_selected_result T C V ThetaX) ::
     E_wim (E_raw_singleton X P Z) (E_wim (E_raw_singleton W P Z) (E_wim ThetaW ThetaX)) :: nil)
    (E_wim (E_wa (E_raw_singleton X P Z) (E_wel V C))
      (E_wim (E_collection_selected T A P W V ThetaW Z)
        (E_collection_selected_result T C V ThetaX))).
Proof.
  set (H:=E_wa (E_raw_singleton X P Z) (E_wel V C)).
  set (Out:=E_collection_selected_result T C V ThetaX).
  set (Body:=E_wa (E_raw_singleton W P Z)
    (E_wa (E_wa (E_wel T W) (E_wel W A)) (E_wa (E_wel T V) ThetaW))).
  set (inputs:=E_vac W H :: E_vac W Out ::
    E_wim (E_raw_singleton X P Z) (E_wim (E_raw_singleton W P Z) (E_wim ThetaW ThetaX)) :: nil).
  assert (HP:proof_macro nil inputs (E_wim H (E_wim Body Out))).
  { apply macro_discharge. do 2 apply macro_deduction.
    unfold Out,E_collection_selected_result. apply kp0_md_conjunction.
    - apply tagged_md_left with (b:=ThetaW).
      apply tagged_md_right with (a:=E_wa (E_wel T W) (E_wel W A)).
      unfold Body. apply tagged_md_right with (a:=E_raw_singleton W P Z),md_hyp;now left.
    - apply kp0_md_conjunction.
      + unfold H. apply tagged_md_right with (a:=E_raw_singleton X P Z),md_hyp;now right;left.
      + eapply md_mp with (a:=ThetaW).
        * apply tagged_md_right with (a:=E_wel T V).
          apply tagged_md_right with (a:=E_wa (E_wel T W) (E_wel W A)).
          unfold Body. apply tagged_md_right with (a:=E_raw_singleton W P Z),md_hyp;now left.
        * eapply md_mp with (a:=E_raw_singleton W P Z).
          -- unfold Body. apply tagged_md_left with
               (b:=E_wa (E_wa (E_wel T W) (E_wel W A)) (E_wa (E_wel T V) ThetaW)),md_hyp;now left.
          -- eapply md_mp with (a:=E_raw_singleton X P Z).
             ++ unfold H. apply tagged_md_left with (b:=E_wel V C),md_hyp;now right;left.
             ++ apply md_global,PM_input;unfold inputs;now right;right;left. }
  unfold E_collection_selected. eapply macro_syl.
  - apply kp0_parameter_exists;[apply PM_input;now left|exact HP].
  - apply kp0_implication_map,request_existential_collapse,PM_input;now right;left.
Qed.

Lemma collection_selected_choice_program T A B R C X P W V ThetaW ThetaX Z :
  proof_macro nil
    (E_wim (E_wa (E_raw_singleton X P Z) (E_wel V C))
      (E_wim (E_collection_selected T A P W V ThetaW Z)
        (E_collection_selected_result T C V ThetaX)) :: nil)
    (E_wim (E_collection_selected_hyp T R X P Z)
      (E_wim (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z))
        (E_collection_selected_result T C V ThetaX))).
Proof.
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq P R) (E_weq V B))
    (E_or (E_wa (E_weq P T) (E_weq V T)) (E_collection_selected T A P W V ThetaW Z))).
  - apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
    eapply md_mp with (a:=E_weq P R).
    + apply tagged_md_left with (b:=E_weq V B),md_hyp;now left.
    + unfold E_collection_selected_hyp. apply tagged_md_left with (b:=E_wn (E_weq P T)).
      apply tagged_md_right with (a:=E_raw_singleton X P Z),md_hyp;now right;right;left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq P T) (E_weq V T)) (E_collection_selected T A P W V ThetaW Z)).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_weq P T).
      * apply tagged_md_left with (b:=E_weq V T),md_hyp;now left.
      * unfold E_collection_selected_hyp. apply tagged_md_right with (a:=E_wn (E_weq P R)).
        apply tagged_md_right with (a:=E_raw_singleton X P Z),md_hyp;now right;right;right;left.
    + apply macro_deduction.
      eapply md_mp with (a:=E_collection_selected T A P W V ThetaW Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wa (E_raw_singleton X P Z) (E_wel V C)).
      * apply kp0_md_conjunction.
        -- unfold E_collection_selected_hyp. apply tagged_md_left with
             (b:=E_wa (E_wn (E_weq P R)) (E_wn (E_weq P T))),md_hyp;now right;right;right;left.
        -- apply tagged_md_left with (b:=E_collection_choices T A B R P W V ThetaW Z),
             md_hyp;now right;right;left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_collection_selected_cleanup M rho T A B R C X P W V ThetaW ThetaX Z :
  ns_proof M rho (E_vac W (E_wa (E_raw_singleton X P Z) (E_wel V C))) ->
  ns_proof M rho (E_vac W (E_collection_selected_result T C V ThetaX)) ->
  ns_proof M rho (E_wim (E_raw_singleton X P Z)
    (E_wim (E_raw_singleton W P Z) (E_wim ThetaW ThetaX))) ->
  ns_proof M rho (E_vac V (E_collection_selected_hyp T R X P Z)) ->
  ns_proof M rho (E_wim (E_collection_selected_hyp T R X P Z)
    (E_wim (E_wex V (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z)))
      (E_wex V (E_collection_selected_result T C V ThetaX)))).
Proof.
  intros VWH VWO HTransport VVH.
  assert (HP:ns_proof M rho
    (E_wim (E_wa (E_raw_singleton X P Z) (E_wel V C))
      (E_wim (E_collection_selected T A P W V ThetaW Z)
        (E_collection_selected_result T C V ThetaX)))).
  { apply (ns_proof_macro M rho
      (E_vac W (E_wa (E_raw_singleton X P Z) (E_wel V C)) ::
       E_vac W (E_collection_selected_result T C V ThetaX) ::
       E_wim (E_raw_singleton X P Z) (E_wim (E_raw_singleton W P Z) (E_wim ThetaW ThetaX)) :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - apply collection_selected_elimination_program. }
  assert (HC:ns_proof M rho (E_wim (E_collection_selected_hyp T R X P Z)
    (E_wim (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z))
      (E_collection_selected_result T C V ThetaX)))).
  { apply (ns_proof_macro M rho
      (E_wim (E_wa (E_raw_singleton X P Z) (E_wel V C))
        (E_wim (E_collection_selected T A P W V ThetaW Z)
          (E_collection_selected_result T C V ThetaX)) :: nil)).
    - intros e [<-|[]]. exact HP.
    - apply collection_selected_choice_program. }
  apply (ns_proof_macro M rho
    (E_vac V (E_collection_selected_hyp T R X P Z) ::
     E_wim (E_collection_selected_hyp T R X P Z)
       (E_wim (E_wa (E_wel V C) (E_collection_choices T A B R P W V ThetaW Z))
         (E_collection_selected_result T C V ThetaX)) :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply kp0_parameter_exists;apply PM_input;cbn;tauto.
Qed.

Print Assumptions collection_selected_elimination_program.
Print Assumptions collection_selected_choice_program.
Print Assumptions numerical_collection_selected_cleanup.
