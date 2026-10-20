(** Exceptional witnesses from the theta-free Collection request summary. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  TemplatePropositional TemplateCD ProofMacros QuantifierMacros NamedLeibnizSteps
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests NumericalBootstrap
  NumericalSingleton NumericalTaggedComprehension NumericalVacuitySteps
  QuotientAtomTemplates ContextualPropositional TemplateFormulaFresh
  StoppingSpecialization CollectionExceptionalRequests CollectionRequestProjection
  CollectionSupportCleanup CollectionRequestSpecialization.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma collection_no_singletons_not_exists U P Z :
  proof_macro nil nil (E_wim (E_collection_no_singletons U P Z)
    (E_wn (E_wex U (E_raw_singleton U P Z)))).
Proof. unfold E_collection_no_singletons,E_wex. apply PM_template,stopping_double_negation. Qed.

Lemma collection_summary_root_point T B R C U V Z :
  proof_macro nil
    (E_wim (E_weq V B) (E_wim (E_wel V C) (E_wel B C)) :: nil)
    (E_wim (E_collection_root_exclusions T R U Z)
      (E_wim (E_wa (E_wel V C) (E_collection_summary T B R R U V Z)) (E_wel B C))).
Proof.
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq R R) (E_weq V B))
    (E_or (E_wa (E_weq R T) (E_weq V T)) (E_wex U (E_raw_singleton U R Z)))).
  - apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=E_wel V C).
    + apply tagged_md_left with (b:=E_collection_summary T B R R U V Z),md_hyp;now right;left.
    + eapply md_mp with (a:=E_weq V B).
      * apply tagged_md_right with (a:=E_weq R R),md_hyp;now left.
      * apply md_global,PM_input;now left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq R T) (E_weq V T)) (E_wex U (E_raw_singleton U R Z))).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_weq R T).
      * apply tagged_md_left with (b:=E_weq V T),md_hyp;now left.
      * unfold E_collection_root_exclusions. apply tagged_md_left with (b:=E_collection_no_singletons U R Z),
          md_hyp;now right;right;right;left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_wex U (E_raw_singleton U R Z));[apply md_hyp;now left|].
      eapply md_mp with (a:=E_collection_no_singletons U R Z).
      * unfold E_collection_root_exclusions. apply tagged_md_right with (a:=E_wn (E_weq R T)),
          md_hyp;now right;right;right;left.
      * apply md_global,collection_empty_inputs,collection_no_singletons_not_exists.
Qed.

Lemma collection_summary_marker_point T B R C U V Z :
  proof_macro nil
    (E_wim (E_weq V T) (E_wim (E_wel V C) (E_wel T C)) :: nil)
    (E_wim (E_collection_marker_exclusions T R U Z)
      (E_wim (E_wa (E_wel V C) (E_collection_summary T B R T U V Z)) (E_wel T C))).
Proof.
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq T R) (E_weq V B))
    (E_or (E_wa (E_weq T T) (E_weq V T)) (E_wex U (E_raw_singleton U T Z)))).
  - apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
    eapply md_mp with (a:=E_weq T R).
    + apply tagged_md_left with (b:=E_weq V B),md_hyp;now left.
    + unfold E_collection_marker_exclusions. apply tagged_md_left with (b:=E_collection_no_singletons U T Z),
        md_hyp;now right;right;left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq T T) (E_weq V T)) (E_wex U (E_raw_singleton U T Z))).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=E_wel V C).
      * apply tagged_md_left with (b:=E_collection_summary T B R T U V Z),md_hyp;now right;right;left.
      * eapply md_mp with (a:=E_weq V T).
        -- apply tagged_md_right with (a:=E_weq T T),md_hyp;now left.
        -- apply md_global,PM_input;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_wex U (E_raw_singleton U T Z));[apply md_hyp;now left|].
      eapply md_mp with (a:=E_collection_no_singletons U T Z).
      * unfold E_collection_marker_exclusions. apply tagged_md_right with (a:=E_wn (E_weq T R)),
          md_hyp;now right;right;right;left.
      * apply md_global,collection_empty_inputs,collection_no_singletons_not_exists.
Qed.

Lemma collection_summary_request M rho V C InputChoice OutputChoice Exclusions Output Eligible :
  ns_proof M rho (E_vac V Exclusions) -> ns_proof M rho (E_vac V Output) ->
  ns_proof M rho (E_wim Exclusions (E_wim (E_wa (E_wel V C) OutputChoice) Output)) ->
  ns_proof M rho (E_wex V InputChoice) ->
  ns_proof M rho (E_wim Exclusions
    (E_wim (E_wim Eligible (E_wim (E_wex V InputChoice)
      (E_wex V (E_wa (E_wel V C) OutputChoice)))) (E_wim Eligible Output))).
Proof.
  intros HVH HVO HPoint HExists.
  assert (HC:ns_proof M rho (E_wim Exclusions (E_wim (E_wex V (E_wa (E_wel V C) OutputChoice)) Output))).
  { apply (ns_proof_macro M rho (E_vac V Exclusions :: E_vac V Output ::
      E_wim Exclusions (E_wim (E_wa (E_wel V C) OutputChoice) Output) :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - eapply macro_syl.
      + apply kp0_parameter_exists;apply PM_input;cbn;tauto.
      + apply kp0_implication_map,request_existential_collapse,PM_input;now right;left. }
  apply (ns_proof_macro M rho
    (E_wim Exclusions (E_wim (E_wex V (E_wa (E_wel V C) OutputChoice)) Output) :: E_wex V InputChoice :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_wex V (E_wa (E_wel V C) OutputChoice)).
    + eapply md_mp with (a:=E_wex V InputChoice);[apply md_global,PM_input;now right;left|].
      eapply md_mp with (a:=Eligible);[apply md_hyp;now left|apply md_hyp;now right;left].
    + eapply md_mp with (a:=Exclusions);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now left.
Qed.

Lemma collection_first_two_root_program T B R V :
  proof_macro nil (E_vac V (E_weq R R) :: E_weq R R :: nil)
    (E_wex V (E_collection_first_two T B R R V)).
Proof.
  assert (H:proof_macro nil (E_vac V (E_weq R R) :: E_weq R R :: nil)
    (E_wim (E_weq R R) (E_wim (E_wex V (E_weq V B))
      (E_wex V (E_collection_first_two T B R R V))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wa (E_weq R R) (E_weq V B));
      [apply kp0_md_conjunction;apply md_hyp;cbn;tauto|].
    apply md_global,PM_template,template_or_left. }
  eapply PM_mp;[exact (PM_template _ (TP_row LR1 V B (CEconst 0) (CEconst 0)))|].
  eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Lemma collection_first_two_marker_program T B R V :
  proof_macro nil (E_vac V (E_weq T T) :: E_weq T T :: nil)
    (E_wex V (E_collection_first_two T B R T V)).
Proof.
  assert (H:proof_macro nil (E_vac V (E_weq T T) :: E_weq T T :: nil)
    (E_wim (E_weq T T) (E_wim (E_wex V (E_weq V T))
      (E_wex V (E_collection_first_two T B R T V))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wa (E_weq T T) (E_weq V T));
      [apply kp0_md_conjunction;apply md_hyp;cbn;tauto|].
    apply md_global,PM_template,template_or_right. }
  eapply PM_mp;[exact (PM_template _ (TP_row LR1 V T (CEconst 0) (CEconst 0)))|].
  eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Print Assumptions collection_summary_root_point.
Print Assumptions collection_summary_marker_point.
Print Assumptions collection_summary_request.
Print Assumptions collection_first_two_root_program.
Print Assumptions collection_first_two_marker_program.

Theorem numerical_collection_summary_root_conditional M rho T B R C U V Z vv :
  code_relation M rho V vv -> vv<>zeroM M ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv B ->
  expression_name_avoids M rho vv R -> expression_name_avoids M rho vv C ->
  expression_name_avoids M rho vv U -> expression_name_avoids M rho vv Z ->
  ns_proof M rho (E_wim (E_collection_root_exclusions T R U Z)
    (E_wim (E_collection_reduced_at T B R C R U V Z)
      (E_wim (E_kp_eligible R V C R) (E_wel B C)))).
Proof.
  intros HV H0 HT HB HR HC HU HZ. apply collection_summary_request.
  - apply (kp0_expression_fresh_vacuity M rho V (E_collection_root_exclusions T R U Z) vv HV).
    unfold E_collection_root_exclusions. apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_negation;[exact H0|].
      apply expression_fresh_atom;[now right|exact HR|exact HT].
    + now apply collection_no_singletons_fresh.
  - apply (kp0_expression_fresh_vacuity M rho V (E_wel B C) vv HV).
    apply expression_fresh_atom;[now left|exact HB|exact HC].
  - apply (ns_proof_macro M rho (E_wim (E_weq V B) (E_wim (E_wel V C) (E_wel B C)) :: nil)).
    + intros e [<-|[]]. apply numerical_tagged_membership_transport.
    + apply collection_summary_root_point.
  - apply (ns_proof_macro M rho (E_vac V (E_weq R R) :: E_weq R R :: nil)).
    + intros e [<-|[<-|[]]].
      * apply (kp0_expression_fresh_vacuity M rho V (E_weq R R) vv HV).
        apply expression_fresh_atom;[now right|exact HR|exact HR].
      * apply ns_proof_reflexivity.
    + apply collection_first_two_root_program.
Qed.

Theorem numerical_collection_summary_marker_request M rho T B R C U V Z vv :
  code_relation M rho V vv -> vv<>zeroM M ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv R ->
  expression_name_avoids M rho vv C -> expression_name_avoids M rho vv U ->
  expression_name_avoids M rho vv Z ->
  ns_proof M rho (E_wim (E_collection_marker_exclusions T R U Z)
    (E_wim (E_collection_reduced_at T B R C T U V Z)
      (E_wim (E_kp_eligible R V C T) (E_wel T C)))).
Proof.
  intros HV H0 HT HR HC HU HZ. apply collection_summary_request.
  - apply (kp0_expression_fresh_vacuity M rho V (E_collection_marker_exclusions T R U Z) vv HV).
    unfold E_collection_marker_exclusions. apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_negation;[exact H0|].
      apply expression_fresh_atom;[now right|exact HT|exact HR].
    + now apply collection_no_singletons_fresh.
  - apply (kp0_expression_fresh_vacuity M rho V (E_wel T C) vv HV).
    apply expression_fresh_atom;[now left|exact HT|exact HC].
  - apply (ns_proof_macro M rho (E_wim (E_weq V T) (E_wim (E_wel V C) (E_wel T C)) :: nil)).
    + intros e [<-|[]]. apply numerical_tagged_membership_transport.
    + apply collection_summary_marker_point.
  - apply (ns_proof_macro M rho (E_vac V (E_weq T T) :: E_weq T T :: nil)).
    + intros e [<-|[<-|[]]].
      * apply (kp0_expression_fresh_vacuity M rho V (E_weq T T) vv HV).
        apply expression_fresh_atom;[now right|exact HT|exact HT].
      * apply ns_proof_reflexivity.
    + apply collection_first_two_marker_program.
Qed.

Theorem numerical_collection_summary_root_request M rho T B R C U V Z vv :
  code_relation M rho V vv -> vv<>zeroM M ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv B ->
  expression_name_avoids M rho vv R -> expression_name_avoids M rho vv C ->
  expression_name_avoids M rho vv U -> expression_name_avoids M rho vv Z ->
  ns_proof M rho (E_wim (E_collection_root_exclusions T R U Z)
    (E_wim (E_collection_reduced_at T B R C R U V Z) (E_wel B C))).
Proof.
  intros HV H0 HT HB HR HC HU HZ.
  apply (ns_proof_macro M rho
    (E_wim (E_collection_root_exclusions T R U Z)
      (E_wim (E_collection_reduced_at T B R C R U V Z)
        (E_wim (E_kp_eligible R V C R) (E_wel B C))) :: E_weq R R :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_collection_summary_root_conditional M rho T B R C U V Z vv HV H0 HT HB HR HC HU HZ).
    + apply ns_proof_reflexivity.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_kp_eligible R V C R).
    + unfold E_kp_eligible. eapply md_mp with (a:=E_weq R R).
      * apply md_global,PM_input;now right;left.
      * apply md_global,PM_template,template_or_left.
    + eapply md_mp with (a:=E_collection_reduced_at T B R C R U V Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_collection_root_exclusions T R U Z);[apply md_hyp;now right;left|].
      apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_collection_summary_root_request.
Print Assumptions numerical_collection_summary_marker_request.
