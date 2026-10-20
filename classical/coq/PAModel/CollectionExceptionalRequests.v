(** Exceptional root and empty-marker requests in the binary Collection
    matrix. No substitution into the arbitrary internal relation is used. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  TemplateCD TemplatePropositional NamedLeibnizSteps NumericalEquality
  ProofMacros QuantifierMacros NumericalVacuitySteps NumericalKP0 NumericalKP0Requests
  NumericalKP0Eligibility NumericalSingleton NumericalTaggedComprehension NumericalBootstrap
  TemplateFormulaFresh QuotientAtomTemplates ContextualPropositional RawMarkerExclusions
  RawMarkerQuantifiers BoundVariableVacuityRules StoppingSpecialization NamedSelfExistential CollectionSupportCleanup.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_no_singletons U I Z := E_wal U (E_wn (E_raw_singleton U I Z)).
Definition E_collection_root_exclusions T R U Z :=
  E_wa (E_wn (E_weq R T)) (E_collection_no_singletons U R Z).
Definition E_collection_marker_exclusions T R U Z :=
  E_wa (E_wn (E_weq T R)) (E_collection_no_singletons U T Z).

Lemma collection_selected_impossible_program T A I U V Theta Z :
  proof_macro nil nil (E_wim (E_collection_no_singletons U I Z)
    (E_wn (E_collection_selected T A I U V Theta Z))).
Proof.
  unfold E_collection_no_singletons,E_collection_selected.
  assert (H:proof_macro nil nil (E_wim
    (E_wex U (E_wa (E_raw_singleton U I Z)
      (E_wa (E_wa (E_wel T U) (E_wel U A)) (E_wa (E_wel T V) Theta))))
    (E_wex U (E_raw_singleton U I Z)))).
  { apply macro_exists_monotone,PM_template,bootstrap_projection_left. }
  eapply macro_syl;[apply PM_template,stopping_double_negation|].
  exact (macro_contra nil nil _ _ H).
Qed.

Lemma collection_root_case_program T A B R C U V Theta Z :
  proof_macro nil
    (E_wim (E_weq V B) (E_wim (E_wel V C) (E_wel B C)) :: nil)
    (E_wim (E_collection_root_exclusions T R U Z)
      (E_wim (E_wa (E_wel V C) (E_collection_choices T A B R R U V Theta Z)) (E_wel B C))).
Proof.
  assert (HS:proof_macro nil
      (E_wim (E_weq V B) (E_wim (E_wel V C) (E_wel B C)) :: nil)
      (E_wim (E_collection_no_singletons U R Z) (E_wn (E_collection_selected T A R U V Theta Z)))).
  { apply collection_empty_inputs,collection_selected_impossible_program. }
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq R R) (E_weq V B))
    (E_or (E_wa (E_weq R T) (E_weq V T)) (E_collection_selected T A R U V Theta Z))).
  - apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=E_wel V C).
    + apply tagged_md_left with (b:=E_collection_choices T A B R R U V Theta Z),md_hyp;now right;left.
    + eapply md_mp with (a:=E_weq V B).
      * apply tagged_md_right with (a:=E_weq R R),md_hyp;now left.
      * apply md_global,PM_input;now left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq R T) (E_weq V T)) (E_collection_selected T A R U V Theta Z)).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_weq R T).
      * apply tagged_md_left with (b:=E_weq V T),md_hyp;now left.
      * unfold E_collection_root_exclusions. apply tagged_md_left with (b:=E_collection_no_singletons U R Z),
          md_hyp;now right;right;right;left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_collection_selected T A R U V Theta Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_collection_no_singletons U R Z).
      * unfold E_collection_root_exclusions. apply tagged_md_right with (a:=E_wn (E_weq R T)),
          md_hyp;now right;right;right;left.
      * apply md_global;exact HS.
Qed.

Lemma collection_marker_case_program T A B R C U V Theta Z :
  proof_macro nil
    (E_wim (E_weq V T) (E_wim (E_wel V C) (E_wel T C)) :: nil)
    (E_wim (E_collection_marker_exclusions T R U Z)
      (E_wim (E_wa (E_wel V C) (E_collection_choices T A B R T U V Theta Z)) (E_wel T C))).
Proof.
  assert (HS:proof_macro nil
      (E_wim (E_weq V T) (E_wim (E_wel V C) (E_wel T C)) :: nil)
      (E_wim (E_collection_no_singletons U T Z) (E_wn (E_collection_selected T A T U V Theta Z)))).
  { apply collection_empty_inputs,collection_selected_impossible_program. }
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _ (E_wa (E_weq T R) (E_weq V B))
    (E_or (E_wa (E_weq T T) (E_weq V T)) (E_collection_selected T A T U V Theta Z))).
  - apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
    eapply md_mp with (a:=E_weq T R).
    + apply tagged_md_left with (b:=E_weq V B),md_hyp;now left.
    + unfold E_collection_marker_exclusions. apply tagged_md_left with (b:=E_collection_no_singletons U T Z),
        md_hyp;now right;right;left.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq T T) (E_weq V T)) (E_collection_selected T A T U V Theta Z)).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=E_wel V C).
      * apply tagged_md_left with (b:=E_collection_choices T A B R T U V Theta Z),md_hyp;now right;right;left.
      * eapply md_mp with (a:=E_weq V T).
        -- apply tagged_md_right with (a:=E_weq T T),md_hyp;now left.
        -- apply md_global,PM_input;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
      eapply md_mp with (a:=E_collection_selected T A T U V Theta Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_collection_no_singletons U T Z).
      * unfold E_collection_marker_exclusions. apply tagged_md_right with (a:=E_wn (E_weq T R)),
          md_hyp;now right;right;right;left.
      * apply md_global;exact HS.
Qed.

(** This common wrapper consumes actual vacuity proofs for the two formulas
    retained while the output existential is eliminated. *)
Lemma collection_exceptional_request M rho V C Choice Exclusions Output Eligible :
  ns_proof M rho (E_vac V Exclusions) -> ns_proof M rho (E_vac V Output) ->
  ns_proof M rho (E_wim Exclusions (E_wim (E_wa (E_wel V C) Choice) Output)) ->
  ns_proof M rho (E_wex V Choice) ->
  ns_proof M rho (E_wim Exclusions
    (E_wim (E_wim Eligible (E_kp_request V C Choice)) (E_wim Eligible Output))).
Proof.
  intros HVH HVO HPoint HExists.
  assert (HC:ns_proof M rho (E_wim Exclusions (E_wim (E_wex V (E_wa (E_wel V C) Choice)) Output))).
  { apply (ns_proof_macro M rho
      (E_vac V Exclusions :: E_vac V Output ::
       E_wim Exclusions (E_wim (E_wa (E_wel V C) Choice) Output) :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - eapply macro_syl.
      + apply kp0_parameter_exists;apply PM_input;cbn;tauto.
      + apply kp0_implication_map,request_existential_collapse,PM_input;now right;left. }
  apply (ns_proof_macro M rho
    (E_wim Exclusions (E_wim (E_wex V (E_wa (E_wel V C) Choice)) Output) :: E_wex V Choice :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_wex V (E_wa (E_wel V C) Choice)).
    + eapply md_mp with (a:=E_wex V Choice);[apply md_global,PM_input;now right;left|].
      eapply md_mp with (a:=Eligible);[apply md_hyp;now left|apply md_hyp;now right;left].
    + eapply md_mp with (a:=Exclusions);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now left.
Qed.

Lemma collection_root_output_program T A B R U V Theta Z :
  proof_macro nil (E_vac V (E_weq R R) :: E_weq R R :: nil)
    (E_wex V (E_collection_choices T A B R R U V Theta Z)).
Proof.
  assert (H:proof_macro nil (E_vac V (E_weq R R) :: E_weq R R :: nil)
    (E_wim (E_weq R R) (E_wim (E_wex V (E_weq V B))
      (E_wex V (E_collection_choices T A B R R U V Theta Z))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wa (E_weq R R) (E_weq V B));
      [apply kp0_md_conjunction;apply md_hyp;cbn;tauto|].
    apply md_global,PM_template,template_or_left. }
  eapply PM_mp;[exact (PM_template _ (TP_row LR1 V B (CEconst 0) (CEconst 0)))|].
  eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Lemma collection_marker_output_program T A B R U V Theta Z :
  proof_macro nil (E_vac V (E_weq T T) :: E_weq T T :: nil)
    (E_wex V (E_collection_choices T A B R T U V Theta Z)).
Proof.
  assert (H:proof_macro nil (E_vac V (E_weq T T) :: E_weq T T :: nil)
    (E_wim (E_weq T T) (E_wim (E_wex V (E_weq V T))
      (E_wex V (E_collection_choices T A B R T U V Theta Z))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_or (E_wa (E_weq T T) (E_weq V T)) (E_collection_selected T A T U V Theta Z)).
    - eapply md_mp with (a:=E_wa (E_weq T T) (E_weq V T));
        [apply kp0_md_conjunction;apply md_hyp;cbn;tauto|].
      apply md_global,PM_template,template_or_left.
    - apply md_global,PM_template,template_or_right. }
  eapply PM_mp;[exact (PM_template _ (TP_row LR1 V T (CEconst 0) (CEconst 0)))|].
  eapply PM_mp;[apply PM_input;now right;left|exact H].
Qed.

Print Assumptions collection_selected_impossible_program.
Print Assumptions collection_exceptional_request.
Print Assumptions collection_root_case_program.
Print Assumptions collection_marker_case_program.
Print Assumptions collection_root_output_program.
Print Assumptions collection_marker_output_program.

Lemma collection_no_singletons_fresh M rho y U I Z :
  y<>zeroM M -> expression_name_avoids M rho y U ->
  expression_name_avoids M rho y I -> expression_name_avoids M rho y Z ->
  expression_fresh M rho y (E_collection_no_singletons U I Z).
Proof.
  intros H0 HU HI HZ. unfold E_collection_no_singletons,E_raw_singleton.
  apply expression_fresh_universal;[exact HU|].
  apply expression_fresh_negation;[exact H0|].
  apply expression_fresh_conjunction;[exact H0| |].
  - apply expression_fresh_atom;[now left|exact HU|exact HI].
  - apply expression_fresh_universal;[exact HZ|].
    apply expression_fresh_implication;apply expression_fresh_atom;
      [now left|exact HZ|exact HI|now right|exact HZ|exact HU].
Qed.

Theorem numerical_collection_root_request M rho T A B R C U V Theta Z vv :
  code_relation M rho V vv -> vv<>zeroM M ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv B ->
  expression_name_avoids M rho vv R -> expression_name_avoids M rho vv C ->
  expression_name_avoids M rho vv U -> expression_name_avoids M rho vv Z ->
  ns_proof M rho (E_wim (E_collection_root_exclusions T R U Z)
    (E_wim (E_wim (E_kp_eligible R V C R)
      (E_kp_request V C (E_collection_choices T A B R R U V Theta Z)))
      (E_wim (E_kp_eligible R V C R) (E_wel B C)))).
Proof.
  intros HV H0 HT HB HR HC HU HZ. apply collection_exceptional_request.
  - apply (kp0_expression_fresh_vacuity M rho V (E_collection_root_exclusions T R U Z) vv HV).
    unfold E_collection_root_exclusions. apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_negation;[exact H0|].
      apply expression_fresh_atom;[now right|exact HR|exact HT].
    + now apply collection_no_singletons_fresh.
  - apply (kp0_expression_fresh_vacuity M rho V (E_wel B C) vv HV).
    apply expression_fresh_atom;[now left|exact HB|exact HC].
  - apply (ns_proof_macro M rho (E_wim (E_weq V B) (E_wim (E_wel V C) (E_wel B C)) :: nil)).
    + intros e [<-|[]]. apply numerical_tagged_membership_transport.
    + apply collection_root_case_program.
  - apply (ns_proof_macro M rho (E_vac V (E_weq R R) :: E_weq R R :: nil)).
    + intros e [<-|[<-|[]]].
      * apply (kp0_expression_fresh_vacuity M rho V (E_weq R R) vv HV).
        apply expression_fresh_atom;[now right|exact HR|exact HR].
      * apply ns_proof_reflexivity.
    + apply collection_root_output_program.
Qed.

Theorem numerical_collection_marker_request M rho T A B R C U V Theta Z vv :
  code_relation M rho V vv -> vv<>zeroM M ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv R ->
  expression_name_avoids M rho vv C -> expression_name_avoids M rho vv U ->
  expression_name_avoids M rho vv Z ->
  ns_proof M rho (E_wim (E_collection_marker_exclusions T R U Z)
    (E_wim (E_wim (E_kp_eligible R V C T)
      (E_kp_request V C (E_collection_choices T A B R T U V Theta Z)))
      (E_wim (E_kp_eligible R V C T) (E_wel T C)))).
Proof.
  intros HV H0 HT HR HC HU HZ. apply collection_exceptional_request.
  - apply (kp0_expression_fresh_vacuity M rho V (E_collection_marker_exclusions T R U Z) vv HV).
    unfold E_collection_marker_exclusions. apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_negation;[exact H0|].
      apply expression_fresh_atom;[now right|exact HT|exact HR].
    + now apply collection_no_singletons_fresh.
  - apply (kp0_expression_fresh_vacuity M rho V (E_wel T C) vv HV).
    apply expression_fresh_atom;[now left|exact HT|exact HC].
  - apply (ns_proof_macro M rho (E_wim (E_weq V T) (E_wim (E_wel V C) (E_wel T C)) :: nil)).
    + intros e [<-|[]]. apply numerical_tagged_membership_transport.
    + apply collection_marker_case_program.
  - apply (ns_proof_macro M rho (E_vac V (E_weq T T) :: E_weq T T :: nil)).
    + intros e [<-|[<-|[]]].
      * apply (kp0_expression_fresh_vacuity M rho V (E_weq T T) vv HV).
        apply expression_fresh_atom;[now right|exact HT|exact HT].
      * apply ns_proof_reflexivity.
    + apply collection_marker_output_program.
Qed.

Print Assumptions numerical_collection_root_request.
Print Assumptions numerical_collection_marker_request.
