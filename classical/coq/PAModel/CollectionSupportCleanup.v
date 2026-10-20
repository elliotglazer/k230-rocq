(** The support direction of KCollection's binary matrix. The raw KP0
    support clause remains a visible input; no collection certificate is
    assumed. Root and marker outputs are eliminated by their domain facts. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates TemplateCD
  TemplatePropositional ProofMacros QuantifierMacros NamedLeibnizSteps NumericalKP0
  NumericalKP0Eligibility NumericalSingleton NumericalTaggedComprehension NumericalBootstrap
  QuotientAtomTemplates TemplateFormulaFresh ContextualPropositional RawMarkerExclusions
  RawMarkerQuantifiers BoundVariableVacuityRules RawCollectionProfile NumericalVacuitySteps
  StoppingSpecialization.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_selected T A P U V Theta Z :=
  E_wex U (E_wa (E_raw_singleton U P Z)
    (E_wa (E_wa (E_wel T U) (E_wel U A)) (E_wa (E_wel T V) Theta))).
Definition E_collection_choices T A B R P U V Theta Z :=
  E_or (E_wa (E_weq P R) (E_weq V B))
    (E_or (E_wa (E_weq P T) (E_weq V T)) (E_collection_selected T A P U V Theta Z)).
Definition E_collection_raw_support T A B R C P U V Theta Z :=
  E_wal V (E_wim (E_wel V C) (E_wex P (E_collection_choices T A B R P U V Theta Z))).
Definition E_collection_support_target T A U Theta :=
  E_wex U (E_wa (E_wa (E_wel T U) (E_wel U A)) Theta).

Lemma collection_selected_projection_program T A P U V Theta Z :
  proof_macro nil nil (E_wim (E_collection_selected T A P U V Theta Z)
    (E_collection_support_target T A U Theta)).
Proof.
  unfold E_collection_selected,E_collection_support_target. apply macro_exists_monotone.
  apply macro_discharge,macro_deduction,kp0_md_conjunction.
  - apply tagged_md_left with (b:=E_wa (E_wel T V) Theta).
    apply tagged_md_right with (a:=E_raw_singleton U P Z),md_hyp;now left.
  - apply tagged_md_right with (a:=E_wel T V).
    apply tagged_md_right with (a:=E_wa (E_wel T U) (E_wel U A)).
    apply tagged_md_right with (a:=E_raw_singleton U P Z),md_hyp;now left.
Qed.

Lemma collection_empty_inputs G inputs e :
  proof_macro G nil e -> proof_macro G inputs e.
Proof.
  intro HP. induction HP.
  - now apply PM_template.
  - inversion H.
  - exact (PM_mp _ _ IHHP1 IHHP2).
  - exact (PM_gen _ _ IHHP).
Qed.

Lemma collection_support_target_fresh M rho T A U Theta pv :
  pv<>zeroM M -> expression_name_avoids M rho pv T ->
  expression_name_avoids M rho pv A -> expression_name_avoids M rho pv U ->
  expression_fresh M rho pv Theta ->
  expression_fresh M rho pv (E_collection_support_target T A U Theta).
Proof.
  intros H0 HT HA HU HTheta. unfold E_collection_support_target.
  apply expression_fresh_existential;[exact H0|exact HU|].
  apply expression_fresh_conjunction;[exact H0| |exact HTheta].
  apply expression_fresh_conjunction;[exact H0| |];
    apply expression_fresh_atom;[now left|exact HT|exact HU|now left|exact HU|exact HA].
Qed.

Theorem numerical_collection_choices_support M rho T A B R P U V Theta Z pv :
  code_relation M rho P pv -> pv<>zeroM M ->
  expression_name_avoids M rho pv T -> expression_name_avoids M rho pv A ->
  expression_name_avoids M rho pv B -> expression_name_avoids M rho pv U ->
  expression_name_avoids M rho pv V -> expression_fresh M rho pv Theta ->
  ns_proof M rho (E_wim (E_wn (E_wel T B)) (E_wim (E_wn (E_wel T T))
    (E_wim (E_wel T V) (E_wim (E_wex P (E_collection_choices T A B R P U V Theta Z))
      (E_collection_support_target T A U Theta))))).
Proof.
  intros HP H0 HT HA HB HU HV HTheta.
  set (Target:=E_collection_support_target T A U Theta).
  set (N:=E_wim (E_wn (E_wel T B)) (E_wim (E_wn (E_wel T T)) (E_wim (E_wel T V) Target))).
  assert (HN:ns_proof M rho (E_vac P N)).
  { apply (kp0_expression_fresh_vacuity M rho P N pv HP).
    unfold N. apply expression_fresh_implication.
    - apply expression_fresh_negation;[exact H0|]. apply expression_fresh_atom;[now left|exact HT|exact HB].
    - apply expression_fresh_implication.
      + apply expression_fresh_negation;[exact H0|]. apply expression_fresh_atom;[now left|exact HT|exact HT].
      + apply expression_fresh_implication.
        * apply expression_fresh_atom;[now left|exact HT|exact HV].
        * apply collection_support_target_fresh;assumption. }
  assert (HCase:ns_proof M rho (E_wim (E_collection_choices T A B R P U V Theta Z) N)).
  { apply (ns_proof_macro M rho
      (E_wim (E_weq V B) (E_wim (E_wel T V) (E_wel T B)) ::
       E_wim (E_weq V T) (E_wim (E_wel T V) (E_wel T T)) :: nil)).
    - intros e [<-|[<-|[]]];apply marker_membership_transport.
    - unfold E_collection_choices. apply tagged_or_cases.
      + apply macro_discharge. do 4 apply macro_deduction.
        eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
        eapply md_mp with (a:=E_wel T B).
        * eapply md_mp with (a:=E_wel T V);[apply md_hyp;now left|].
          eapply md_mp with (a:=E_weq V B).
          -- apply tagged_md_right with (a:=E_weq P R),md_hyp;now right;right;right;left.
          -- apply md_global,PM_input;now left.
        * apply md_hyp;now right;right;left.
      + apply tagged_or_cases.
        * apply macro_discharge. do 4 apply macro_deduction.
          eapply md_mp with (a:=CEconst 1);[|apply md_global,PM_template,template_F].
          eapply md_mp with (a:=E_wel T T).
          -- eapply md_mp with (a:=E_wel T V);[apply md_hyp;now left|].
             eapply md_mp with (a:=E_weq V T).
             ++ apply tagged_md_right with (a:=E_weq P T),md_hyp;now right;right;right;left.
             ++ apply md_global,PM_input;now right;left.
          -- apply md_hyp;now right;left.
        * apply macro_discharge. do 4 apply macro_deduction.
          eapply md_mp with (a:=E_collection_selected T A P U V Theta Z).
          -- apply md_hyp;now right;right;right;left.
          -- apply md_global,collection_empty_inputs,collection_selected_projection_program. }
  assert (HElim:ns_proof M rho (E_wim (E_wex P (E_collection_choices T A B R P U V Theta Z)) N)).
  { apply (ns_proof_macro M rho (E_vac P N :: E_wim (E_collection_choices T A B R P U V Theta Z) N :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply kp0_exists_eliminate;apply PM_input;cbn;tauto. }
  apply (ns_proof_macro M rho (E_wim (E_wex P (E_collection_choices T A B R P U V Theta Z)) N :: nil)).
  - intros e [<-|[]]. exact HElim.
  - unfold N. apply macro_discharge. do 4 apply macro_deduction.
    eapply md_mp with (a:=E_wel T V);[apply md_hyp;now right;left|].
    eapply md_mp with (a:=E_wn (E_wel T T));[apply md_hyp;now right;right;left|].
    eapply md_mp with (a:=E_wn (E_wel T B));[apply md_hyp;now right;right;right;left|].
    eapply md_mp with (a:=E_wex P (E_collection_choices T A B R P U V Theta Z));[apply md_hyp;now left|].
    apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_collection_choices_support.

(** Generalize before introducing the empty-marker hypothesis.  In particular,
    the output name need not differ from the marker's own bound test name. *)
Theorem numerical_collection_support_from_exclusions M rho T A B R C P U V Theta Z pv vv :
  code_relation M rho P pv -> code_relation M rho V vv ->
  pv<>zeroM M -> vv<>zeroM M ->
  expression_name_avoids M rho pv T -> expression_name_avoids M rho pv A ->
  expression_name_avoids M rho pv B -> expression_name_avoids M rho pv U ->
  expression_name_avoids M rho pv V -> expression_fresh M rho pv Theta ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv B ->
  ns_proof M rho (E_wim (E_wa (E_wn (E_wel T B)) (E_wn (E_wel T T)))
    (E_wim (E_collection_raw_support T A B R C P U V Theta Z)
      (E_wal V (E_raw_collection_support T A C U V Theta)))).
Proof.
  intros HP HV HP0 HV0 HTP HAP HBP HUP HVP HTheta HTV HBV.
  apply marker_generalize_two.
  - apply (kp0_expression_fresh_vacuity M rho V
      (E_wa (E_wn (E_wel T B)) (E_wn (E_wel T T))) vv HV).
    apply expression_fresh_conjunction;[exact HV0| |];
      apply expression_fresh_negation;try exact HV0;
      apply expression_fresh_atom;[now left|exact HTV|exact HBV|now left|exact HTV|exact HTV].
  - unfold E_collection_raw_support. apply ns_bound_universal_vacuity.
  - apply (ns_proof_macro M rho
      (E_wim (E_wn (E_wel T B)) (E_wim (E_wn (E_wel T T))
         (E_wim (E_wel T V) (E_wim (E_wex P (E_collection_choices T A B R P U V Theta Z))
           (E_collection_support_target T A U Theta)))) ::
       E_wim (E_collection_raw_support T A B R C P U V Theta Z)
         (E_wim (E_wel V C) (E_wex P (E_collection_choices T A B R P U V Theta Z))) :: nil)).
    + intros e [<-|[<-|[]]].
      * exact (numerical_collection_choices_support M rho T A B R P U V Theta Z pv
          HP HP0 HTP HAP HBP HUP HVP HTheta).
      * unfold E_collection_raw_support. apply ns_stopping_self_specialization.
    + unfold E_raw_collection_support. apply macro_discharge. do 3 apply macro_deduction.
      eapply md_mp with (a:=E_wex P (E_collection_choices T A B R P U V Theta Z)).
      * eapply md_mp with (a:=E_wel V C).
        -- apply tagged_md_right with (a:=E_wel T V),md_hyp;now left.
        -- eapply md_mp with (a:=E_collection_raw_support T A B R C P U V Theta Z).
           ++ apply md_hyp;now right;left.
           ++ apply md_global,PM_input;now right;left.
      * eapply md_mp with (a:=E_wel T V).
        -- apply tagged_md_left with (b:=E_wel V C),md_hyp;now left.
        -- eapply md_mp with (a:=E_wn (E_wel T T)).
           ++ apply tagged_md_right with (a:=E_wn (E_wel T B)),md_hyp;now right;right;left.
           ++ eapply md_mp with (a:=E_wn (E_wel T B)).
              ** apply tagged_md_left with (b:=E_wn (E_wel T T)),md_hyp;now right;right;left.
              ** apply md_global,PM_input;now left.
Qed.

Theorem numerical_collection_support_cleanup M rho T A B R C P U V Theta Z Zempty tv pv vv zev :
  code_relation M rho T tv -> code_relation M rho P pv -> code_relation M rho V vv ->
  code_relation M rho Zempty zev ->
  pv<>zeroM M -> vv<>zeroM M -> zev<>zeroM M -> tv<>zev ->
  expression_name_avoids M rho pv T -> expression_name_avoids M rho pv A ->
  expression_name_avoids M rho pv B -> expression_name_avoids M rho pv U ->
  expression_name_avoids M rho pv V -> expression_fresh M rho pv Theta ->
  expression_name_avoids M rho vv T -> expression_name_avoids M rho vv B ->
  ns_proof M rho (E_wim (E_marker_empty T Zempty)
    (E_wim (E_wn (E_wel T B))
      (E_wim (E_collection_raw_support T A B R C P U V Theta Z)
        (E_wal V (E_raw_collection_support T A C U V Theta))))).
Proof.
  intros HT HP HV HZ HP0 HV0 HZ0 HTZ HTP HAP HBP HUP HVP HTheta HTV HBV.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Zempty) (E_wn (E_wel T T)) ::
     E_wim (E_wa (E_wn (E_wel T B)) (E_wn (E_wel T T)))
       (E_wim (E_collection_raw_support T A B R C P U V Theta Z)
         (E_wal V (E_raw_collection_support T A C U V Theta))) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (marker_empty_specialization M rho T Zempty T tv zev tv HT HZ HT HZ0
        (fun E=>HTZ (Logic.eq_sym E)) HTZ).
    + exact (numerical_collection_support_from_exclusions M rho T A B R C P U V Theta Z pv vv
        HP HV HP0 HV0 HTP HAP HBP HUP HVP HTheta HTV HBV).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_collection_raw_support T A B R C P U V Theta Z).
    + apply md_hyp;now left.
    + eapply md_mp with (a:=E_wa (E_wn (E_wel T B)) (E_wn (E_wel T T))).
      * apply kp0_md_conjunction.
        -- apply md_hyp;now right;left.
        -- eapply md_mp with (a:=E_marker_empty T Zempty).
           ++ apply md_hyp;now right;right;left.
           ++ apply md_global,PM_input;now left.
      * apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_collection_support_from_exclusions.
Print Assumptions numerical_collection_support_cleanup.
