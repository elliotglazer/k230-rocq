(** A genuine input/output pair supplies the selected Collection branch.
    Its existential input is renamed to a fresh private name before use. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedSubstitution NamedBinderFresh TemplateBinderFresh
  TemplateFormulaFresh TemplateNamedSubstitution NumericalKP0 NumericalKP0Eligibility
  NumericalSingleton NumericalTaggedComprehension NumericalVacuitySteps
  TemplatePropositional ProofMacros QuantifierMacros QuotientAtomTemplates
  ContextualPropositional StoppingAlpha StoppingSpecialization
  CollectionSupportCleanup.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_selected_body T A P X V Theta Z :=
  E_wa (E_raw_singleton X P Z)
    (E_wa (E_wa (E_wel T X) (E_wel X A)) (E_wa (E_wel T V) Theta)).

Lemma collection_selected_body_substitution M rho T A P X W V ThetaX ThetaW Z x w z :
  code_relation M rho X x -> code_relation M rho W w -> code_relation M rho Z z ->
  x<>zeroM M -> z<>x -> z<>w ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho x P -> expression_name_avoids M rho x V ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  expression_named_substitution M rho rho x w
    (E_collection_selected_body T A P X V ThetaX Z)
    (E_collection_selected_body T A P W V ThetaW Z).
Proof.
  intros HX HW HZ H0 HZX HZW HT HA HP HV HTheta.
  assert (RX:expression_named_replace M rho rho x w X W).
  { intros a b Ha Hb. rewrite (code_relation_functional M X rho a x Ha HX),
      (code_relation_functional M W rho b w Hb HW). now left. }
  assert (fixed:forall Q,expression_name_avoids M rho x Q -> expression_named_replace M rho rho x w Q Q).
  { intros Q HQ a b Ha Hb. right. split;[exact (HQ a Ha)|].
    symmetry. exact (code_relation_functional M Q rho a b Ha Hb). }
  assert (RT:expression_named_replace M rho rho x w T T) by now apply fixed.
  assert (RA:expression_named_replace M rho rho x w A A) by now apply fixed.
  assert (RP:expression_named_replace M rho rho x w P P) by now apply fixed.
  assert (RV:expression_named_replace M rho rho x w V V) by now apply fixed.
  assert (RZ:expression_named_replace M rho rho x w Z Z).
  { apply fixed. intros a Ha. now rewrite (code_relation_functional M Z rho a z Ha HZ). }
  unfold E_collection_selected_body. apply expression_ns_conjunction;[exact H0| |].
  - unfold E_raw_singleton. apply expression_ns_conjunction;[exact H0| |].
    + apply (expression_ns_atom M rho rho x w false);assumption.
    + apply (expression_ns_universal M rho rho x w Z Z _ _ z HZ HZ HZX HZW).
      apply expression_ns_implication.
      * apply (expression_ns_atom M rho rho x w false);assumption.
      * apply (expression_ns_atom M rho rho x w true);assumption.
  - apply expression_ns_conjunction;[exact H0| |].
    + apply expression_ns_conjunction;[exact H0| |];apply (expression_ns_atom M rho rho x w false);assumption.
    + apply expression_ns_conjunction;[exact H0| |exact HTheta].
      apply (expression_ns_atom M rho rho x w false);assumption.
Qed.

Lemma collection_selected_body_fresh M rho w T A P X V Theta Z :
  w<>zeroM M -> expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_name_avoids M rho w P -> expression_name_avoids M rho w X ->
  expression_name_avoids M rho w V -> expression_name_avoids M rho w Z ->
  expression_fresh M rho w Theta ->
  expression_fresh M rho w (E_collection_selected_body T A P X V Theta Z).
Proof.
  intros H0 HT HA HP HX HV HZ HTheta. unfold E_collection_selected_body.
  apply expression_fresh_conjunction;[exact H0| |].
  - unfold E_raw_singleton. apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_atom;[now left|exact HX|exact HP].
    + apply expression_fresh_universal;[exact HZ|].
      apply expression_fresh_implication;apply expression_fresh_atom;
        [now left|exact HZ|exact HP|now right|exact HZ|exact HX].
  - apply expression_fresh_conjunction;[exact H0| |].
    + apply expression_fresh_conjunction;[exact H0| |];apply expression_fresh_atom;
        [now left|exact HT|exact HX|now left|exact HX|exact HA].
    + apply expression_fresh_conjunction;[exact H0| |exact HTheta].
      apply expression_fresh_atom;[now left|exact HT|exact HV].
Qed.

Theorem numerical_collection_selected_branch M rho T A B R P X W V ThetaX ThetaW Z x w z :
  code_relation M rho X x -> code_relation M rho W w -> code_relation M rho Z z ->
  x<>zeroM M -> w<>zeroM M -> x<>w -> z<>x -> z<>w ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho x P -> expression_name_avoids M rho x V ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_name_avoids M rho w P -> expression_name_avoids M rho w X ->
  expression_name_avoids M rho w V -> expression_name_avoids M rho w Z ->
  expression_fresh M rho w ThetaX ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim (E_collection_selected_body T A P X V ThetaX Z)
    (E_collection_choices T A B R P W V ThetaW Z)).
Proof.
  intros HX HW HZ HX0 HW0 HXW HZX HZW HXT HXA HXP HXV HWT HWA HWP HWX HWV HWZ HTheta HSub.
  set (FX:=E_collection_selected_body T A P X V ThetaX Z).
  set (FW:=E_collection_selected_body T A P W V ThetaW Z).
  destruct (code_relation_total M FX rho) as [f HF].
  destruct (code_relation_total M FW rho) as [g HG].
  assert (HSubBody:expression_named_substitution M rho rho x w FX FW).
  { exact (collection_selected_body_substitution M rho T A P X W V ThetaX ThetaW Z x w z
      HX HW HZ HX0 HZX HZW HXT HXA HXP HXV HSub). }
  assert (HFresh:expression_fresh M rho w FX).
  { exact (collection_selected_body_fresh M rho w T A P X V ThetaX Z HW0 HWT HWA HWP HWX HWV HWZ HTheta). }
  pose proof (proj1 (proj2 (ns_stopping_alpha M rho X W FX FW x w f g
    HX HW HF HG HXW (HFresh f HF) (HSubBody f g HF HG)))) as HA.
  apply (ns_proof_macro M rho
    (E_wim FX (E_wex X FX) :: E_wim (E_wex X FX) (E_wex W FW) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply ns_stopping_self_existential.
    + exact HA.
  - eapply macro_syl;[apply PM_input;now left|].
    eapply macro_syl;[apply PM_input;now right;left|].
    unfold E_collection_choices,E_collection_selected,FW,FX.
    eapply macro_syl;apply PM_template,template_or_right.
Qed.

Theorem numerical_collection_selected_antecedent M rho T A B R P X W V ThetaX ThetaW Z x w v z :
  code_relation M rho X x -> code_relation M rho W w -> code_relation M rho V v -> code_relation M rho Z z ->
  x<>zeroM M -> w<>zeroM M -> v<>zeroM M -> x<>w -> z<>x -> z<>w ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho x P -> expression_name_avoids M rho x V ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_name_avoids M rho w P -> expression_name_avoids M rho w X ->
  expression_name_avoids M rho w V -> expression_name_avoids M rho w Z ->
  expression_name_avoids M rho v T -> expression_name_avoids M rho v A ->
  expression_name_avoids M rho v P -> expression_name_avoids M rho v X ->
  expression_name_avoids M rho v Z ->
  expression_fresh M rho w ThetaX -> expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim (E_wa (E_raw_singleton X P Z) (E_wa (E_wel T X) (E_wel X A)))
    (E_wim (E_wex V (E_wa (E_wel T V) ThetaX))
      (E_wex V (E_collection_choices T A B R P W V ThetaW Z)))).
Proof.
  intros HX HW HV HZ HX0 HW0 HV0 HXW HZX HZW HXT HXA HXP HXV HWT HWA HWP HWX HWV HWZ
    HVT HVA HVP HVX HVZ HTheta HSub.
  set (H:=E_wa (E_raw_singleton X P Z) (E_wa (E_wel T X) (E_wel X A))).
  assert (HP:ns_proof M rho (E_wim H (E_wim (E_wa (E_wel T V) ThetaX)
    (E_collection_choices T A B R P W V ThetaW Z)))).
  { apply (ns_proof_macro M rho
      (E_wim (E_collection_selected_body T A P X V ThetaX Z)
        (E_collection_choices T A B R P W V ThetaW Z) :: nil)).
    - intros e [<-|[]]. exact (numerical_collection_selected_branch M rho T A B R P X W V ThetaX ThetaW Z x w z
        HX HW HZ HX0 HW0 HXW HZX HZW HXT HXA HXP HXV HWT HWA HWP HWX HWV HWZ HTheta HSub).
    - apply macro_discharge. do 2 apply macro_deduction.
      eapply md_mp with (a:=E_collection_selected_body T A P X V ThetaX Z).
      + unfold E_collection_selected_body. apply kp0_md_conjunction.
        * unfold H. apply tagged_md_left with (b:=E_wa (E_wel T X) (E_wel X A)),md_hyp;now right;left.
        * apply kp0_md_conjunction.
          -- unfold H. apply tagged_md_right with (a:=E_raw_singleton X P Z),md_hyp;now right;left.
          -- apply md_hyp;now left.
      + apply md_global,PM_input;now left. }
  apply (ns_proof_macro M rho (E_vac V H ::
    E_wim H (E_wim (E_wa (E_wel T V) ThetaX) (E_collection_choices T A B R P W V ThetaW Z)) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply (kp0_expression_fresh_vacuity M rho V H v HV).
      unfold H,E_raw_singleton. apply expression_fresh_conjunction;[exact HV0| |].
      * apply expression_fresh_conjunction;[exact HV0| |].
        -- apply expression_fresh_atom;[now left|exact HVX|exact HVP].
        -- apply expression_fresh_universal;[exact HVZ|].
           apply expression_fresh_implication;apply expression_fresh_atom;
             [now left|exact HVZ|exact HVP|now right|exact HVZ|exact HVX].
      * apply expression_fresh_conjunction;[exact HV0| |];apply expression_fresh_atom;
          [now left|exact HVT|exact HVX|now left|exact HVX|exact HVA].
    + exact HP.
  - apply kp0_parameter_exists;apply PM_input;cbn;tauto.
Qed.

Print Assumptions collection_selected_body_substitution.
Print Assumptions numerical_collection_selected_branch.
Print Assumptions numerical_collection_selected_antecedent.
