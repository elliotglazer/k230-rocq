(** Every side condition for selected-output cleanup is discharged from
    explicit fresh names and the original input-to-witness substitution. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalSingleton NumericalKP0Eligibility NumericalVacuitySteps
  TemplateFormulaFresh TemplateBinderFresh TemplateNamedSubstitution NamedBinderFresh
  CollectionInputReverse CollectionSelectedCleanup QuotientAtomTemplates.
Unset Implicit Arguments.

Lemma collection_singleton_fresh M rho name X P Z :
  name<>zeroM M -> expression_name_avoids M rho name X ->
  expression_name_avoids M rho name P -> expression_name_avoids M rho name Z ->
  expression_fresh M rho name (E_raw_singleton X P Z).
Proof.
  intros H0 HX HP HZ. unfold E_raw_singleton.
  apply expression_fresh_conjunction;[exact H0| |].
  - apply expression_fresh_atom;[now left|exact HX|exact HP].
  - apply expression_fresh_universal;[exact HZ|].
    apply expression_fresh_implication;apply expression_fresh_atom;
      [now left|exact HZ|exact HP|now right|exact HZ|exact HX].
Qed.

Theorem numerical_collection_selected_cleanup_checked M rho T A B R C X P W V ThetaW ThetaX Z x p w v z :
  code_relation M rho X x -> code_relation M rho P p -> code_relation M rho W w ->
  code_relation M rho V v -> code_relation M rho Z z ->
  w<>zeroM M -> v<>zeroM M -> z<>w -> p<>z -> x<>z ->
  expression_name_avoids M rho w X -> expression_name_avoids M rho w P ->
  expression_name_avoids M rho w Z -> expression_name_avoids M rho w V ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w C ->
  expression_name_avoids M rho v X -> expression_name_avoids M rho v P ->
  expression_name_avoids M rho v Z -> expression_name_avoids M rho v T ->
  expression_name_avoids M rho v R ->
  expression_fresh M rho w ThetaX ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim (E_collection_selected_hyp T R X P Z)
    (E_wim (E_wex V (E_wa (E_wel V C)
      (CollectionSupportCleanup.E_collection_choices T A B R P W V ThetaW Z)))
      (E_wex V (E_collection_selected_result T C V ThetaX)))).
Proof.
  intros HX HP HW HV HZ HW0 HV0 HZW HPZ HXZ HWX HWP HWZ HWV HWT HWC
    HVX HVP HVZ HVT HVR HTheta HSub.
  apply numerical_collection_selected_cleanup.
  - apply (kp0_expression_fresh_vacuity M rho W
      (E_wa (E_raw_singleton X P Z) (E_wel V C)) w HW).
    apply expression_fresh_conjunction;[exact HW0| |].
    + now apply collection_singleton_fresh.
    + apply expression_fresh_atom;[now left|exact HWV|exact HWC].
  - apply (kp0_expression_fresh_vacuity M rho W (E_collection_selected_result T C V ThetaX) w HW).
    unfold E_collection_selected_result. apply expression_fresh_conjunction;[exact HW0| |].
    + apply expression_fresh_atom;[now left|exact HWT|exact HWV].
    + apply expression_fresh_conjunction;[exact HW0| |exact HTheta].
      apply expression_fresh_atom;[now left|exact HWV|exact HWC].
  - apply (numerical_singleton_input_congruence_reverse M rho X W P Z ThetaX ThetaW x w p z
      HX HW HP HZ HZW HPZ HXZ).
    + intros f HF. exact (named_formula_fresh_binder_absent M f w (HTheta f HF)).
    + exact HSub.
  - apply (kp0_expression_fresh_vacuity M rho V (E_collection_selected_hyp T R X P Z) v HV).
    unfold E_collection_selected_hyp. apply expression_fresh_conjunction;[exact HV0| |].
    + now apply collection_singleton_fresh.
    + apply expression_fresh_conjunction;[exact HV0| |];apply expression_fresh_negation;try exact HV0;
        apply expression_fresh_atom;[now right|exact HVP|exact HVR|now right|exact HVP|exact HVT].
Qed.

Print Assumptions numerical_collection_selected_cleanup_checked.
