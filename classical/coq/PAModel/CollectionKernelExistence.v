(** Existentially map the actual K kernel to the raw Collection profile,
    retaining one object-level outer context throughout. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros QuantifierMacros NamedLeibnizSteps NumericalKP0 NumericalKP0Eligibility
  NumericalVacuitySteps TemplateFormulaFresh FormulaFreshConstructors
  NumericalSingleton NumericalRawPair NumericalRawEnvelope RawMarkerExclusions
  CollectionFramePoint CollectionFrameFresh CollectionKernelProfile.
Unset Implicit Arguments.

Lemma numerical_collection_container_map M rho C Outer Step Profile :
  ns_proof M rho (E_wim Outer (E_wim Step Profile)) ->
  ns_proof M rho (E_vac C Outer) ->
  ns_proof M rho (E_wex C Step) ->
  ns_proof M rho (E_wim Outer (E_wex C Profile)).
Proof.
  intros HStep HV HK.
  apply (ns_proof_macro M rho
    (E_wim Outer (E_wim Step Profile)::E_vac C Outer::E_wex C Step::nil)).
  - intros e [<-|[<-|[<-|[]]]];assumption.
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_wex C Step);[apply md_global,PM_input;now right;right;left|].
    eapply md_mp with (a:=Outer);[apply md_hyp;now left|].
    apply md_global,kp0_parameter_exists;apply PM_input;cbn;tauto.
Qed.

Lemma collection_outer_fresh M rho T A B R Z Q y :
  y<>zeroM M -> expression_name_avoids M rho y T ->
  expression_name_avoids M rho y A -> expression_name_avoids M rho y B ->
  expression_name_avoids M rho y R -> expression_name_avoids M rho y Z ->
  expression_name_avoids M rho y Q ->
  expression_fresh M rho y (E_collection_outer T A B R Z Q).
Proof.
  intros H0 HT HA HB HR HZ HQ.
  unfold E_collection_outer,collection_outer_fields. cbn [E_collection_bundle].
  unfold E_marker_empty,E_raw_pair,E_raw_envelope.
  collection_frame_fresh.
Qed.

Print Assumptions numerical_collection_container_map.
Print Assumptions collection_outer_fresh.
