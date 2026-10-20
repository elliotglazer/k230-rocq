(** Full name freshness of the finite Collection frame, keeping its
    arbitrary matrix as an explicit hole. *)
From PAModel Require Import Model CodeExpressions NumericalProofs
  TemplateFormulaFresh FormulaFreshConstructors NumericalSingleton NumericalRawPair
  NumericalRawEnvelope RawMarkerExclusions NumericalKP0Eligibility NumericalKP0Requests
  QuotientAtomTemplates CollectionSupportCleanup CollectionKernel CollectionFramePoint.
Unset Implicit Arguments.

Ltac collection_frame_fresh :=
  first [assumption |
    apply expression_fresh_conjunction;[assumption|collection_frame_fresh|collection_frame_fresh] |
    apply expression_fresh_disjunction;[assumption|collection_frame_fresh|collection_frame_fresh] |
    apply expression_fresh_negation;[assumption|collection_frame_fresh] |
    apply expression_fresh_implication;[collection_frame_fresh|collection_frame_fresh] |
    apply expression_fresh_universal;[assumption|collection_frame_fresh] |
    apply expression_fresh_existential;[assumption|assumption|collection_frame_fresh] |
    apply expression_fresh_atom;[now left|assumption|assumption] |
    apply expression_fresh_atom;[now right|assumption|assumption] |
    apply expression_fresh_one;assumption |
    intros v Hv;change (v=zeroM _) in Hv;subst v;apply formula_fresh_zero].

Theorem collection_frame_expression_fresh M rho T A B R C I W V Theta Z Q y :
  y<>zeroM M ->
  expression_name_avoids M rho y T -> expression_name_avoids M rho y A ->
  expression_name_avoids M rho y B -> expression_name_avoids M rho y R ->
  expression_name_avoids M rho y C -> expression_name_avoids M rho y I ->
  expression_name_avoids M rho y W -> expression_name_avoids M rho y V ->
  expression_name_avoids M rho y Z -> expression_name_avoids M rho y Q ->
  expression_fresh M rho y Theta ->
  expression_fresh M rho y (E_collection_frame T A B R C I W V Theta Z Q).
Proof.
  intros H0 HT HA HB HR HC HI HW HV HZ HQ HF.
  unfold E_collection_frame,collection_frame_fields.
  cbn [E_collection_bundle].
  unfold E_marker_empty,E_raw_pair,E_raw_envelope,E_raw_singleton,
    E_collection_requests,E_collection_choices,E_collection_selected,
    E_kp_eligible,E_kp_request,E_ksubset.
  collection_frame_fresh.
Qed.

Print Assumptions collection_frame_expression_fresh.
