(** Weak, proved vacuity is enough for the arbitrary matrix hole.  All
    other Collection-frame components have finite syntactic freshness. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalVacuitySteps TemplateFormulaFresh FormulaFreshConstructors
  NumericalSingleton NumericalRawPair NumericalRawEnvelope RawMarkerExclusions
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests ProofMacros QuantifierMacros
  QuotientAtomTemplates CollectionSupportCleanup CollectionKernel CollectionFramePoint
  CollectionFrameFresh.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_frame_vacuity_implication M rho X A B :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X B) ->
  ns_proof M rho (E_vac X (E_wim A B)).
Proof.
  intros HA HB. apply (ns_proof_macro M rho (E_vac X A :: E_vac X B :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_vacuous_implication;apply PM_input;cbn;tauto.
Qed.

Lemma collection_frame_vacuity_negation M rho X A :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X (E_wn A)).
Proof.
  intro HA. apply (ns_proof_macro M rho (E_vac X A :: nil)).
  - intros e [<-|[]];assumption.
  - apply macro_vacuous_negation,PM_input;now left.
Qed.

Lemma collection_frame_vacuity_conjunction M rho X A B :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X B) ->
  ns_proof M rho (E_vac X (E_wa A B)).
Proof.
  intros HA HB. apply (ns_proof_macro M rho (E_vac X A :: E_vac X B :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply kp0_vacuous_conjunction;apply PM_input;cbn;tauto.
Qed.

Lemma collection_frame_vacuity_disjunction M rho X A B :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X B) ->
  ns_proof M rho (E_vac X (E_or A B)).
Proof.
  intros HA HB. unfold E_or. apply collection_frame_vacuity_implication;
    [now apply collection_frame_vacuity_negation|exact HB].
Qed.

Lemma collection_frame_vacuity_universal M rho X Y A :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X (E_wal Y A)).
Proof.
  intro HA. apply (ns_proof_macro M rho (E_vac X A :: nil)).
  - intros e [<-|[]];assumption.
  - apply macro_vacuous_universal,PM_input;now left.
Qed.

Lemma collection_frame_vacuity_existential M rho X Y A :
  ns_proof M rho (E_vac X A) -> ns_proof M rho (E_vac X (E_wex Y A)).
Proof.
  intro HA. apply (ns_proof_macro M rho (E_vac X A :: nil)).
  - intros e [<-|[]];assumption.
  - apply kp0_vacuous_exists,PM_input;now left.
Qed.

Ltac collection_frame_weak_vacuity HX :=
  first [assumption |
    apply collection_frame_vacuity_conjunction;
      [collection_frame_weak_vacuity HX|collection_frame_weak_vacuity HX] |
    apply collection_frame_vacuity_disjunction;
      [collection_frame_weak_vacuity HX|collection_frame_weak_vacuity HX] |
    apply collection_frame_vacuity_negation;collection_frame_weak_vacuity HX |
    apply collection_frame_vacuity_implication;
      [collection_frame_weak_vacuity HX|collection_frame_weak_vacuity HX] |
    apply collection_frame_vacuity_universal;collection_frame_weak_vacuity HX |
    apply collection_frame_vacuity_existential;collection_frame_weak_vacuity HX |
    eapply kp0_expression_fresh_vacuity;[exact HX|collection_frame_fresh]].

Theorem numerical_collection_frame_vacuity M rho X T A B R C I W V Theta Z Q x :
  code_relation M rho X x -> x<>zeroM M ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho x B -> expression_name_avoids M rho x R ->
  expression_name_avoids M rho x C -> expression_name_avoids M rho x I ->
  expression_name_avoids M rho x W -> expression_name_avoids M rho x V ->
  expression_name_avoids M rho x Z -> expression_name_avoids M rho x Q ->
  ns_proof M rho (E_vac X Theta) ->
  ns_proof M rho (E_vac X (E_collection_frame T A B R C I W V Theta Z Q)).
Proof.
  intros HX H0 HT HA HB HR HC HI HW HV HZ HQ HF.
  unfold E_collection_frame,collection_frame_fields.
  cbn [E_collection_bundle].
  unfold E_marker_empty,E_raw_pair,E_raw_envelope,E_raw_singleton,
    E_collection_requests,E_collection_choices,E_collection_selected,
    E_kp_eligible,E_kp_request,E_ksubset.
  collection_frame_weak_vacuity HX.
Qed.

Print Assumptions collection_frame_vacuity_implication.
Print Assumptions numerical_collection_frame_vacuity.
