(** Remove the arbitrary relation from the exceptional requests before
    specializing at the marker.  This permits arbitrary bound marker names
    in Theta; no replacement-freshness assumption on Theta is needed. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps TemplateCD TemplatePropositional ProofMacros QuantifierMacros
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility NumericalBootstrap
  NumericalSingleton NumericalTaggedComprehension QuotientAtomTemplates
  ContextualPropositional CollectionSupportCleanup CollectionKernel.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_collection_first_two T B R P V :=
  E_or (E_wa (E_weq P R) (E_weq V B)) (E_wa (E_weq P T) (E_weq V T)).
Definition E_collection_summary T B R P U V Z :=
  E_or (E_wa (E_weq P R) (E_weq V B))
    (E_or (E_wa (E_weq P T) (E_weq V T)) (E_wex U (E_raw_singleton U P Z))).
Definition E_collection_reduced_request T B R C P U V Z :=
  E_wim (E_wex V (E_collection_first_two T B R P V))
    (E_wex V (E_wa (E_wel V C) (E_collection_summary T B R P U V Z))).
Definition E_collection_reduced_requests T B R C P U V Z :=
  E_wal P (E_wim (E_kp_eligible R V C P)
    (E_collection_reduced_request T B R C P U V Z)).

Lemma collection_first_two_inclusion T A B R P U V Theta Z :
  proof_macro nil nil (E_wim (E_collection_first_two T B R P V)
    (E_collection_choices T A B R P U V Theta Z)).
Proof.
  unfold E_collection_first_two,E_collection_choices. apply tagged_or_cases.
  - apply PM_template,template_or_left.
  - eapply macro_syl;[apply PM_template,template_or_left|apply PM_template,template_or_right].
Qed.

Lemma collection_summary_projection T A B R P U V Theta Z :
  proof_macro nil nil (E_wim (E_collection_choices T A B R P U V Theta Z)
    (E_collection_summary T B R P U V Z)).
Proof.
  unfold E_collection_choices,E_collection_summary. apply tagged_or_cases.
  - apply PM_template,template_or_left.
  - eapply macro_syl;[|apply PM_template,template_or_right].
    apply tagged_or_cases.
    + apply PM_template,template_or_left.
    + eapply macro_syl;[|apply PM_template,template_or_right].
      unfold E_collection_selected. apply macro_exists_monotone,PM_template,bootstrap_projection_left.
Qed.

Lemma collection_reduced_request_program T A B R C P U V Theta Z :
  proof_macro nil nil (E_wim
    (E_kp_request V C (E_collection_choices T A B R P U V Theta Z))
    (E_collection_reduced_request T B R C P U V Z)).
Proof.
  set (F:=E_collection_first_two T B R P V).
  set (M:=E_collection_choices T A B R P U V Theta Z).
  set (S:=E_collection_summary T B R P U V Z).
  assert (HIn:proof_macro nil nil (E_wim (E_wex V F) (E_wex V M))).
  { apply macro_exists_monotone,collection_first_two_inclusion. }
  assert (HOut:proof_macro nil nil
    (E_wim (E_wex V (E_wa (E_wel V C) M)) (E_wex V (E_wa (E_wel V C) S)))).
  { apply macro_exists_monotone,macro_discharge,macro_deduction,kp0_md_conjunction.
    - apply tagged_md_left with (b:=M),md_hyp;now left.
    - eapply md_mp with (a:=M).
      + apply tagged_md_right with (a:=E_wel V C),md_hyp;now left.
      + apply md_global,collection_summary_projection. }
  unfold E_kp_request,E_collection_reduced_request. apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=E_wex V (E_wa (E_wel V C) M));[|apply md_global;exact HOut].
  eapply md_mp with (a:=E_wex V M);[|apply md_hyp;now right;left].
  eapply md_mp with (a:=E_wex V F);[apply md_hyp;now left|apply md_global;exact HIn].
Qed.

Theorem numerical_collection_reduced_requests M rho T A B R C P U V Theta Z :
  ns_proof M rho (E_wim (E_collection_requests T A B R C P U V Theta Z)
    (E_collection_reduced_requests T B R C P U V Z)).
Proof.
  apply (ns_proof_macro M rho nil);[intros e []|].
  unfold E_collection_requests,E_collection_reduced_requests.
  apply macro_all_monotone,kp0_implication_map,collection_reduced_request_program.
Qed.

Print Assumptions collection_first_two_inclusion.
Print Assumptions collection_summary_projection.
Print Assumptions collection_reduced_request_program.
Print Assumptions numerical_collection_reduced_requests.
