(** The full request family puts the envelope and empty marker in the same
    container. The exception exclusions remain visible object hypotheses. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedAlpha ProofMacros QuantifierMacros TemplatePropositional
  NumericalKP0 NumericalKP0Eligibility NumericalSingleton NumericalTaggedComprehension
  RawMarkerExclusions RawMarkerQuantifiers TemplateFormulaFresh
  TaggedSubsetFacts TaggedEligibility CollectionKernel CollectionRequestProjection
  CollectionRequestSpecialization CollectionSummaryWitness CollectionExceptionalRequests
  CollectionCoverageNumerical.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem numerical_collection_root_from_requests M rho T A B R C P W V Theta Z
    t b r c p w v z :
  code_relation M rho T t -> code_relation M rho B b -> code_relation M rho R r ->
  code_relation M rho C c -> code_relation M rho P p -> code_relation M rho W w ->
  code_relation M rho V v -> code_relation M rho Z z ->
  NoDup [t;b;r;c;p;w;v;z] -> p<>zeroM M -> v<>zeroM M ->
  ns_proof M rho (E_wim (E_collection_root_exclusions T R W Z)
    (E_wim (E_collection_requests T A B R C P W V Theta Z) (E_wel B C))).
Proof.
  intros HT HB HR HC HP HW HV HZ HND HP0 HV0.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  assert (HSpec:ns_proof M rho (E_wim (E_collection_requests T A B R C P W V Theta Z)
    (E_collection_reduced_at T B R C R W V Z))).
  { eapply ns_proof_syl;[apply numerical_collection_reduced_requests|].
    apply (numerical_collection_reduced_specialization M rho T B R C P R W V Z p r c w v z);
      try assumption;collection_discharge_name. }
  assert (HLocal:ns_proof M rho (E_wim (E_collection_root_exclusions T R W Z)
    (E_wim (E_collection_reduced_at T B R C R W V Z) (E_wel B C)))).
  { apply (numerical_collection_summary_root_request M rho T B R C W V Z v);
      try assumption;collection_discharge_name. }
  apply (ns_proof_macro M rho
    (E_wim (E_collection_requests T A B R C P W V Theta Z) (E_collection_reduced_at T B R C R W V Z) ::
     E_wim (E_collection_root_exclusions T R W Z) (E_wim (E_collection_reduced_at T B R C R W V Z) (E_wel B C)) :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_collection_reduced_at T B R C R W V Z).
    + eapply md_mp with (a:=E_collection_requests T A B R C P W V Theta Z);[apply md_hyp;now left|].
      apply md_global,PM_input;now left.
    + eapply md_mp with (a:=E_collection_root_exclusions T R W Z);[apply md_hyp;now right;left|].
      apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_collection_marker_from_requests M rho T A B R C P W V Theta Z
    t b r c p w v z :
  code_relation M rho T t -> code_relation M rho B b -> code_relation M rho R r ->
  code_relation M rho C c -> code_relation M rho P p -> code_relation M rho W w ->
  code_relation M rho V v -> code_relation M rho Z z ->
  NoDup [t;b;r;c;p;w;v;z] -> p<>zeroM M -> v<>zeroM M -> c<>zeroM M -> z<>zeroM M ->
  ns_proof M rho (E_wim (E_collection_marker_exclusions T R W Z)
    (E_wim (E_marker_empty T Z) (E_wim (E_collection_requests T A B R C P W V Theta Z)
      (E_wim (E_wel B C) (E_wel T C))))).
Proof.
  intros HT HB HR HC HP HW HV HZ HND HP0 HV0 HC0 HZ0.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  assert (HSpec:ns_proof M rho (E_wim (E_collection_requests T A B R C P W V Theta Z)
    (E_collection_reduced_at T B R C T W V Z))).
  { eapply ns_proof_syl;[apply numerical_collection_reduced_requests|].
    apply (numerical_collection_reduced_specialization M rho T B R C P T W V Z p t c w v z);
      try assumption;collection_discharge_name. }
  assert (HLocal:ns_proof M rho (E_wim (E_collection_marker_exclusions T R W Z)
    (E_wim (E_collection_reduced_at T B R C T W V Z)
      (E_wim (E_kp_eligible R V C T) (E_wel T C))))).
  { apply (numerical_collection_summary_marker_request M rho T B R C W V Z v);
      try assumption;collection_discharge_name. }
  assert (HSub:ns_proof M rho (E_wim (E_marker_empty T Z) (E_ksubset T B C))).
  { apply (numerical_empty_subset M rho T B C Z t c z);try assumption;collection_discharge_name. }
  assert (HElig:ns_proof M rho (E_wim (E_wa (E_wel B C) (E_ksubset T B C)) (E_kp_eligible R V C T))).
  { apply (numerical_tagged_eligibility M rho T B C V R t b c v);try assumption;collection_discharge_name. }
  apply (ns_proof_macro M rho
    (E_wim (E_collection_requests T A B R C P W V Theta Z) (E_collection_reduced_at T B R C T W V Z) ::
     E_wim (E_collection_marker_exclusions T R W Z) (E_wim (E_collection_reduced_at T B R C T W V Z)
       (E_wim (E_kp_eligible R V C T) (E_wel T C))) ::
     E_wim (E_marker_empty T Z) (E_ksubset T B C) ::
     E_wim (E_wa (E_wel B C) (E_ksubset T B C)) (E_kp_eligible R V C T) :: nil)).
  - intros e [<-|[<-|[<-|[<-|[]]]]];assumption.
  - apply macro_discharge. do 4 apply macro_deduction.
    eapply md_mp with (a:=E_kp_eligible R V C T).
    + eapply md_mp with (a:=E_wa (E_wel B C) (E_ksubset T B C)).
      * apply kp0_md_conjunction;[apply md_hyp;now left|].
        eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
        apply md_global,PM_input;now right;right;left.
      * apply md_global,PM_input;now right;right;right;left.
    + eapply md_mp with (a:=E_collection_reduced_at T B R C T W V Z).
      * eapply md_mp with (a:=E_collection_requests T A B R C P W V Theta Z);[apply md_hyp;now right;left|].
        apply md_global,PM_input;now left.
      * eapply md_mp with (a:=E_collection_marker_exclusions T R W Z);[apply md_hyp;now right;right;right;left|].
        apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_collection_root_from_requests.
Print Assumptions numerical_collection_marker_from_requests.
