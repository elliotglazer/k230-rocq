(** Numerical discharge of every local coverage-program input. All raw
    formula transport uses the actual input-to-private-witness substitution. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution
  TemplateFormulaFresh RawMarkerQuantifiers NumericalRawEnvelope NumericalKP0
  NumericalKP0Eligibility NumericalSingleton NumericalTaggedComprehension
  TaggedSubsetFacts TaggedEligibility CollectionEnvelopeHelpers CollectionCoverageFrame
  CollectionSelectedOutput CollectionSelectedNumerical CollectionCoverageProgram
  CollectionSelectedCleanup CollectionFullSpecialization CollectionSupportCleanup.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Ltac collection_discharge_name :=
  first [assumption | solve [congruence] |
    solve [eapply marker_name_avoids;[eassumption|congruence]]].

Theorem numerical_collection_coverage_local M rho T A B R C X P W V Z Q ThetaX ThetaW
    t a b r c x p w v z q :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho R r -> code_relation M rho C c -> code_relation M rho X x ->
  code_relation M rho P p -> code_relation M rho W w -> code_relation M rho V v ->
  code_relation M rho Z z -> code_relation M rho Q q ->
  NoDup [t;a;b;r;c;x;p;w;v;z;q] ->
  c<>zeroM M -> x<>zeroM M -> p<>zeroM M -> w<>zeroM M -> v<>zeroM M -> z<>zeroM M -> q<>zeroM M ->
  expression_fresh M rho w ThetaX ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho
    (E_wim (E_raw_envelope T A B Q)
      (E_wim (E_collection_selected_hyp T R X P Z)
        (E_wim (E_wel B C)
          (E_wim (E_collection_request_at T A B R C P W V ThetaW Z)
            (E_wim (E_wa (E_wel T X) (E_wel X A))
              (E_wim (E_wex V (E_wa (E_wel T V) ThetaX))
                (E_wex V (E_collection_selected_result T C V ThetaX)))))))).
Proof.
  intros HT HA HB HR HC HX HP HW HV HZ HQ HND HC0 HX0 HP0 HW0 HV0 HZ0 HQ0 HTheta HSub.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  apply (ns_proof_macro M rho
    (collection_coverage_frame_inputs (E_raw_envelope T A B Q) T A B R C X P W V ThetaW ThetaX Z)).
  - intros e [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (numerical_envelope_member M rho T A B Q X t a b q x);try assumption;collection_discharge_name.
    + apply (numerical_singleton_subset M rho X P B C Z x p b c z);try assumption;collection_discharge_name.
    + apply (numerical_tagged_eligibility M rho P B C V R p b c v);try assumption;collection_discharge_name.
    + apply (numerical_collection_selected_antecedent M rho T A B R P X W V ThetaX ThetaW Z x w v z);
        try assumption;collection_discharge_name.
    + apply (numerical_collection_selected_cleanup_checked M rho T A B R C X P W V ThetaW ThetaX Z x p w v z);
        try assumption;collection_discharge_name.
  - apply collection_coverage_frame_program.
Qed.

Print Assumptions numerical_collection_coverage_local.
