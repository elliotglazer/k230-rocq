(** Derive the finite outer context from actual envelope facts, then apply
    the generated Collection profile for its already chosen pair. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Eligibility
  NumericalBootstrap NumericalRawEnvelope NumericalRawPair RawMarkerExclusions
  NumericalEnvelopeFacts CollectionFramePoint CollectionKernelProfile.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_outer_from_envelope_program T A B R Z Q Goal :
  proof_macro nil
   [E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
      (E_wim (E_raw_envelope T A B Q) (E_wn (E_wel T B))));
    E_wim (E_marker_empty T Z) (E_wim (E_raw_envelope T A B Q) (E_wn (E_weq B T)));
    E_wim (E_collection_outer T A B R Z Q) Goal]
   (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
     (E_wim (E_raw_envelope T A B Q) (E_wim (E_raw_pair B T R Z) Goal)))).
Proof.
  set (Emp:=E_marker_empty T Z). set (Dom:=E_wel T A).
  set (Env:=E_raw_envelope T A B Q). set (Pair:=E_raw_pair B T R Z).
  set (inputs:=[E_wim Emp (E_wim Dom (E_wim Env (E_wn (E_wel T B))));
    E_wim Emp (E_wim Env (E_wn (E_weq B T)));
    E_wim (E_collection_outer T A B R Z Q) Goal]).
  apply macro_discharge. do 4 apply macro_deduction.
  set (ctx:=[Pair;Env;Dom;Emp]).
  eapply md_mp with (a:=E_collection_outer T A B R Z Q);[|apply md_global,PM_input;unfold inputs;now right;right;left].
  unfold E_collection_outer,collection_outer_fields. apply collection_bundle_construct.
  intros f [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply md_hyp;unfold ctx;cbn;tauto.
  - eapply md_mp with (a:=Env);[apply md_hyp;unfold ctx;cbn;tauto|].
    eapply md_mp with (a:=Emp);[apply md_hyp;unfold ctx;cbn;tauto|].
    apply md_global,PM_input;unfold inputs;now right;left.
  - apply md_hyp;unfold ctx;cbn;tauto.
  - apply md_hyp;unfold ctx;cbn;tauto.
  - eapply md_mp with (a:=Env);[apply md_hyp;unfold ctx;cbn;tauto|].
    eapply md_mp with (a:=Dom);[apply md_hyp;unfold ctx;cbn;tauto|].
    eapply md_mp with (a:=Emp);[apply md_hyp;unfold ctx;cbn;tauto|].
    apply md_global,PM_input;unfold inputs;now left.
Qed.

Theorem numerical_collection_outer_from_envelope M rho T A B R Z Q Goal t a b z q :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho Z z -> code_relation M rho Q q ->
  q<>zeroM M -> t<>q -> a<>q -> b<>q -> z<>zeroM M -> t<>z -> a<>z ->
  ns_proof M rho (E_wim (E_collection_outer T A B R Z Q) Goal) ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B Q) (E_wim (E_raw_pair B T R Z) Goal)))).
Proof.
  intros HT HA HB HZ HQ HQ0 HTQ HAQ HBQ HZ0 HTZ HAZ HOuter.
  apply (ns_proof_macro M rho
   [E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
      (E_wim (E_raw_envelope T A B Q) (E_wn (E_wel T B))));
    E_wim (E_marker_empty T Z) (E_wim (E_raw_envelope T A B Q) (E_wn (E_weq B T)));
    E_wim (E_collection_outer T A B R Z Q) Goal]).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (numerical_envelope_not_domain M rho T A B Q Z t a b q z HT HA HB HQ HZ HTQ HAQ HBQ HZ0 HTZ).
    + exact (numerical_envelope_not_marker M rho T A B Q Z t a b q z HT HA HB HQ HZ HQ0 HTQ HAQ HBQ HZ0 HTZ HAZ).
    + exact HOuter.
  - apply collection_outer_from_envelope_program.
Qed.

Print Assumptions numerical_collection_outer_from_envelope.
