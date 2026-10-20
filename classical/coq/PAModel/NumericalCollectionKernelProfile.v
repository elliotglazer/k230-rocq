(** Numeric realization of the outer-to-profile program. All five inputs
    are actual K derivations; the initial kernel and finite outer facts
    remain object hypotheses for the same result container. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NumericalKP0 NumericalKP0Eligibility
  NumericalTaggedComprehension NumericalRawPair RawMarkerExclusions RawMarkerQuantifiers
  TemplateFormulaFresh TemplateNamedSubstitution RawCollectionProfile
  CollectionSupportCleanup CollectionKernel CollectionExceptionalRequests
  CollectionDistinguishedMembers CollectionCoverageNumerical CollectionFramePoint
  CollectionFrameConclusion CollectionKernelProfile.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem numerical_collection_kernel_profile M rho T A B R C I J X P W V Z Q Fresh ThetaX ThetaW
    t a b r c i j x p w v z q base :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho R r -> code_relation M rho C c -> code_relation M rho I i ->
  code_relation M rho J j -> code_relation M rho X x ->
  code_relation M rho P p -> code_relation M rho W w -> code_relation M rho V v ->
  code_relation M rho Z z -> code_relation M rho Q q -> code_relation M rho Fresh base ->
  NoDup [t;a;b;r;c;i;x;p;w;v;z;q] ->
  c<>zeroM M -> i<>zeroM M -> x<>zeroM M -> p<>zeroM M -> w<>zeroM M -> v<>zeroM M -> z<>zeroM M -> q<>zeroM M ->
  j<>zeroM M -> t<>j -> a<>j -> b<>j -> w<>j -> v<>j ->
  p=succM M (succM M base) -> coding_lt M (zeroM M) base -> coding_lt M x base -> coding_lt M z base ->
  expression_fresh M rho w ThetaX -> expression_fresh M rho i ThetaW ->
  expression_fresh M rho p ThetaW -> expression_fresh M rho j ThetaW ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  expression_fresh M rho p (E_collection_frame T A B R C I W V ThetaW Z Q) ->
  expression_fresh M rho p (E_raw_collection_coverage T A C X V ThetaX) ->
  ns_proof M rho (E_wim (E_collection_outer T A B R Z Q)
    (E_wim (E_wa (E_collection_requests T A B R C I W V ThetaW Z)
      (E_collection_raw_support T A B R C J W V ThetaW Z))
      (E_raw_collection_profile T A C X V ThetaX))).
Proof.
  intros HT HA HB HR HC HI HJ HX HP HW HV HZ HQ HF HND HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0
    HJ0 HTJ HAJ HBJ HWJ HVJ HE H0 Hx Hz HTheta HThetaI HThetaP HThetaJ HSub HFrame HGoal.
  pose proof (numerical_collection_root_from_requests M rho T A B R C I W V ThetaW Z
    t b r c i w v z HT HB HR HC HI HW HV HZ
    (collection_conclusion_nodup t a b r c i x p w v z q HND) HI0 HV0) as HRoot.
  pose proof (numerical_collection_frame_conclusion M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
    t a b r c i x p w v z q base HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND
    HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz HTheta HThetaI HThetaP HSub HFrame HGoal) as HProfile.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  apply (ns_proof_macro M rho
   [E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq R T)));
    E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z) (E_collection_no_singletons W R Z));
    E_wim (E_collection_root_exclusions T R W Z)
      (E_wim (E_collection_requests T A B R C I W V ThetaW Z) (E_wel B C));
    E_wim (E_marker_empty T Z) (E_wim (E_wn (E_wel T B))
      (E_wim (E_collection_raw_support T A B R C J W V ThetaW Z)
        (E_wal V (E_raw_collection_support T A C W V ThetaW))));
    E_wim (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
        (E_wal V (E_raw_collection_support T A C W V ThetaW)))
      (E_raw_collection_profile T A C X V ThetaX)]).
  - intros e [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (numerical_pair_not_empty M rho B T R Z b t z HB HT HZ HZ0);
        collection_discharge_name.
    + apply (numerical_pair_no_singletons M rho B T R W Z b t r w z HB HT HR HW HZ HW0);
        collection_discharge_name.
    + exact HRoot.
    + apply (numerical_collection_support_cleanup M rho T A B R C J W V ThetaW Z Z
        t j v z HT HJ HV HZ HJ0 HV0 HZ0);try (collection_discharge_name).
    + exact HProfile.
  - apply collection_outer_profile_program.
Qed.

Print Assumptions numerical_collection_kernel_profile.
