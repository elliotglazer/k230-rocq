(** Combine actual singleton coverage, support-witness rebasing and
    marker membership for the same raw Collection container. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates ProofMacros NamedLeibnizSteps NumericalKP0 NumericalTaggedComprehension
  TemplateNamedSubstitution TemplateFormulaFresh RawMarkerQuantifiers
  RawCollectionProfile CollectionCoverageNumerical CollectionFramePoint
  CollectionFrameCoverage CollectionSupportRebase CollectionFrameProfile.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_conclusion_nodup {D:Type} (t a b r c i x p w v z q:D) :
  NoDup [t;a;b;r;c;i;x;p;w;v;z;q] -> NoDup [t;b;r;c;i;w;v;z].
Proof.
  intro H.
  pose proof (NoDup_remove_1 [t] [b;r;c;i;x;p;w;v;z;q] a H) as H1.
  pose proof (NoDup_remove_1 [t;b;r;c;i] [p;w;v;z;q] x H1) as H2.
  pose proof (NoDup_remove_1 [t;b;r;c;i] [w;v;z;q] p H2) as H3.
  exact (NoDup_remove_1 [t;b;r;c;i;w;v;z] [] q H3).
Qed.

Theorem numerical_collection_frame_conclusion M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
    t a b r c i x p w v z q base :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho R r -> code_relation M rho C c -> code_relation M rho I i -> code_relation M rho X x ->
  code_relation M rho P p -> code_relation M rho W w -> code_relation M rho V v ->
  code_relation M rho Z z -> code_relation M rho Q q -> code_relation M rho Fresh base ->
  NoDup [t;a;b;r;c;i;x;p;w;v;z;q] ->
  c<>zeroM M -> i<>zeroM M -> x<>zeroM M -> p<>zeroM M -> w<>zeroM M -> v<>zeroM M -> z<>zeroM M -> q<>zeroM M ->
  p=succM M (succM M base) -> coding_lt M (zeroM M) base -> coding_lt M x base -> coding_lt M z base ->
  expression_fresh M rho w ThetaX -> expression_fresh M rho i ThetaW -> expression_fresh M rho p ThetaW ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  expression_fresh M rho p (E_collection_frame T A B R C I W V ThetaW Z Q) ->
  expression_fresh M rho p (E_raw_collection_coverage T A C X V ThetaX) ->
  ns_proof M rho (E_wim
    (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
      (E_wal V (E_raw_collection_support T A C W V ThetaW)))
    (E_raw_collection_profile T A C X V ThetaX)).
Proof.
  intros HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz
    HTheta HThetaI HThetaP HSub HFrame HGoal.
  pose proof (numerical_collection_frame_coverage M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
    t a b r c i x p w v z q base HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND
    HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz HTheta HThetaI HThetaP HSub HFrame HGoal) as HCoverage.
  pose proof (numerical_collection_frame_profile M rho T A B R C I W V ThetaW Z Q X ThetaX
    t b r c i w v z HT HB HR HC HI HW HV HZ
    (collection_conclusion_nodup t a b r c i x p w v z q HND)
    HI0 HV0 HC0 HZ0 HW0 HCoverage) as HProfile.
  assert (HRebase:ns_proof M rho (E_wim
    (E_wal V (E_raw_collection_support T A C W V ThetaW))
    (E_wal V (E_raw_collection_support T A C X V ThetaX)))).
  { repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
    repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
    exact (proj1 (numerical_collection_support_rebase M rho T A C X W V ThetaX ThetaW x w
      HX HW HX0 HW0 ltac:(congruence)
      (marker_name_avoids M rho T t x HT ltac:(congruence))
      (marker_name_avoids M rho A a x HA ltac:(congruence))
      (marker_name_avoids M rho T t w HT ltac:(congruence))
      (marker_name_avoids M rho A a w HA ltac:(congruence)) HTheta HSub)). }
  apply (ns_proof_macro M rho
    [E_wim (E_wal V (E_raw_collection_support T A C W V ThetaW))
       (E_wal V (E_raw_collection_support T A C X V ThetaX));
     E_wim (E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
       (E_wal V (E_raw_collection_support T A C X V ThetaX)))
       (E_raw_collection_profile T A C X V ThetaX)]).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_wa (E_collection_frame T A B R C I W V ThetaW Z Q)
      (E_wal V (E_raw_collection_support T A C X V ThetaX))).
    + apply kp0_md_conjunction.
      * apply tagged_md_left with (b:=E_wal V (E_raw_collection_support T A C W V ThetaW)),
          md_hyp;now left.
      * eapply md_mp with (a:=E_wal V (E_raw_collection_support T A C W V ThetaW)).
        -- apply tagged_md_right with (a:=E_collection_frame T A B R C I W V ThetaW Z Q),
             md_hyp;now left.
        -- apply md_global,PM_input;now left.
    + apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_collection_frame_conclusion.
