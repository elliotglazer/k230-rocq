(** The singleton tag is constructed by K and then eliminated. Freshness
    is an explicit syntactic premise, not a weakening rule for old proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Requests
  NumericalKP0Eligibility NumericalSingleton NumericalChosenSingleton NumericalRawPair
  NumericalFreshPair NumericalVacuitySteps TemplateFormulaFresh TemplateNamedSubstitution
  RawCollectionProfile CollectionFramePoint.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_remove_local_exists M rho P Local Frame Goal :
  ns_proof M rho (E_wim Frame (E_wim Local Goal)) ->
  ns_proof M rho (E_wex P Local) ->
  ns_proof M rho (E_vac P Frame) -> ns_proof M rho (E_vac P Goal) ->
  ns_proof M rho (E_wim Frame Goal).
Proof.
  intros HPoint HExists VF VG.
  apply (ns_proof_macro M rho
    [E_wim Frame (E_wim Local Goal); E_wex P Local; E_vac P Frame; E_vac P Goal]).
  - intros e [<-|[<-|[<-|[<-|[]]]]];assumption.
  - assert (HP:proof_macro nil [E_wim Frame (E_wim Local Goal); E_wex P Local; E_vac P Frame; E_vac P Goal]
      (E_wim Frame (E_wim (E_wex P Local) Goal))).
    { eapply macro_syl.
      - apply kp0_parameter_exists;apply PM_input;cbn;tauto.
      - apply kp0_implication_map,request_existential_collapse,PM_input;cbn;tauto. }
    apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_wex P Local);[apply md_global,PM_input;cbn;tauto|].
    eapply md_mp with (a:=Frame);[apply md_hyp;now left|apply md_global;exact HP].
Qed.

Theorem numerical_collection_singleton_fixed M rho X P Z Fresh x p z base :
  code_relation M rho X x -> code_relation M rho P p -> code_relation M rho Z z ->
  code_relation M rho Fresh base -> x<>z -> z<>zeroM M -> p=succM M (succM M base) ->
  coding_lt M (zeroM M) base -> coding_lt M x base -> coding_lt M z base ->
  ns_proof M rho (E_wex P (E_raw_singleton X P Z)).
Proof.
  intros HX HP HZ HF HXZ HZ0 HE H0 Hx Hz.
  apply (ns_proof_mp M rho (E_wex P (E_raw_pair X X P Z))).
  - exact (numerical_fresh_pair M rho X X P Z Fresh x x p z base
      HX HX HP HZ HF HXZ HXZ HZ0 HE H0 Hx Hx Hz).
  - apply (ns_proof_macro M rho nil);[intros e []|].
    apply macro_exists_monotone,diagonal_pair_singleton_program.
Qed.

Theorem numerical_collection_coverage_from_frame M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
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
  ns_proof M rho (E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
    (E_raw_collection_coverage T A C X V ThetaX)).
Proof.
  intros HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz
    HTheta HThetaI HThetaP HSub HFrame HGoal.
  apply (collection_remove_local_exists M rho P (E_raw_singleton X P Z)
    (E_collection_frame T A B R C I W V ThetaW Z Q) (E_raw_collection_coverage T A C X V ThetaX)).
  - exact (numerical_collection_frame_point M rho T A B R C I X P W V Z Q ThetaX ThetaW
      t a b r c i x p w v z q HT HA HB HR HC HI HX HP HW HV HZ HQ HND
      HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HTheta HThetaI HThetaP HSub).
  - apply (numerical_collection_singleton_fixed M rho X P Z Fresh x p z base HX HP HZ HF).
    + inversion HND as [|? ? ? H1].
      repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
      repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
      congruence.
    + exact HZ0.
    + exact HE.
    + exact H0.
    + exact Hx.
    + exact Hz.
  - exact (kp0_expression_fresh_vacuity M rho P _ p HP HFrame).
  - exact (kp0_expression_fresh_vacuity M rho P _ p HP HGoal).
Qed.

Print Assumptions collection_remove_local_exists.
Print Assumptions numerical_collection_singleton_fixed.
Print Assumptions numerical_collection_coverage_from_frame.
