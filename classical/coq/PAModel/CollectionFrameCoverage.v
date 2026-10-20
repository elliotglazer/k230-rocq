(** Universally close actual singleton-based coverage. The original
    matrix may bind its source name: stopping-substitution output vacuity
    supplies precisely the context condition needed for generalization. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NumericalVacuitySteps NamedBinderFresh
  TemplateNamedSubstitution TemplateFormulaFresh BoundVariableVacuity
  RawMarkerQuantifiers RawCollectionProfile CollectionCoverageNumerical
  CollectionFramePoint CollectionCoverageExists CollectionFrameVacuity.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma ns_stopping_substitution_output_vacuity M rho X Original Output x y :
  code_relation M rho X x -> x<>y ->
  expression_named_substitution M rho rho x y Original Output ->
  ns_proof M rho (E_vac X Output).
Proof.
  intros HX HXY HSub result HResult.
  destruct (code_relation_total M Original rho) as [f HF].
  destruct (code_relation_total M Output rho) as [g HG].
  apply (stopping_substitution_vacuity_internal M f x y g HXY (HSub f g HF HG) result).
  exact (proj1 (expression_vacuity_graph M rho X Output x g result HX HG) HResult).
Qed.

Theorem numerical_collection_frame_coverage M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
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
    (E_wal X (E_raw_collection_coverage T A C X V ThetaX))).
Proof.
  intros HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz
    HTheta HThetaI HThetaP HSub HFrame HGoal.
  pose proof (numerical_collection_coverage_from_frame M rho T A B R C I X P W V Z Q Fresh ThetaX ThetaW
    t a b r c i x p w v z q base HT HA HB HR HC HI HX HP HW HV HZ HQ HF HND
    HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HE H0 Hx Hz HTheta HThetaI HThetaP HSub HFrame HGoal) as HPoint.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  apply marker_generalize_one;[|exact HPoint].
  apply (numerical_collection_frame_vacuity M rho X T A B R C I W V ThetaW Z Q x HX HX0).
  all:try (eapply marker_name_avoids;[eassumption|congruence]).
  apply (ns_stopping_substitution_output_vacuity M rho X ThetaX ThetaW x w HX).
  - congruence.
  - exact HSub.
Qed.

Print Assumptions ns_stopping_substitution_output_vacuity.
Print Assumptions numerical_collection_frame_coverage.
