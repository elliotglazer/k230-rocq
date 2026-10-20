(** All fixed hypotheses for Collection are kept in one explicit object
    conjunction while a fresh singleton request supplies pointwise coverage. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps ProofMacros QuantifierMacros TemplateCD TemplatePropositional
  NumericalKP0 NumericalKP0Eligibility NumericalBootstrap NumericalSingleton NumericalRawPair
  NumericalTaggedComprehension NumericalRawEnvelope RawMarkerExclusions RawMarkerTransport
  RawMarkerQuantifiers TemplateFormulaFresh TemplateBinderFresh TemplateNamedSubstitution
  NamedBinderFresh FreshNames CollectionCoverageNumerical CollectionCoverageFrame
  CollectionSelectedCleanup CollectionFullSpecialization CollectionKernel RawCollectionProfile.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint E_collection_bundle (xs:list code_expr) : code_expr :=
  match xs with nil=>CEconst 0 | a::rest=>E_wa a (E_collection_bundle rest) end.

Lemma collection_bundle_projection G inputs xs f :
  In f xs -> proof_macro G inputs (E_wim (E_collection_bundle xs) f).
Proof.
  induction xs as [|a rest IH];cbn;intro H;[contradiction|].
  destruct H as [<-|H].
  - apply PM_template,bootstrap_projection_left.
  - eapply macro_syl;[apply PM_template,bootstrap_projection_right|now apply IH].
Qed.

Lemma collection_bundle_member G inputs delta xs f :
  In f xs -> macro_derivation G inputs delta (E_collection_bundle xs) ->
  macro_derivation G inputs delta f.
Proof. intros HI HP. eapply md_mp;[exact HP|apply md_global,collection_bundle_projection,HI]. Qed.

Definition collection_frame_fields T A B R C I W V ThetaW Z Q :=
  [E_marker_empty T Z; E_wn (E_weq B T); E_raw_pair B T R Z;
   E_raw_envelope T A B Q; E_wel B C; E_collection_requests T A B R C I W V ThetaW Z].
Definition E_collection_frame T A B R C I W V ThetaW Z Q :=
  E_collection_bundle (collection_frame_fields T A B R C I W V ThetaW Z Q).

Definition collection_frame_point_inputs T A B R C I X P W V ThetaX ThetaW Z Q :=
  [E_wim (E_wn (E_weq B T)) (E_wim (E_raw_pair B T R Z)
     (E_wim (E_raw_singleton X P Z) (E_wn (E_weq P R))));
   E_wim (E_marker_empty T Z) (E_wim (E_raw_singleton X P Z) (E_wn (E_weq P T)));
   E_wim (E_collection_requests T A B R C I W V ThetaW Z)
     (E_collection_request_at T A B R C P W V ThetaW Z);
   E_wim (E_raw_envelope T A B Q)
     (E_wim (E_collection_selected_hyp T R X P Z)
       (E_wim (E_wel B C) (E_wim (E_collection_request_at T A B R C P W V ThetaW Z)
         (E_raw_collection_coverage T A C X V ThetaX))))].

Lemma collection_frame_point_program T A B R C I X P W V ThetaX ThetaW Z Q :
  proof_macro nil (collection_frame_point_inputs T A B R C I X P W V ThetaX ThetaW Z Q)
    (E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
      (E_wim (E_raw_singleton X P Z) (E_raw_collection_coverage T A C X V ThetaX))).
Proof.
  set (fields:=collection_frame_fields T A B R C I W V ThetaW Z Q).
  set (inputs:=collection_frame_point_inputs T A B R C I X P W V ThetaX ThetaW Z Q).
  set (ctx:=E_raw_singleton X P Z :: E_collection_bundle fields :: nil).
  apply macro_discharge. do 2 apply macro_deduction.
  assert (HFrame:macro_derivation nil inputs ctx (E_collection_bundle fields)) by (apply md_hyp;now right;left).
  assert (HS:macro_derivation nil inputs ctx (E_raw_singleton X P Z)) by (apply md_hyp;now left).
  assert (HEmpty:macro_derivation nil inputs ctx (E_marker_empty T Z)).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HNot:macro_derivation nil inputs ctx (E_wn (E_weq B T))).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HPair:macro_derivation nil inputs ctx (E_raw_pair B T R Z)).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HEnv:macro_derivation nil inputs ctx (E_raw_envelope T A B Q)).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HBC:macro_derivation nil inputs ctx (E_wel B C)).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HReq:macro_derivation nil inputs ctx (E_collection_requests T A B R C I W V ThetaW Z)).
  { apply (collection_bundle_member nil inputs ctx fields);[unfold fields,collection_frame_fields;cbn;tauto|exact HFrame]. }
  assert (HSelected:macro_derivation nil inputs ctx (E_collection_selected_hyp T R X P Z)).
  { unfold E_collection_selected_hyp. apply kp0_md_conjunction;[exact HS|].
    apply kp0_md_conjunction.
    - eapply md_mp;[exact HS|]. eapply md_mp;[exact HPair|]. eapply md_mp;[exact HNot|].
      apply md_global,PM_input;unfold inputs,collection_frame_point_inputs;now left.
    - eapply md_mp;[exact HS|]. eapply md_mp;[exact HEmpty|].
      apply md_global,PM_input;unfold inputs,collection_frame_point_inputs;now right;left. }
  eapply md_mp with (a:=E_collection_request_at T A B R C P W V ThetaW Z).
  - eapply md_mp;[exact HReq|]. apply md_global,PM_input;unfold inputs,collection_frame_point_inputs;now right;right;left.
  - eapply md_mp;[exact HBC|]. eapply md_mp;[exact HSelected|]. eapply md_mp;[exact HEnv|].
    apply md_global,PM_input;unfold inputs,collection_frame_point_inputs;now right;right;right;left.
Qed.

Theorem numerical_collection_frame_point M rho T A B R C I X P W V Z Q ThetaX ThetaW
    t a b r c i x p w v z q :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho R r -> code_relation M rho C c -> code_relation M rho I i -> code_relation M rho X x ->
  code_relation M rho P p -> code_relation M rho W w -> code_relation M rho V v ->
  code_relation M rho Z z -> code_relation M rho Q q ->
  NoDup [t;a;b;r;c;i;x;p;w;v;z;q] ->
  c<>zeroM M -> i<>zeroM M -> x<>zeroM M -> p<>zeroM M -> w<>zeroM M -> v<>zeroM M -> z<>zeroM M -> q<>zeroM M ->
  expression_fresh M rho w ThetaX -> expression_fresh M rho i ThetaW -> expression_fresh M rho p ThetaW ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim (E_collection_frame T A B R C I W V ThetaW Z Q)
    (E_wim (E_raw_singleton X P Z) (E_raw_collection_coverage T A C X V ThetaX))).
Proof.
  intros HT HA HB HR HC HI HX HP HW HV HZ HQ HND HC0 HI0 HX0 HP0 HW0 HV0 HZ0 HQ0 HTheta HThetaI HThetaP HSub.
  assert (HNDlocal:NoDup [t;a;b;r;c;x;p;w;v;z;q]).
  { exact (NoDup_remove_1 [t;a;b;r;c] [x;p;w;v;z;q] i HND). }
  pose proof (numerical_collection_coverage_local M rho T A B R C X P W V Z Q ThetaX ThetaW
    t a b r c x p w v z q HT HA HB HR HC HX HP HW HV HZ HQ HNDlocal
    HC0 HX0 HP0 HW0 HV0 HZ0 HQ0 HTheta HSub) as HLocal.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~ In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  apply (ns_proof_macro M rho (collection_frame_point_inputs T A B R C I X P W V ThetaX ThetaW Z Q)).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + apply (numerical_singleton_not_pair M rho B T R X P Z b t r x p z);try assumption;collection_discharge_name.
    + apply (numerical_singleton_not_marker M rho T X P Z t x p z);try assumption;collection_discharge_name.
    + apply (numerical_collection_full_specialization M rho T A B R C I P W V ThetaW Z i p c w v z);
        try assumption;try (intros f HF;apply named_formula_fresh_binder_absent, HThetaP,HF);collection_discharge_name.
    + exact HLocal.
  - apply collection_frame_point_program.
Qed.

Print Assumptions collection_bundle_projection.
Print Assumptions collection_frame_point_program.
Print Assumptions numerical_collection_frame_point.
