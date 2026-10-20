(** Finite proof programs for the witness step in KQuotSeparation.
    The predicate-invariance premise is explicit here; quoted predicates
    obtain it from the separately proved actual mixed congruence theorem. *)
From PAModel Require Import CodeExpressions ProofTemplates TemplatePropositional
  ProofMacros QuantifierMacros NumericalVacuitySteps NumericalKP0 NumericalBootstrap
  StoppingSpecialization BoundVariableVacuityRules NamedLeibnizSteps Model.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_selection_iff p q := E_wa (E_wim p q) (E_wim q p).
Definition E_selection_witness d a e := E_wa (E_wa d a) e.
Definition E_selection_raw d c a p := E_wim d (E_selection_iff c (E_wa a p)).
Definition E_selection_invariant e p q := E_wim e (E_selection_iff p q).

Lemma selection_forward_derivation G Delta d c a e p q :
  template_derivation G Delta (E_selection_raw d c a p) ->
  template_derivation G Delta (E_selection_invariant e p q) ->
  template_derivation G Delta (E_selection_witness d c e) ->
  template_derivation G Delta (E_wa (E_selection_witness d a e) q).
Proof.
  intros HR HI HW.
  pose proof (template_der_andl G Delta (E_wa d c) e HW) as HDC.
  pose proof (template_der_andl G Delta d c HDC) as HD.
  pose proof (template_der_andr G Delta d c HDC) as HC.
  pose proof (template_der_andr G Delta (E_wa d c) e HW) as HE.
  assert (HCiff : template_derivation G Delta (E_selection_iff c (E_wa a p))).
  { exact (dmp G Delta d _ HR HD). }
  assert (HAP : template_derivation G Delta (E_wa a p)).
  { exact (dmp G Delta c _ (template_der_andl G Delta _ _ HCiff) HC). }
  assert (HPiff : template_derivation G Delta (E_selection_iff p q)).
  { exact (dmp G Delta e _ HI HE). }
  apply template_der_andi.
  - unfold E_selection_witness. apply template_der_andi;[|exact HE].
    apply template_der_andi;[exact HD|exact (template_der_andl G Delta a p HAP)].
  - exact (dmp G Delta p _ (template_der_andl G Delta _ _ HPiff)
      (template_der_andr G Delta a p HAP)).
Qed.

Lemma selection_backward_derivation G Delta d c a e p q :
  template_derivation G Delta (E_selection_raw d c a p) ->
  template_derivation G Delta (E_selection_invariant e p q) ->
  template_derivation G Delta (E_wa (E_selection_witness d a e) q) ->
  template_derivation G Delta (E_selection_witness d c e).
Proof.
  intros HR HI HW.
  pose proof (template_der_andl G Delta (E_selection_witness d a e) q HW) as HDAE.
  pose proof (template_der_andr G Delta (E_selection_witness d a e) q HW) as HQ.
  pose proof (template_der_andl G Delta (E_wa d a) e HDAE) as HDA.
  pose proof (template_der_andl G Delta d a HDA) as HD.
  pose proof (template_der_andr G Delta d a HDA) as HA.
  pose proof (template_der_andr G Delta (E_wa d a) e HDAE) as HE.
  assert (HCiff : template_derivation G Delta (E_selection_iff c (E_wa a p))).
  { exact (dmp G Delta d _ HR HD). }
  assert (HPiff : template_derivation G Delta (E_selection_iff p q)).
  { exact (dmp G Delta e _ HI HE). }
  unfold E_selection_witness. apply template_der_andi;[|exact HE].
  apply template_der_andi;[exact HD|].
  apply (dmp G Delta (E_wa a p) c (template_der_andr G Delta _ _ HCiff)).
  apply template_der_andi;[exact HA|].
  exact (dmp G Delta q p (template_der_andr G Delta _ _ HPiff) HQ).
Qed.

Theorem selection_point_equivalence G d c a e p q :
  template_proof G
    (E_wim (E_selection_raw d c a p) (E_wim (E_selection_invariant e p q)
      (E_selection_iff (E_selection_witness d c e) (E_wa (E_selection_witness d a e) q)))).
Proof.
  apply template_discharge. do 2 apply template_deduction.
  apply template_der_andi;apply template_deduction.
  - eapply selection_forward_derivation;apply dhyp;cbn;tauto.
  - eapply selection_backward_derivation;apply dhyp;cbn;tauto.
Qed.

Lemma exists_constant_conjunction_program w a q :
  proof_macro nil (E_vac w q :: nil)
    (E_selection_iff (E_wex w (E_wa a q)) (E_wa (E_wex w a) q)).
Proof.
  set (inputs:=E_vac w q :: nil).
  assert (HA : proof_macro nil inputs (E_wim (E_wex w (E_wa a q)) (E_wex w a))).
  { apply macro_exists_monotone,PM_template,bootstrap_projection_left. }
  assert (HQ : proof_macro nil inputs (E_wim (E_wex w (E_wa a q)) q)).
  { eapply macro_syl;[apply macro_exists_monotone,PM_template,bootstrap_projection_right|].
    eapply macro_syl.
    - apply macro_exists_monotone,PM_input;now left.
    - apply PM_template,template_r6. }
  assert (HB : proof_macro nil inputs (E_wim q (E_wim (E_wex w a) (E_wex w (E_wa a q))))).
  { apply kp0_parameter_exists;[apply PM_input;now left|].
    apply PM_template,template_discharge. do 2 apply template_deduction.
    apply template_der_andi;apply dhyp;cbn;tauto. }
  apply macro_discharge,kp0_md_conjunction;apply macro_deduction.
  - apply kp0_md_conjunction;eapply md_mp;[apply md_hyp;now left|apply md_global;exact HA|
      apply md_hyp;now left|apply md_global;exact HQ].
  - eapply md_mp with (a:=E_wex w a).
    + eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_left.
    + eapply md_mp with (a:=q).
      * eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_right.
      * apply md_global;exact HB.
Qed.

Print Assumptions selection_point_equivalence.
Print Assumptions exists_constant_conjunction_program.

Lemma selection_macro_inputs G inputs inputs' f :
  (forall p,In p inputs -> In p inputs') ->
  proof_macro G inputs f -> proof_macro G inputs' f.
Proof.
  intros HI HP. induction HP.
  - now apply PM_template.
  - now apply PM_input,HI.
  - exact (PM_mp _ _ IHHP1 IHHP2).
  - exact (PM_gen _ _ IHHP).
Qed.
Lemma selection_vacuous_conjunction inputs w p q :
  proof_macro nil inputs (E_vac w p) -> proof_macro nil inputs (E_vac w q) ->
  proof_macro nil inputs (E_vac w (E_wa p q)).
Proof.
  intros HP HQ. unfold E_wa. apply macro_vacuous_negation.
  apply macro_vacuous_implication;[exact HP|now apply macro_vacuous_negation].
Qed.

Definition selection_witness_inputs w d c a e p q :=
  E_wim (E_wal w (E_selection_raw d c a p)) (E_selection_raw d c a p) ::
  E_wim (E_wal w (E_selection_invariant e p q)) (E_selection_invariant e p q) ::
  E_vac w (E_wal w (E_selection_raw d c a p)) ::
  E_vac w (E_wal w (E_selection_invariant e p q)) :: E_vac w q :: nil.

Theorem selection_witness_program w d c a e p q :
  proof_macro nil (selection_witness_inputs w d c a e p q)
    (E_wim (E_wal w (E_selection_raw d c a p))
      (E_wim (E_wal w (E_selection_invariant e p q))
        (E_selection_iff (E_wex w (E_selection_witness d c e))
          (E_wa (E_wex w (E_selection_witness d a e)) q)))).
Proof.
  set (inputs:=selection_witness_inputs w d c a e p q).
  set (R:=E_wal w (E_selection_raw d c a p)).
  set (I:=E_wal w (E_selection_invariant e p q)).
  set (P:=E_wa R I).
  set (C:=E_selection_witness d c e).
  set (A:=E_selection_witness d a e).
  assert (HPoint : proof_macro nil inputs (E_wim P (E_selection_iff C (E_wa A q)))).
  { apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_selection_invariant e p q).
    - eapply md_mp with (a:=I).
      + eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_right.
      + apply md_global,PM_input;unfold inputs,selection_witness_inputs,I;cbn;tauto.
    - eapply md_mp with (a:=E_selection_raw d c a p).
      + eapply md_mp with (a:=R).
        * eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_left.
        * apply md_global,PM_input;unfold inputs,selection_witness_inputs,R;cbn;tauto.
      + apply md_global,PM_template,selection_point_equivalence. }
  assert (HP : proof_macro nil inputs (E_vac w P)).
  { unfold P. apply selection_vacuous_conjunction;apply PM_input;
      unfold inputs,selection_witness_inputs,R,I;cbn;tauto. }
  assert (HQ : proof_macro nil inputs (E_vac w q)).
  { apply PM_input;unfold inputs,selection_witness_inputs;cbn;tauto. }
  assert (HDist : proof_macro nil inputs
    (E_selection_iff (E_wex w (E_wa A q)) (E_wa (E_wex w A) q))).
  { apply (selection_macro_inputs nil (E_vac w q :: nil));[|apply exists_constant_conjunction_program].
    intros f [<-|[]]. unfold inputs,selection_witness_inputs;cbn;tauto. }
  assert (HForward : proof_macro nil inputs
    (E_wim P (E_wim (E_wex w C) (E_wa (E_wex w A) q)))).
  { eapply macro_syl.
    - apply kp0_parameter_exists;[exact HP|].
      eapply macro_syl;[exact HPoint|apply PM_template,bootstrap_projection_left].
    - apply kp0_implication_map.
      eapply PM_mp;[exact HDist|apply PM_template,bootstrap_projection_left]. }
  assert (HPointBack : proof_macro nil inputs (E_wim (E_wa P q) (E_wim A C))).
  { assert (HBack : proof_macro nil inputs (E_wim P (E_wim (E_wa A q) C))).
    { eapply macro_syl;[exact HPoint|apply PM_template,bootstrap_projection_right]. }
    apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wa A q).
    - apply kp0_md_conjunction;[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wa P q);[apply md_hyp;cbn;tauto|]. apply md_global,PM_template,bootstrap_projection_right.
    - eapply md_mp with (a:=P).
      + eapply md_mp with (a:=E_wa P q);[apply md_hyp;cbn;tauto|]. apply md_global,PM_template,bootstrap_projection_left.
      + apply md_global;exact HBack. }
  assert (HBackLift : proof_macro nil inputs
    (E_wim (E_wa P q) (E_wim (E_wex w A) (E_wex w C)))).
  { apply kp0_parameter_exists;[now apply selection_vacuous_conjunction|exact HPointBack]. }
  assert (HBackward : proof_macro nil inputs
    (E_wim P (E_wim (E_wa (E_wex w A) q) (E_wex w C)))).
  { apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wex w A).
    - eapply md_mp with (a:=E_wa (E_wex w A) q);[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_left.
    - eapply md_mp with (a:=E_wa P q).
      + apply kp0_md_conjunction;[apply md_hyp;cbn;tauto|].
        eapply md_mp with (a:=E_wa (E_wex w A) q);[apply md_hyp;now left|]. apply md_global,PM_template,bootstrap_projection_right.
      + apply md_global;exact HBackLift. }
  apply macro_discharge. do 2 apply macro_deduction.
  assert (HPar : macro_derivation nil inputs (I::R::nil) P).
  { unfold P. apply kp0_md_conjunction;apply md_hyp;cbn;tauto. }
  apply kp0_md_conjunction.
  - eapply md_mp;[exact HPar|apply md_global;exact HForward].
  - eapply md_mp;[exact HPar|apply md_global;exact HBackward].
Qed.

Theorem numerical_selection_witness M env W D C A E P Q :
  ns_proof M env (E_vac W Q) ->
  ns_proof M env
    (E_wim (E_wal W (E_selection_raw D C A P))
      (E_wim (E_wal W (E_selection_invariant E P Q))
        (E_selection_iff (E_wex W (E_selection_witness D C E))
          (E_wa (E_wex W (E_selection_witness D A E)) Q)))).
Proof.
  intro HQ. apply (ns_proof_macro M env (selection_witness_inputs W D C A E P Q)).
  - intros f [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply ns_stopping_self_specialization.
    + apply ns_stopping_self_specialization.
    + apply ns_bound_universal_vacuity.
    + apply ns_bound_universal_vacuity.
    + exact HQ.
  - apply selection_witness_program.
Qed.
Print Assumptions numerical_selection_witness.
