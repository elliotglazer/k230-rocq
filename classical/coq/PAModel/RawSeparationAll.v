(** Lift the raw Separation point calculation to every domain element.
    The two universally quantified inputs carry explicit vacuity proofs. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalVacuitySteps TemplateFormulaFresh NumericalKP0Eligibility
  NumericalRawEnvelope NumericalTaggedComprehension RawMarkerExclusions RawMarkerQuantifiers
  RawSeparationPoint EnvelopeSpecializations QuotientSeparationWitness LiteralMemberSeparationPoint
  StoppingSpecialization BoundVariableVacuityRules NumericalKP0
  TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_separation_all_context T A B C X Z Theta :=
  E_wa (E_marker_empty T Z) (E_wa (E_wn (E_wel T B))
    (E_wa (E_raw_envelope T A B X) (E_wal X (E_raw_separation_tagged_point T A B C X Theta)))).

Theorem numerical_raw_separation_all M rho T A B C X Z Theta tv bv xv zv :
  code_relation M rho T tv -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  xv<>zeroM M -> zv<>zeroM M -> zv<>tv -> tv<>xv -> bv<>xv -> zv<>xv ->
  ns_proof M rho (E_wim (E_separation_all_context T A B C X Z Theta)
    (E_raw_member_selection T A C X Theta)).
Proof.
  intros HT HB HX HZ HX0 HZ0 HZT HTX HBX HZX.
  set (Emp:=E_marker_empty T Z). set (Neg:=E_wn (E_wel T B)).
  set (EP:=E_envelope_point T A B X).
  set (TP:=E_raw_separation_tagged_point T A B C X Theta).
  set (EA:=E_wal X EP). set (TA:=E_wal X TP).
  set (CP:=E_raw_separation_clean_point T A C X Theta).
  set (Ctx:=E_wa Emp (E_wa Neg (E_wa EA TA))).
  assert (HPoint:ns_proof M rho (E_wim Ctx CP)).
  { apply (ns_proof_macro M rho
      (E_wim EA EP :: E_wim TA TP :: E_wim Emp (E_wim Neg (E_wim EP (E_wim TP CP))) :: nil)).
    - intros e [<-|[<-|[<-|[]]]].
      + apply ns_stopping_self_specialization.
      + apply ns_stopping_self_specialization.
      + exact (numerical_raw_separation_point M rho T A B C X Z Theta tv zv HT HZ HZ0 HZT).
    - apply macro_discharge,macro_deduction.
      eapply md_mp with (a:=TP).
      + eapply md_mp with (a:=TA).
        * apply tagged_md_right with (a:=EA),tagged_md_right with (a:=Neg),
            tagged_md_right with (a:=Emp),md_hyp;now left.
        * apply md_global,PM_input;now right;left.
      + eapply md_mp with (a:=EP).
        * eapply md_mp with (a:=EA).
          -- apply tagged_md_left with (b:=TA),tagged_md_right with (a:=Neg),
               tagged_md_right with (a:=Emp),md_hyp;now left.
          -- apply md_global,PM_input;now left.
        * eapply md_mp with (a:=Neg).
          -- apply tagged_md_left with (b:=E_wa EA TA),tagged_md_right with (a:=Emp),md_hyp;now left.
          -- eapply md_mp with (a:=Emp).
             ++ apply tagged_md_left with (b:=E_wa Neg (E_wa EA TA)),md_hyp;now left.
             ++ apply md_global,PM_input;now right;right;left. }
  assert (HV:ns_proof M rho (E_vac X Ctx)).
  { apply (ns_proof_macro M rho (E_vac X Emp :: E_vac X Neg :: E_vac X EA :: E_vac X TA :: nil)).
    - intros e [<-|[<-|[<-|[<-|[]]]]].
      + apply (kp0_expression_fresh_vacuity M rho X Emp xv HX).
        exact (marker_empty_fresh M rho T Z tv zv xv HT HZ HX0 HTX HZX).
      + apply (kp0_expression_fresh_vacuity M rho X Neg xv HX).
        apply expression_fresh_negation;[exact HX0|]. apply expression_fresh_atom;[now left| |].
        * exact (marker_name_avoids M rho T tv xv HT HTX).
        * exact (marker_name_avoids M rho B bv xv HB HBX).
      + apply ns_bound_universal_vacuity.
      + apply ns_bound_universal_vacuity.
    - unfold Ctx. apply kp0_vacuous_conjunction;[apply PM_input;now left|].
      apply kp0_vacuous_conjunction;[apply PM_input;now right;left|].
      apply kp0_vacuous_conjunction;apply PM_input;cbn;tauto. }
  exact (marker_generalize_one M rho X Ctx CP HV HPoint).
Qed.

Print Assumptions numerical_raw_separation_all.
