(** Use the raw domain envelope in the input direction of Collection. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalKP0Eligibility NumericalVacuitySteps TemplateFormulaFresh
  RawMarkerExclusions RawMarkerQuantifiers NumericalRawEnvelope NumericalEnvelopeFacts
  EnvelopeSpecializations ProofMacros QuantifierMacros TemplateCD TemplatePropositional
  NumericalKP0 NumericalTaggedComprehension NumericalBootstrap QuotientAtomTemplates
  ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_envelope_member M rho T A B Q X tv av bv qv xv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho Q qv -> code_relation M rho X xv ->
  qv<>zeroM M -> qv<>xv -> tv<>qv -> av<>qv -> bv<>qv ->
  ns_proof M rho (E_wim (E_raw_envelope T A B Q)
    (E_wim (E_wa (E_wel T X) (E_wel X A)) (E_wel X B))).
Proof.
  intros HT HA HB HQ HX HQ0 HQX HTQ HAQ HBQ.
  apply (ns_proof_macro M rho
    (E_wim (E_raw_envelope T A B Q) (E_envelope_point T A B X) :: nil)).
  - intros e [<-|[]]. exact (numerical_envelope_specialize M rho T A B Q X tv av bv qv xv
      HT HA HB HQ HX HQ0 HQX HTQ HAQ HBQ).
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_envelope_case T A X).
    + unfold E_envelope_case. eapply md_mp with (a:=E_wa (E_wel X A) (E_wel T X)).
      * apply kp0_md_conjunction.
        -- apply tagged_md_right with (a:=E_wel T X),md_hyp;now left.
        -- apply tagged_md_left with (b:=E_wel X A),md_hyp;now left.
      * apply md_global,PM_template,template_or_right.
    + apply tagged_md_right with (a:=E_wim (E_wel X B) (E_envelope_case T A X)).
      eapply md_mp with (a:=E_raw_envelope T A B Q);[apply md_hyp;now right;left|].
      apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_envelope_member.
