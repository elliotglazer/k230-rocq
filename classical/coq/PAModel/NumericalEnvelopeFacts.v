(** Numerical version of KDomain.domain_envelope_facts. The proof uses
    the actual raw-envelope profile and raw empty marker. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  TemplateCD TemplatePropositional ProofMacros QuantifierMacros NumericalVacuitySteps NumericalEquality
  NamedLeibnizSteps NamedAlpha NumericalRawEnvelope NumericalTaggedComprehension NumericalBootstrap
  TemplateFormulaFresh ContextualPropositional NumericalKP0 NumericalKP0Eligibility BoundVariableVacuityRules RawMarkerExclusions RawMarkerQuantifiers
  EnvelopeSpecializations.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_envelope_domain_all T B X := E_wal X (E_wim (E_wel X B) (E_wel T X)).
Definition E_envelope_facts T A B X :=
  E_wa (E_wa (E_wel A B) (E_envelope_domain_all T B X))
    (E_wa (E_wn (E_wel T B)) (E_wn (E_weq B T))).

Lemma envelope_eq_domain M rho T A X :
  ns_proof M rho (E_wim (E_weq X A) (E_wim (E_wel T A) (E_wel T X))).
Proof.
  apply (ns_proof_syl M rho (E_weq X A) (E_weq A X) (E_wim (E_wel T A) (E_wel T X))).
  - apply ns_proof_symmetry.
  - apply marker_membership_transport.
Qed.

Theorem numerical_envelope_root M rho T A B X tv av bv xv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> xv<>zeroM M -> tv<>xv -> av<>xv -> bv<>xv ->
  ns_proof M rho (E_wim (E_raw_envelope T A B X) (E_wel A B)).
Proof.
  intros HT HA HB HX H0 HTX HAX HBX.
  apply (ns_proof_macro M rho
    (E_wim (E_raw_envelope T A B X) (E_envelope_point T A B A) :: E_weq A A :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_envelope_specialize M rho T A B X A tv av bv xv av HT HA HB HX HA H0
        (fun E=>HAX (eq_sym E)) HTX HAX HBX).
    + apply ns_proof_reflexivity.
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_envelope_case T A A).
    + eapply md_mp with (a:=E_weq A A).
      * apply md_global,PM_input;now right;left.
      * unfold E_envelope_case. apply md_global,PM_template,template_or_left.
    + apply tagged_md_right with (a:=E_wim (E_wel A B) (E_envelope_case T A A)).
      eapply md_mp with (a:=E_raw_envelope T A B X).
      * apply md_hyp;now left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_envelope_domains M rho T A B X tv av xv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho X xv ->
  tv<>xv -> av<>xv ->
  ns_proof M rho (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B X) (E_envelope_domain_all T B X))).
Proof.
  intros HT HA HX HTX HAX.
  assert (HPoint:ns_proof M rho (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B X) (E_wim (E_wel X B) (E_wel T X))))).
  { apply (ns_proof_macro M rho
      (E_wim (E_weq X A) (E_wim (E_wel T A) (E_wel T X)) ::
       E_wim (E_raw_envelope T A B X) (E_envelope_point T A B X) :: nil)).
    - intros e [<-|[<-|[]]].
      + apply envelope_eq_domain.
      + apply numerical_envelope_self.
    - assert (HCases:proof_macro nil
        (E_wim (E_weq X A) (E_wim (E_wel T A) (E_wel T X)) ::
         E_wim (E_raw_envelope T A B X) (E_envelope_point T A B X) :: nil)
        (E_wim (E_envelope_case T A X) (E_wim (E_wel T A) (E_wel T X)))).
      { unfold E_envelope_case. apply tagged_or_cases.
        + apply PM_input;now left.
        + eapply macro_syl;[apply PM_template,bootstrap_projection_right|apply PM_template,template_K]. }
      apply macro_discharge. do 3 apply macro_deduction.
      eapply md_mp with (a:=E_wel T A);[apply md_hyp;now right;right;left|].
      eapply md_mp with (a:=E_envelope_case T A X).
      + eapply md_mp with (a:=E_wel X B);[apply md_hyp;now left|].
        apply tagged_md_left with (b:=E_wim (E_envelope_case T A X) (E_wel X B)).
        eapply md_mp with (a:=E_raw_envelope T A B X).
        * apply md_hyp;now right;left.
        * apply md_global,PM_input;now right;left.
      + apply md_global;exact HCases. }
  apply marker_generalize_two.
  - apply (kp0_expression_fresh_vacuity M rho X (E_wel T A) xv HX).
    apply expression_fresh_atom;[now left| |];eapply marker_name_avoids;eassumption.
  - apply ns_bound_universal_vacuity.
  - exact HPoint.
Qed.

Print Assumptions numerical_envelope_root.
Print Assumptions numerical_envelope_domains.

Theorem numerical_envelope_not_domain M rho T A B X Z tv av bv xv zv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  tv<>xv -> av<>xv -> bv<>xv -> zv<>zeroM M -> tv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B X) (E_wn (E_wel T B))))).
Proof.
  intros HT HA HB HX HZ HTX HAX HBX HZ0 HTZ.
  apply (ns_proof_macro M rho
    (E_wim (E_wel T A) (E_wim (E_raw_envelope T A B X) (E_envelope_domain_all T B X)) ::
     E_wim (E_envelope_domain_all T B X) (E_wim (E_wel T B) (E_wel T T)) ::
     E_wim (E_marker_empty T Z) (E_wn (E_wel T T)) :: nil)).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (numerical_envelope_domains M rho T A B X tv av xv HT HA HX HTX HAX).
    + exact (numerical_domain_profile_specialize M rho T B X T tv bv xv tv HT HB HX HT
        (fun E=>HTX (eq_sym E)) HTX HBX).
    + exact (marker_empty_specialization M rho T Z T tv zv tv HT HZ HT HZ0
        (fun E=>HTZ (eq_sym E)) HTZ).
  - apply macro_discharge. do 4 apply macro_deduction.
    eapply md_mp with (a:=E_wel T T).
    + eapply md_mp with (a:=E_wel T B);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_envelope_domain_all T B X).
      * eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now right;left|].
        eapply md_mp with (a:=E_wel T A);[apply md_hyp;now right;right;left|].
        apply md_global,PM_input;now left.
      * apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;right;left|].
      apply md_global,PM_input;now right;right;left.
Qed.

Theorem numerical_envelope_not_marker M rho T A B X Z tv av bv xv zv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  xv<>zeroM M -> tv<>xv -> av<>xv -> bv<>xv ->
  zv<>zeroM M -> tv<>zv -> av<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z)
    (E_wim (E_raw_envelope T A B X) (E_wn (E_weq B T)))).
Proof.
  intros HT HA HB HX HZ HX0 HTX HAX HBX HZ0 HTZ HAZ.
  apply (ns_proof_macro M rho
    (E_wim (E_raw_envelope T A B X) (E_wel A B) ::
     E_wim (E_weq B T) (E_wim (E_wel A B) (E_wel A T)) ::
     E_wim (E_marker_empty T Z) (E_wn (E_wel A T)) :: nil)).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (numerical_envelope_root M rho T A B X tv av bv xv HT HA HB HX HX0 HTX HAX HBX).
    + apply marker_membership_transport.
    + exact (marker_empty_specialization M rho T Z A tv zv av HT HZ HA HZ0
        (fun E=>HAZ (eq_sym E)) HTZ).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_wel A T).
    + eapply md_mp with (a:=E_wel A B).
      * eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now right;left|].
        apply md_global,PM_input;now left.
      * eapply md_mp with (a:=E_weq B T);[apply md_hyp;now left|].
        apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now right;right;left.
Qed.

Theorem numerical_raw_envelope_facts M rho T A B X Z tv av bv xv zv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  xv<>zeroM M -> tv<>xv -> av<>xv -> bv<>xv ->
  zv<>zeroM M -> tv<>zv -> av<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B X) (E_envelope_facts T A B X)))).
Proof.
  intros HT HA HB HX HZ HX0 HTX HAX HBX HZ0 HTZ HAZ.
  set (inputs:=
    E_wim (E_raw_envelope T A B X) (E_wel A B) ::
    E_wim (E_wel T A) (E_wim (E_raw_envelope T A B X) (E_envelope_domain_all T B X)) ::
    E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
      (E_wim (E_raw_envelope T A B X) (E_wn (E_wel T B)))) ::
    E_wim (E_marker_empty T Z) (E_wim (E_raw_envelope T A B X) (E_wn (E_weq B T))) :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact (numerical_envelope_root M rho T A B X tv av bv xv HT HA HB HX HX0 HTX HAX HBX).
    + exact (numerical_envelope_domains M rho T A B X tv av xv HT HA HX HTX HAX).
    + exact (numerical_envelope_not_domain M rho T A B X Z tv av bv xv zv HT HA HB HX HZ HTX HAX HBX HZ0 HTZ).
    + exact (numerical_envelope_not_marker M rho T A B X Z tv av bv xv zv HT HA HB HX HZ HX0 HTX HAX HBX HZ0 HTZ HAZ).
  - apply macro_discharge. do 3 apply macro_deduction.
    unfold E_envelope_facts. apply kp0_md_conjunction;apply kp0_md_conjunction.
    + eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now left|].
      apply md_global,PM_input;unfold inputs;now left.
    + eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wel T A);[apply md_hyp;now right;left|].
      apply md_global,PM_input;unfold inputs;now right;left.
    + eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wel T A);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;unfold inputs;now right;right;left.
    + eapply md_mp with (a:=E_raw_envelope T A B X);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;unfold inputs;now right;right;right;left.
Qed.

Print Assumptions numerical_envelope_not_domain.
Print Assumptions numerical_envelope_not_marker.
Print Assumptions numerical_raw_envelope_facts.
