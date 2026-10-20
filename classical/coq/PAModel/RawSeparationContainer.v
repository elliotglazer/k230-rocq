(** The exact tagged container is a raw domain-Separation container.
    All hypotheses are object formulas with numerical K certificates. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalRawEnvelope NumericalEnvelopeFacts EnvelopeSpecializations
  RawMarkerExclusions RawSeparationPoint RawSeparationAll TaggedMarkerPresence
  NumericalTaggedComprehension QuotientSeparationWitness LiteralMemberSeparationPoint
  QuotedSameContainer NumericalKP0 TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_raw_separation_container M rho T A B C X Z Theta tv av bv cv xv zv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho C cv -> code_relation M rho X xv -> code_relation M rho Z zv ->
  xv<>zeroM M -> zv<>zeroM M -> tv<>xv -> av<>xv -> bv<>xv -> cv<>xv ->
  tv<>zv -> av<>zv -> zv<>xv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B X)
      (E_wim (E_wal X (E_raw_separation_tagged_point T A B C X Theta))
        (E_raw_selection_container T A C X Theta))))).
Proof.
  intros HT HA HB HC HX HZ HX0 HZ0 HTX HAX HBX HCX HTZ HAZ HZX.
  set (Emp:=E_marker_empty T Z). set (DA:=E_wel T A).
  set (Env:=E_raw_envelope T A B X).
  set (Tag:=E_wal X (E_raw_separation_tagged_point T A B C X Theta)).
  set (Sel:=E_raw_member_selection T A C X Theta).
  set (Facts:=E_envelope_facts T A B X).
  set (Neg:=E_wn (E_wel T B)).
  set (Ctx:=E_separation_all_context T A B C X Z Theta).
  set (inputs:=
    E_wim Emp (E_wim DA (E_wim Env Facts)) ::
    E_wim Ctx Sel :: E_wim Tag (E_wel T C) :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[]]]].
    + exact (numerical_raw_envelope_facts M rho T A B X Z tv av bv xv zv
        HT HA HB HX HZ HX0 HTX HAX HBX HZ0 HTZ HAZ).
    + exact (numerical_raw_separation_all M rho T A B C X Z Theta tv bv xv zv
        HT HB HX HZ HX0 HZ0 (not_eq_sym HTZ) HTX HBX HZX).
    + exact (numerical_tagged_marker_presence M rho X B T C (E_wa (E_wel X A) Theta)
        xv tv cv HX HT HC (not_eq_sym HTX) HCX).
  - apply macro_discharge. do 4 apply macro_deduction.
    set (delta:=Tag::Env::DA::Emp::nil).
    assert (HF:macro_derivation nil inputs delta Facts).
    { eapply md_mp with (a:=Env);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=DA);[apply md_hyp;now right;right;left|].
      eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
      apply md_global,PM_input;now left. }
    unfold E_raw_selection_container. apply kp0_md_conjunction.
    + eapply md_mp with (a:=Tag);[apply md_hyp;now left|].
      apply md_global,PM_input;now right;right;left.
    + eapply md_mp with (a:=Ctx).
      * unfold Ctx,E_separation_all_context. apply kp0_md_conjunction.
        -- apply md_hyp;now right;right;right;left.
        -- apply kp0_md_conjunction.
           ++ apply tagged_md_left with (b:=E_wn (E_weq B T)),
                tagged_md_right with (a:=E_wa (E_wel A B) (E_envelope_domain_all T B X)). exact HF.
           ++ apply kp0_md_conjunction;apply md_hyp;cbn;tauto.
      * apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_raw_separation_container.
