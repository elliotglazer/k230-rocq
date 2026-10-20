(** Project a theta-free consequence before specializing at the marker.
    The arbitrary predicate need not be binder-fresh at that marker. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros TemplatePropositional QuantifierMacros NamedLeibnizSteps NamedAlpha
  NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution StoppingInstantiation
  NumericalTaggedComprehension NumericalKP0 QuotientSeparationWitness
  QuotientAtomTemplates ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma tagged_marker_reverse_projection M rho Y B T C Theta :
  ns_proof M rho
    (E_wim (E_selection_iff (E_wel Y C) (E_tagged_profile Y B T Theta))
      (E_wim (E_weq Y T) (E_wel Y C))).
Proof.
  apply ns_proof_macro with (inputs:=nil);[intros e []|].
  apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=E_tagged_profile Y B T Theta).
  - unfold E_tagged_profile.
    eapply md_mp with (a:=E_or (E_weq Y T) (E_wa (E_wel Y B) Theta)).
    + eapply md_mp with (a:=E_weq Y T);[apply md_hyp;now left|].
      apply md_global,PM_template,template_or_left.
    + apply md_global,PM_template,template_or_right.
  - apply tagged_md_right with (a:=E_wim (E_wel Y C) (E_tagged_profile Y B T Theta)).
    apply md_hyp;now right;left.
Qed.

Lemma marker_implication_specialize M rho Y T C yv tv cv :
  code_relation M rho Y yv -> code_relation M rho T tv -> code_relation M rho C cv ->
  yv<>tv -> cv<>yv ->
  ns_proof M rho
    (E_wim (E_wal Y (E_wim (E_weq Y T) (E_wel Y C)))
      (E_wim (E_weq T T) (E_wel T C))).
Proof.
  intros HY HT HC HYT HCY.
  set (F:=E_wim (E_weq Y T) (E_wel Y C)).
  set (G:=E_wim (E_weq T T) (E_wel T C)).
  assert (RY:expression_named_replace M rho rho yv tv Y T).
  { intros u v HU HV. rewrite (code_relation_functional M Y rho u yv HU HY),
      (code_relation_functional M T rho v tv HV HT). now left. }
  assert (RT:expression_named_replace M rho rho yv tv T T).
  { intros u v HU HV. rewrite (code_relation_functional M T rho u tv HU HT),
      (code_relation_functional M T rho v tv HV HT). right;split;[congruence|reflexivity]. }
  assert (RC:expression_named_replace M rho rho yv tv C C).
  { intros u v HU HV. rewrite (code_relation_functional M C rho u cv HU HC),
      (code_relation_functional M C rho v cv HV HC). now right. }
  assert (HS:expression_named_substitution M rho rho yv tv F G).
  { unfold F,G. apply expression_ns_implication.
    - apply (expression_ns_atom M rho rho yv tv true);assumption.
    - apply (expression_ns_atom M rho rho yv tv false);assumption. }
  assert (HAbs:expression_binder_absent M rho tv F).
  { unfold F. apply expression_binder_absent_implication;apply expression_binder_absent_atom;auto. }
  destruct (code_relation_total M F rho) as [f HF].
  destruct (code_relation_total M G rho) as [g HG].
  exact (proj1 (ns_stopping_instantiation M rho Y T F G yv tv f g
    HY HT HF HG HYT (HAbs f HF) (HS f g HF HG))).
Qed.

Theorem numerical_tagged_marker_presence M rho Y B T C Theta yv tv cv :
  code_relation M rho Y yv -> code_relation M rho T tv -> code_relation M rho C cv ->
  yv<>tv -> cv<>yv ->
  ns_proof M rho
    (E_wim (E_wal Y (E_selection_iff (E_wel Y C) (E_tagged_profile Y B T Theta)))
      (E_wel T C)).
Proof.
  intros HY HT HC HYT HCY.
  set (All:=E_wal Y (E_selection_iff (E_wel Y C) (E_tagged_profile Y B T Theta))).
  set (Simple:=E_wal Y (E_wim (E_weq Y T) (E_wel Y C))).
  apply (ns_proof_macro M rho
    (E_wim All Simple :: E_wim Simple (E_wim (E_weq T T) (E_wel T C)) :: E_weq T T :: nil)).
  - intros e [<-|[<-|[<-|[]]]].
    + apply ns_proof_all_monotone,tagged_marker_reverse_projection.
    + exact (marker_implication_specialize M rho Y T C yv tv cv HY HT HC HYT HCY).
    + apply ns_proof_reflexivity.
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_weq T T);[apply md_global,PM_input;now right;right;left|].
    eapply md_mp with (a:=Simple).
    + eapply md_mp with (a:=All);[apply md_hyp;now left|]. apply md_global,PM_input;now left.
    + apply md_global,PM_input;now right;left.
Qed.

Print Assumptions tagged_marker_reverse_projection.
Print Assumptions marker_implication_specialize.
Print Assumptions numerical_tagged_marker_presence.
