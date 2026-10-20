(** A subset of a known member is an eligible KP0 input. All names and
    proofs below live in the arbitrary arithmetic model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NumericalEquality NamedLeibnizSteps NamedBinderFresh
  TemplateBinderFresh TemplateNamedSubstitution StoppingInstantiation
  NumericalKP0Eligibility NumericalKP0Requests NumericalTaggedComprehension
  TemplatePropositional ProofMacros QuantifierMacros QuotientAtomTemplates ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_tagged_eligibility M rho P B K Y Root pv bv kv yv :
  code_relation M rho P pv -> code_relation M rho B bv ->
  code_relation M rho K kv -> code_relation M rho Y yv ->
  yv<>zeroM M -> yv<>bv -> kv<>yv -> kv<>bv -> pv<>yv ->
  ns_proof M rho (E_wim (E_wa (E_wel B K) (E_ksubset P B K))
    (E_kp_eligible Root Y K P)).
Proof.
  intros HP HB HK HY H0 HYB HKY HKB HPY.
  set (A:=E_wa (E_wel Y K) (E_ksubset P Y K)).
  set (V:=E_wa (E_wel B K) (E_ksubset P B K)).
  assert (RY:expression_named_replace M rho rho yv bv Y B).
  { intros u v HU HV. rewrite (code_relation_functional M Y rho u yv HU HY),
      (code_relation_functional M B rho v bv HV HB). now left. }
  assert (RK:expression_named_replace M rho rho yv bv K K).
  { intros u v HU HV. rewrite (code_relation_functional M K rho u kv HU HK),
      (code_relation_functional M K rho v kv HV HK). now right. }
  assert (RP:expression_named_replace M rho rho yv bv P P).
  { intros u v HU HV. rewrite (code_relation_functional M P rho u pv HU HP),
      (code_relation_functional M P rho v pv HV HP). now right. }
  assert (S:expression_named_substitution M rho rho yv bv A V).
  { unfold A,V. apply expression_ns_conjunction;[exact H0| |].
    - apply (expression_ns_atom M rho rho yv bv false);assumption.
    - unfold E_ksubset. apply (expression_ns_universal M rho rho yv bv K K _ _ kv HK HK HKY HKB).
      apply expression_ns_implication;apply (expression_ns_atom M rho rho yv bv false);assumption. }
  assert (HA:expression_binder_absent M rho bv A).
  { unfold A. apply expression_binder_absent_conjunction.
    - apply expression_binder_absent_atom;now left.
    - unfold E_ksubset. apply expression_binder_absent_universal.
      + intros v Hv. now rewrite (code_relation_functional M K rho v kv Hv HK).
      + apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left. }
  destruct (code_relation_total M A rho) as [a Ha].
  destruct (code_relation_total M V rho) as [v Hv].
  pose proof (proj2 (ns_stopping_instantiation M rho Y B A V yv bv a v
    HY HB Ha Hv HYB (HA a Ha) (S a v Ha Hv))) as Intro.
  apply (ns_proof_macro M rho (E_wim V (E_wex Y A) :: nil)).
  - intros e [<-|[]]. exact Intro.
  - unfold E_kp_eligible. eapply macro_syl;[apply PM_input;now left|].
    apply PM_template,template_or_right.
Qed.

Print Assumptions numerical_tagged_eligibility.
