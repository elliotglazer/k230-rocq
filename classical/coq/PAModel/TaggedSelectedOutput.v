(** A selected element supplies the third tagged output branch. Only the
    predicate's genuine source-to-witness substitution is an input. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NamedBinderFresh TemplateBinderFresh TemplateFormulaFresh
  TemplateNamedSubstitution NumericalSingleton NumericalTaggedComprehension
  NumericalKP0 TemplatePropositional ProofMacros QuantifierMacros
  QuotientAtomTemplates ContextualPropositional.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_tagged_selected_output M rho Y X P B T R Theta ThetaX Z y x z :
  code_relation M rho Y y -> code_relation M rho X x -> code_relation M rho Z z ->
  y<>zeroM M -> y<>x -> z<>y -> z<>x ->
  expression_name_avoids M rho y P -> expression_name_avoids M rho y B ->
  expression_name_avoids M rho y T -> expression_name_avoids M rho y R ->
  expression_named_substitution M rho rho y x Theta ThetaX ->
  expression_binder_absent M rho x Theta ->
  ns_proof M rho (E_wim
    (E_wa (E_raw_singleton X P Z) (E_wa (E_wel X B) ThetaX))
    (E_wex Y (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z)))).
Proof.
  intros HY HX HZ H0 HYX HZY HZX HP HB HT HR HTheta HBind.
  assert (RY:expression_named_replace M rho rho y x Y X).
  { intros a b HA HB'. rewrite (code_relation_functional M Y rho a y HA HY),
      (code_relation_functional M X rho b x HB' HX). now left. }
  assert (fixed:forall A,expression_name_avoids M rho y A ->
    expression_named_replace M rho rho y x A A).
  { intros A HA a b Ha Hb. right. split;[exact (HA a Ha)|].
    symmetry. exact (code_relation_functional M A rho a b Ha Hb). }
  assert (RZ:expression_named_replace M rho rho y x Z Z).
  { apply fixed. intros a HA. now rewrite (code_relation_functional M Z rho a z HA HZ). }
  assert (SS:expression_named_substitution M rho rho y x
    (E_raw_singleton Y P Z) (E_raw_singleton X P Z)).
  { unfold E_raw_singleton. apply expression_ns_conjunction;[exact H0| |].
    - apply (expression_ns_atom M rho rho y x false);[exact RY|exact (fixed P HP)].
    - apply (expression_ns_universal M rho rho y x Z Z _ _ z HZ HZ HZY HZX).
      apply expression_ns_implication.
      + apply (expression_ns_atom M rho rho y x false);[exact RZ|exact (fixed P HP)].
      + apply (expression_ns_atom M rho rho y x true);assumption. }
  assert (BS:expression_binder_absent M rho x (E_raw_singleton Y P Z)).
  { unfold E_raw_singleton. apply expression_binder_absent_conjunction.
    - apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_universal.
      + intros a HA. now rewrite (code_relation_functional M Z rho a z HA HZ).
      + apply expression_binder_absent_implication;apply expression_binder_absent_atom;auto. }
  pose proof (numerical_tagged_output_intro M rho y x Y X P B T R Theta ThetaX
    (E_raw_singleton Y P Z) (E_raw_singleton X P Z) HY HX HYX H0 RY
    (fixed P HP) (fixed B HB) (fixed T HT) (fixed R HR) HTheta SS HBind BS) as HIntro.
  apply (ns_proof_macro M rho
    (E_wim (E_tagged_choices X P B T R ThetaX (E_raw_singleton X P Z))
      (E_wex Y (E_tagged_choices Y P B T R Theta (E_raw_singleton Y P Z))) :: nil)).
  - intros e [<-|[]]. exact HIntro.
  - eapply macro_syl;[|apply PM_input;now left].
    unfold E_tagged_choices. eapply macro_syl;apply PM_template,template_or_right.
Qed.

Print Assumptions numerical_tagged_selected_output.
