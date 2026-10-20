(** Rebase the literal Collection support witness using the actual forward
    stopping substitution.  No inverse substitution or old-name binder
    absence is assumed.  The output container and support guard are fixed. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps TemplateBinderFresh TemplateNamedSubstitution
  TemplateFormulaFresh NamedBinderFresh StoppingAlpha RawCollectionProfile
  NumericalKP0 NumericalKP0Eligibility ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition E_collection_support_witness T A X Theta :=
  E_wa (E_wa (E_wel T X) (E_wel X A)) Theta.

Lemma collection_support_body_substitution M rho T A X W ThetaX ThetaW x w :
  code_relation M rho X x -> code_relation M rho W w -> x<>zeroM M ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  expression_named_substitution M rho rho x w
    (E_collection_support_witness T A X ThetaX)
    (E_collection_support_witness T A W ThetaW).
Proof.
  intros HX HW HX0 HT HA HTheta.
  assert (RX:expression_named_replace M rho rho x w X W).
  { intros a b Ha Hb. rewrite (code_relation_functional M X rho a x Ha HX),
      (code_relation_functional M W rho b w Hb HW). now left. }
  assert (fixed:forall Q,expression_name_avoids M rho x Q ->
      expression_named_replace M rho rho x w Q Q).
  { intros Q HQ a b Ha Hb. right. split;[exact (HQ a Ha)|].
    symmetry. exact (code_relation_functional M Q rho a b Ha Hb). }
  assert (RT:expression_named_replace M rho rho x w T T) by now apply fixed.
  assert (RA:expression_named_replace M rho rho x w A A) by now apply fixed.
  unfold E_collection_support_witness.
  apply expression_ns_conjunction;[exact HX0| |exact HTheta].
  apply expression_ns_conjunction;[exact HX0| |];
    apply (expression_ns_atom M rho rho x w false);assumption.
Qed.

Lemma collection_support_body_fresh M rho T A X Theta w :
  w<>zeroM M ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_name_avoids M rho w X -> expression_fresh M rho w Theta ->
  expression_fresh M rho w (E_collection_support_witness T A X Theta).
Proof.
  intros HW0 HT HA HX HTheta. unfold E_collection_support_witness.
  apply expression_fresh_conjunction;[exact HW0| |exact HTheta].
  apply expression_fresh_conjunction;[exact HW0| |];
    apply expression_fresh_atom;[now left|exact HT|exact HX|now left|exact HX|exact HA].
Qed.

Theorem numerical_collection_support_witness_rebase M rho T A X W ThetaX ThetaW x w :
  code_relation M rho X x -> code_relation M rho W w ->
  x<>zeroM M -> w<>zeroM M -> x<>w ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_fresh M rho w ThetaX ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim
    (E_wex X (E_collection_support_witness T A X ThetaX))
    (E_wex W (E_collection_support_witness T A W ThetaW))) /\
  ns_proof M rho (E_wim
    (E_wex W (E_collection_support_witness T A W ThetaW))
    (E_wex X (E_collection_support_witness T A X ThetaX))).
Proof.
  intros HX HW HX0 HW0 HXW HTX HAX HTW HAW HF HSub.
  assert (HXW':expression_name_avoids M rho w X).
  { intros u Hu. rewrite (code_relation_functional M X rho u x Hu HX). congruence. }
  pose proof (collection_support_body_fresh M rho T A X ThetaX w HW0 HTW HAW HXW' HF) as HFresh.
  pose proof (collection_support_body_substitution M rho T A X W ThetaX ThetaW x w
    HX HW HX0 HTX HAX HSub) as HSubs.
  destruct (code_relation_total M (E_collection_support_witness T A X ThetaX) rho) as [f Hf].
  destruct (code_relation_total M (E_collection_support_witness T A W ThetaW) rho) as [g Hg].
  exact (proj2 (ns_stopping_alpha M rho X W
    (E_collection_support_witness T A X ThetaX)
    (E_collection_support_witness T A W ThetaW) x w f g
    HX HW Hf Hg HXW (HFresh f Hf) (HSubs f g Hf Hg))).
Qed.

Theorem numerical_collection_support_rebase M rho T A C X W V ThetaX ThetaW x w :
  code_relation M rho X x -> code_relation M rho W w ->
  x<>zeroM M -> w<>zeroM M -> x<>w ->
  expression_name_avoids M rho x T -> expression_name_avoids M rho x A ->
  expression_name_avoids M rho w T -> expression_name_avoids M rho w A ->
  expression_fresh M rho w ThetaX ->
  expression_named_substitution M rho rho x w ThetaX ThetaW ->
  ns_proof M rho (E_wim
    (E_wal V (E_raw_collection_support T A C W V ThetaW))
    (E_wal V (E_raw_collection_support T A C X V ThetaX))) /\
  ns_proof M rho (E_wim
    (E_wal V (E_raw_collection_support T A C X V ThetaX))
    (E_wal V (E_raw_collection_support T A C W V ThetaW))).
Proof.
  intros HX HW HX0 HW0 HXW HTX HAX HTW HAW HF HS.
  destruct (numerical_collection_support_witness_rebase M rho T A X W ThetaX ThetaW x w
    HX HW HX0 HW0 HXW HTX HAX HTW HAW HF HS) as [Forward Backward].
  split.
  - apply (ns_proof_macro M rho
      (E_wim (E_wex W (E_collection_support_witness T A W ThetaW))
        (E_wex X (E_collection_support_witness T A X ThetaX)) :: nil)).
    + intros e [<-|[]]. exact Backward.
    + unfold E_raw_collection_support,E_collection_support_witness.
      apply macro_all_monotone,kp0_implication_map,PM_input;now left.
  - apply (ns_proof_macro M rho
      (E_wim (E_wex X (E_collection_support_witness T A X ThetaX))
        (E_wex W (E_collection_support_witness T A W ThetaW)) :: nil)).
    + intros e [<-|[]]. exact Forward.
    + unfold E_raw_collection_support,E_collection_support_witness.
      apply macro_all_monotone,kp0_implication_map,PM_input;now left.
Qed.

Print Assumptions numerical_collection_support_witness_rebase.
Print Assumptions numerical_collection_support_rebase.
