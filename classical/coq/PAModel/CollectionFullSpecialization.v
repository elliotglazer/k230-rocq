(** Specialization of the full request at a fresh singleton-container name.
    Unlike exceptional requests, this retains the arbitrary relation. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedSubstitution NamedBinderFresh TemplateBinderFresh
  TemplateFormulaFresh TemplateNamedSubstitution StoppingInstantiation
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests QuotientAtomTemplates
  CollectionSupportCleanup CollectionMatrixInstance CollectionKernel.
Unset Implicit Arguments.

Definition E_collection_request_at T A B R C P W V Theta Z :=
  E_wim (E_kp_eligible R V C P)
    (E_kp_request V C (E_collection_choices T A B R P W V Theta Z)).

Lemma generic_request_at_substitution M rho R C P J V F G p j c v :
  code_relation M rho P p -> code_relation M rho J j ->
  code_relation M rho C c -> code_relation M rho V v ->
  p<>zeroM M -> c<>p -> c<>j -> v<>p -> v<>j ->
  expression_name_avoids M rho p R ->
  expression_named_substitution M rho rho p j F G ->
  expression_named_substitution M rho rho p j
    (E_wim (E_kp_eligible R V C P) (E_kp_request V C F))
    (E_wim (E_kp_eligible R V C J) (E_kp_request V C G)).
Proof.
  intros HP HJ HC HV H0 HCP HCJ HVP HVJ HR HFG.
  assert (RP:expression_named_replace M rho rho p j P J).
  { intros x y HX HY. rewrite (code_relation_functional M P rho x p HX HP),
      (code_relation_functional M J rho y j HY HJ). now left. }
  assert (fixed:forall X,expression_name_avoids M rho p X -> expression_named_replace M rho rho p j X X).
  { intros X HX x y Hx Hy. right. split;[exact (HX x Hx)|].
    symmetry. exact (code_relation_functional M X rho x y Hx Hy). }
  assert (RR:expression_named_replace M rho rho p j R R) by now apply fixed.
  assert (RC:expression_named_replace M rho rho p j C C).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M C rho x c HX HC). }
  assert (RV:expression_named_replace M rho rho p j V V).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M V rho x v HX HV). }
  apply expression_ns_implication.
  - unfold E_kp_eligible. apply expression_ns_disjunction;[exact H0| |].
    + apply (expression_ns_atom M rho rho p j true);assumption.
    + apply (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ).
      apply expression_ns_conjunction;[exact H0| |].
      * apply (expression_ns_atom M rho rho p j false);assumption.
      * unfold E_ksubset. apply (expression_ns_universal M rho rho p j C C _ _ c HC HC HCP HCJ).
        apply expression_ns_implication;apply (expression_ns_atom M rho rho p j false);assumption.
  - unfold E_kp_request. apply expression_ns_implication.
    + exact (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ HFG).
    + apply (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ).
      apply expression_ns_conjunction;[exact H0| |exact HFG].
      apply (expression_ns_atom M rho rho p j false);assumption.
Qed.

Theorem numerical_generic_request_specialization M rho R C P J V F G p j c v :
  code_relation M rho P p -> code_relation M rho J j ->
  code_relation M rho C c -> code_relation M rho V v ->
  p<>zeroM M -> p<>j -> c<>p -> c<>j -> v<>p -> v<>j ->
  expression_name_avoids M rho p R -> expression_binder_absent M rho j F ->
  expression_named_substitution M rho rho p j F G ->
  ns_proof M rho (E_wim (E_wal P (E_wim (E_kp_eligible R V C P) (E_kp_request V C F)))
    (E_wim (E_kp_eligible R V C J) (E_kp_request V C G))).
Proof.
  intros HP HJ HC HV H0 HPJ HCP HCJ HVP HVJ HR HF HFG.
  set (A:=E_wim (E_kp_eligible R V C P) (E_kp_request V C F)).
  set (B:=E_wim (E_kp_eligible R V C J) (E_kp_request V C G)).
  assert (HAbs:expression_binder_absent M rho j A).
  { unfold A,E_kp_eligible. apply expression_binder_absent_implication.
    - apply expression_binder_absent_disjunction;[apply expression_binder_absent_atom;now right|].
      apply expression_binder_absent_existential.
      + intros x HX. now rewrite (code_relation_functional M V rho x v HX HV).
      + apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
        unfold E_ksubset. apply expression_binder_absent_universal.
        * intros x HX. now rewrite (code_relation_functional M C rho x c HX HC).
        * apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left.
    - apply (request_binder_absent M rho V C F v j HV HVJ HF). }
  destruct (code_relation_total M A rho) as [a HA].
  destruct (code_relation_total M B rho) as [b HB].
  exact (proj1 (ns_stopping_instantiation M rho P J A B p j a b HP HJ HA HB HPJ
    (HAbs a HA) (generic_request_at_substitution M rho R C P J V F G p j c v
      HP HJ HC HV H0 HCP HCJ HVP HVJ HR HFG a b HA HB))).
Qed.

Theorem numerical_collection_full_specialization M rho T A B R C P J W V Theta Z p j c w v z :
  code_relation M rho P p -> code_relation M rho J j -> code_relation M rho C c ->
  code_relation M rho W w -> code_relation M rho V v -> code_relation M rho Z z ->
  p<>zeroM M -> p<>j -> c<>p -> c<>j -> w<>p -> w<>j -> v<>p -> v<>j -> z<>p -> z<>j ->
  expression_name_avoids M rho p T -> expression_name_avoids M rho p A ->
  expression_name_avoids M rho p B -> expression_name_avoids M rho p R ->
  expression_fresh M rho p Theta -> expression_binder_absent M rho j Theta ->
  ns_proof M rho (E_wim (E_collection_requests T A B R C P W V Theta Z)
    (E_collection_request_at T A B R C J W V Theta Z)).
Proof.
  intros HP HJ HC HW HV HZ H0 HPJ HCP HCJ HWP HWJ HVP HVJ HZP HZJ HT HA HB HR HTheta HBind.
  apply (numerical_generic_request_specialization M rho R C P J V
    (E_collection_choices T A B R P W V Theta Z) (E_collection_choices T A B R J W V Theta Z)
    p j c v HP HJ HC HV H0 HPJ HCP HCJ HVP HVJ HR).
  - exact (collection_matrix_binder_absent M rho j T A B R P W V Theta Z w z HW HZ HWJ HZJ HBind).
  - apply (collection_matrix_input_substitution M rho T A B R P J W V Theta Z p j w z
      HP HJ HW HZ H0 HWP HWJ HZP HZJ HT HA HB HR).
    + intros x HX. now rewrite (code_relation_functional M V rho x v HX HV).
    + exact HTheta.
    + exact HBind.
Qed.

Print Assumptions generic_request_at_substitution.
Print Assumptions numerical_generic_request_specialization.
Print Assumptions numerical_collection_full_specialization.
