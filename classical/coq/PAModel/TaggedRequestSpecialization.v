(** Specialize the constructed universal request at a root, marker, or
    singleton name. The arbitrary predicate is fixed by source freshness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates NumericalEquality NamedLeibnizSteps
  FreshNames NamedSubstitution NamedBinderFresh TemplateBinderFresh
  TemplateFormulaFresh TemplateNamedSubstitution StoppingInstantiation
  NumericalKP0Requests NumericalKP0Eligibility NumericalSingleton
  NumericalTaggedMatrix NumericalTaggedComprehension NumericalTaggedKernel
  TaggedMatrixSubstitution QuotientAtomTemplates.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition tagged_specialization_parameters M y p q carrier marker root container z theta :=
  y .: p .: q .: carrier .: marker .: root .: container .: z .: theta .: fun _=>zeroM M.

Theorem numerical_tagged_request_specialization M y p q carrier marker root container z theta :
  p<>zeroM M -> p<>q -> y<>p -> y<>q -> container<>p -> container<>q ->
  z<>p -> z<>q -> carrier<>p -> marker<>p -> root<>p ->
  formula_fresh M theta p -> named_binder_absent M theta q ->
  ns_proof M (tagged_specialization_parameters M y p q carrier marker root container z theta)
    (E_wim
      (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 3) (CEvar 4)
        (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
      (E_tagged_local_request (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4)
        (CEvar 5) (CEvar 6) (CEvar 8) (E_raw_singleton (CEvar 0) (CEvar 2) (CEvar 7)))).
Proof.
  intros HP0 HPQ HYP HYQ HKP HKQ HZP HZQ HBP HTP HRP HTheta HBind.
  set (rho:=tagged_specialization_parameters M y p q carrier marker root container z theta).
  set (A:=E_tagged_local_request (CEvar 0) (CEvar 1) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (E_raw_singleton (CEvar 0) (CEvar 1) (CEvar 7))).
  set (B:=E_tagged_local_request (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (E_raw_singleton (CEvar 0) (CEvar 2) (CEvar 7))).
  assert (same:forall idx v, rho idx=v -> v<>p ->
    expression_named_replace M rho rho p q (CEvar idx) (CEvar idx)).
  { intros idx v E HV a b HA HB. change (a=rho idx) in HA. change (b=rho idx) in HB.
    subst a b. right;split;congruence. }
  assert (RY:expression_named_replace M rho rho p q (CEvar 0) (CEvar 0)) by exact (same 0 y eq_refl HYP).
  assert (RK:expression_named_replace M rho rho p q (CEvar 6) (CEvar 6)) by exact (same 6 container eq_refl HKP).
  assert (RR:expression_named_replace M rho rho p q (CEvar 5) (CEvar 5)) by exact (same 5 root eq_refl HRP).
  assert (RP:expression_named_replace M rho rho p q (CEvar 1) (CEvar 2)).
  { intros a b HA HB. change (a=p) in HA. change (b=q) in HB. subst a b. now left. }
  assert (SM:expression_named_substitution M rho rho p q
    (E_tagged_matrix (CEvar 0) (CEvar 1) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 7))
    (E_tagged_matrix (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 7))).
  { apply (tagged_matrix_input_substitution M rho (CEvar 0) (CEvar 1) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 7) p q z
      eq_refl eq_refl eq_refl HP0 HZP HZQ).
    - intros v Hv. change (v=y) in Hv. now subst v.
    - intros v Hv. change (v=carrier) in Hv. now subst v.
    - intros v Hv. change (v=marker) in Hv. now subst v.
    - intros v Hv. change (v=root) in Hv. now subst v.
    - intros v Hv. change (v=theta) in Hv. now subst v.
    - intros v Hv. change (v=theta) in Hv. now subst v. }
  assert (SE:expression_named_substitution M rho rho p q
    (E_kp_eligible (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1))
    (E_kp_eligible (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 2))).
  { unfold E_kp_eligible. apply expression_ns_disjunction;[exact HP0| |].
    - apply (expression_ns_atom M rho rho p q true);assumption.
    - apply (expression_ns_existential M rho rho p q (CEvar 0) (CEvar 0) _ _ y
        HP0 eq_refl eq_refl HYP HYQ).
      apply expression_ns_conjunction;[exact HP0| |].
      + apply (expression_ns_atom M rho rho p q false);assumption.
      + unfold E_ksubset. apply (expression_ns_universal M rho rho p q (CEvar 6) (CEvar 6)
          _ _ container eq_refl eq_refl HKP HKQ).
        apply expression_ns_implication;apply (expression_ns_atom M rho rho p q false);assumption. }
  assert (SR:expression_named_substitution M rho rho p q A B).
  { unfold A,B,E_tagged_local_request. apply expression_ns_implication;[exact SE|].
    apply expression_ns_implication.
    - exact (expression_ns_existential M rho rho p q (CEvar 0) (CEvar 0) _ _ y
        HP0 eq_refl eq_refl HYP HYQ SM).
    - apply (expression_ns_existential M rho rho p q (CEvar 0) (CEvar 0) _ _ y
        HP0 eq_refl eq_refl HYP HYQ).
      apply expression_ns_conjunction;[exact HP0| |exact SM].
      apply (expression_ns_atom M rho rho p q false);assumption. }
  assert (BA:expression_binder_absent M rho q A).
  { unfold A,E_tagged_local_request. apply expression_binder_absent_implication.
    - unfold E_kp_eligible. apply expression_binder_absent_disjunction.
      + apply expression_binder_absent_atom;now right.
      + apply expression_binder_absent_existential.
        * intros v Hv. change (v=y) in Hv. now subst v.
        * apply expression_binder_absent_conjunction.
          -- apply expression_binder_absent_atom;now left.
          -- unfold E_ksubset. apply expression_binder_absent_universal.
             ++ intros v Hv. change (v=container) in Hv. now subst v.
             ++ apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left.
    - change (expression_binder_absent M rho q
        (E_kp_request (CEvar 0) (CEvar 6)
          (E_tagged_matrix (CEvar 0) (CEvar 1) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 7)))).
      apply (request_binder_absent M rho (CEvar 0) (CEvar 6) _ y q eq_refl HYQ).
      apply (tagged_matrix_binder_absent M rho q (CEvar 0) (CEvar 1) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 7) z eq_refl HZQ).
      intros v Hv. change (v=theta) in Hv. now subst v. }
  destruct (code_relation_total M A rho) as [a HA].
  destruct (code_relation_total M B rho) as [b HB].
  exact (proj1 (ns_stopping_instantiation M rho (CEvar 1) (CEvar 2) A B p q a b
    eq_refl eq_refl HA HB HPQ (BA a HA) (SR a b HA HB))).
Qed.

Print Assumptions numerical_tagged_request_specialization.
