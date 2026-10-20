(** The raw tagged matrix uses the actual predicate X in A and Theta. *)
From PAModel Require Import Model CodeExpressions FreshNames TemplateFormulaFresh
  TemplateBinderFresh ExpressionFreshElimination FreshMembershipNames.
Unset Implicit Arguments.

Definition E_separation_predicate X A Theta := E_wa (E_wel X A) Theta.

Lemma separation_predicate_binder_absent M rho name X A Theta :
  expression_binder_absent M rho name Theta ->
  expression_binder_absent M rho name (E_separation_predicate X A Theta).
Proof.
  intro H. apply expression_binder_absent_conjunction;[|exact H].
  apply expression_binder_absent_atom;now left.
Qed.

Lemma separation_predicate_fresh M rho name X A Theta :
  name<>zeroM M -> expression_name_avoids M rho name X ->
  expression_name_avoids M rho name A -> expression_fresh M rho name Theta ->
  expression_fresh M rho name (E_separation_predicate X A Theta).
Proof.
  intros H0 HX HA HTheta. apply expression_fresh_conjunction;[exact H0| |exact HTheta].
  apply expression_fresh_atom;[now left|exact HX|exact HA].
Qed.

Lemma separation_predicate_fresh_parts M rho name X A Theta :
  expression_fresh M rho name (E_separation_predicate X A Theta) ->
  expression_name_avoids M rho name X /\ expression_name_avoids M rho name A /\
  expression_fresh M rho name Theta.
Proof.
  intro H. destruct (expression_fresh_conjunction_parts M rho name (E_wel X A) Theta H) as [HM HT].
  destruct (expression_fresh_membership_names M rho name X A HM) as [HX HA]. auto.
Qed.

Print Assumptions separation_predicate_binder_absent.
Print Assumptions separation_predicate_fresh_parts.
