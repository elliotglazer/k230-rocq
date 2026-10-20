(** Finite bounds on the labels allocated by a host-finite template.
    All actual label values still range over an arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions QuotientAtomTemplates TemplateNamedExclusions.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Fixpoint template_binder_span {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 0
  | atom _ _ => 0
  | bin _ a b => template_binder_span a + template_binder_span b
  | quant _ a => S (template_binder_span a)
  end.

Lemma template_numeral_add M a b :
  code_numeral M (a+b) = addM M (code_numeral M a) (code_numeral M b).
Proof.
  induction a; cbn [Nat.add code_numeral].
  - symmetry. apply Arithmetic.add_zero.
  - rewrite IHa,Arithmetic.add_succ. reflexivity.
Qed.

Lemma template_offset_shift M k i :
  addM M (succM M k) (code_numeral M i) = addM M k (code_numeral M (S i)).
Proof.
  cbn [code_numeral]. rewrite (Arithmetic.add_comm M k (succM M (code_numeral M i))).
  rewrite !Arithmetic.add_succ. now rewrite (Arithmetic.add_comm M k (code_numeral M i)).
Qed.

Theorem template_allocations_avoid_offsets M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall k y,
    (forall i, i<template_binder_span phi -> addM M k (code_numeral M i)<>y) ->
    template_allocations_avoid M phi k y.
Proof.
  induction phi; intros k y H; cbn [template_allocations_avoid]; try exact I.
  - split.
    + apply IHphi1. intros i Hi. apply H. cbn [template_binder_span]. lia.
    + apply IHphi2. intros i Hi. apply H. cbn [template_binder_span]. lia.
  - split.
    + specialize (H 0 ltac:(cbn [template_binder_span];lia)).
      now rewrite (coding_add_zero_r M) in H.
    + apply IHphi. intros i Hi. rewrite template_offset_shift.
      apply H. cbn [template_binder_span]. lia.
Qed.

Definition template_new_name M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) k f x :=
  succM M (addM M (addM M f x) (addM M k (code_numeral M (template_binder_span phi)))).

Section Bounds.
Variable M : Model.
Add Ring template_range_ring : (model_semiring M).

Theorem template_new_name_above {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) k f x :
  coding_lt M f (template_new_name M phi k f x) /\
  coding_lt M x (template_new_name M phi k f x).
Proof.
  unfold template_new_name. split.
  - exists (addM M x (addM M k (code_numeral M (template_binder_span phi)))).
    f_equal. ring.
  - exists (addM M f (addM M k (code_numeral M (template_binder_span phi)))).
    f_equal. ring.
Qed.

Theorem template_new_name_avoids {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) k f x :
  template_allocations_avoid M phi k (template_new_name M phi k f x).
Proof.
  apply template_allocations_avoid_offsets. intros i Hi.
  assert (E : template_binder_span phi = i + (template_binder_span phi - i)) by lia.
  assert (Hlt : coding_lt M (addM M k (code_numeral M i)) (template_new_name M phi k f x)).
  { unfold template_new_name. rewrite E,template_numeral_add.
    exists (addM M (addM M f x) (code_numeral M (template_binder_span phi-i))).
    f_equal. ring. }
  exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) _ _ Hlt).
Qed.

End Bounds.

Print Assumptions template_allocations_avoid_offsets.
Print Assumptions template_new_name_above.
Print Assumptions template_new_name_avoids.
