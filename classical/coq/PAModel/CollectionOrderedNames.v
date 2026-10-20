(** Finite name bookkeeping for the outer Collection construction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT TemplateNamedSubstitution.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_ordered_names_nodup M t a c x v w j z q b r :
  NoDup [t;a;c;x;v] ->
  coding_lt M t w -> coding_lt M a w -> coding_lt M c w ->
  coding_lt M x w -> coding_lt M v w ->
  coding_lt M w j -> coding_lt M j z -> coding_lt M z q ->
  coding_lt M q b -> coding_lt M b r ->
  NoDup [t;a;b;r;j;x;w;v;z;q;c].
Proof.
  intros ND HT HA HC HX HV HWJ HJZ HZQ HQB HBR.
  repeat match goal with
  | H1: coding_lt M ?u ?v, H2: coding_lt M ?v ?w |- _ =>
      let T := constr:(coding_lt M u w) in
      tryif (match goal with _:T |- _ => idtac end)
      then fail
      else let H := fresh "HL" in pose proof (coding_lt_trans M u v w H1 H2) as H
  end.
  repeat match goal with
  | H: coding_lt M ?u ?v |- _ =>
      let T := constr:(v<>u) in
      tryif (match goal with _:T |- _ => idtac end)
      then fail
      else let N := fresh "HN" in pose proof (template_lt_different M u v H) as N
  end.
  repeat match goal with H:NoDup (_::_) |- _ => inversion H;clear H end.
  repeat match goal with H:~In _ (_::_) |- _ => apply not_in_cons in H;destruct H end.
  repeat (constructor;[cbn;intuition congruence|]). constructor.
Qed.

Print Assumptions collection_ordered_names_nodup.
