(** The ordinary natural numbers form an actual PA model, and the arithmetic
    code graphs reduce to the exact frozen source code functions there. *)
From PAModel Require Import Model Arithmetic Pairing CodeExpressions.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL.Arithmetics Require Import NatModel.
From K230S Require Import KCode230.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition natModel : Model.
Proof.
  refine {| carrier := nat; raw_interpretation := interp_nat |}.
  intros phi rho H. exact (@nat_is_PAeq_model phi rho H).
Defined.

Lemma numeral_natModel n : code_numeral natModel n = n.
Proof. induction n; [reflexivity|]. change (S (code_numeral natModel n) = S n). now rewrite IHn. Qed.

Lemma twice_triangle n : 2 * tri n = n * S n.
Proof. induction n; cbn [tri]; nia. Qed.

Lemma pair_graph_natModel a b z :
  pair_graph natModel a b z <-> z = KCode230.P a b.
Proof.
  change (2*z = (a+b)*S(a+b)+2*b <-> z = tri(a+b)+b).
  pose proof (twice_triangle (a+b)). nia.
Qed.

Theorem code_relation_natModel env e z :
  code_relation natModel env e z <-> z = code_value env e.
Proof.
  induction e in z |- *; cbn [code_relation code_value].
  - now rewrite numeral_natModel.
  - reflexivity.
  - setoid_rewrite IHe1. setoid_rewrite IHe2.
    change ((exists x y, x = code_value env e1 /\ y = code_value env e2 /\ z = x+y) <->
      z = code_value env e1 + code_value env e2).
    split; [intros (x & y & -> & -> & H); exact H|].
    intro H. exists (code_value env e1),(code_value env e2). auto.
  - setoid_rewrite IHe1. setoid_rewrite IHe2.
    change ((exists x y, x = code_value env e1 /\ y = code_value env e2 /\ z = x*y) <->
      z = code_value env e1 * code_value env e2).
    split; [intros (x & y & -> & -> & H); exact H|].
    intro H. exists (code_value env e1),(code_value env e2). auto.
  - setoid_rewrite IHe1. setoid_rewrite IHe2. setoid_rewrite pair_graph_natModel.
    split; [intros (x & y & -> & -> & H); exact H|].
    intro H. exists (code_value env e1),(code_value env e2). auto.
Qed.

