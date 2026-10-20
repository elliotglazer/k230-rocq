(** Algebra in an arbitrary model of ordinary PA.  The ring tactic below
    checks polynomial identities against these PA-derived equations. *)
From PAModel Require Import Model.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Arithmetic.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Notation one := (S O).
Local Notation add := (addM M).
Local Notation mul := (mulM M).
Local Definition PA := fun ax H rho => axioms M ax rho H.

Lemma add_zero x : add O x = x.
Proof. exact (@Peano.add_zero D (raw_interpretation M) PA x). Qed.
Lemma add_comm x y : add x y = add y x.
Proof. exact (@Peano.add_comm D (raw_interpretation M) PA x y). Qed.
Lemma add_assoc x y z : add x (add y z) = add (add x y) z.
Proof. symmetry. exact (@Peano.add_asso D (raw_interpretation M) PA x y z). Qed.
Lemma add_succ x y : add (S x) y = S (add x y).
Proof. exact (@Peano.add_rec D (raw_interpretation M) PA x y). Qed.
Lemma mul_zero x : mul O x = O.
Proof. exact (@Peano.mult_zero D (raw_interpretation M) PA x). Qed.
Lemma mul_comm x y : mul x y = mul y x.
Proof. exact (@Peano.mult_comm D (raw_interpretation M) PA x y). Qed.
Lemma mul_assoc x y z : mul x (mul y z) = mul (mul x y) z.
Proof. symmetry. exact (@Peano.mult_asso D (raw_interpretation M) PA x y z). Qed.
Lemma mul_succ x y : mul (S x) y = add y (mul x y).
Proof. exact (@Peano.mult_rec D (raw_interpretation M) PA y x). Qed.
Lemma mul_one x : mul one x = x.
Proof. rewrite mul_succ, mul_zero, add_comm. apply add_zero. Qed.
Lemma mul_add x y z : mul (add x y) z = add (mul x z) (mul y z).
Proof. exact (@Peano.distributive D (raw_interpretation M) PA x y z). Qed.

Lemma model_semiring : semi_ring_theory O one add mul (@eq D).
Proof.
  constructor; [exact add_zero|exact add_comm|exact add_assoc|
    exact mul_one|exact mul_zero|exact mul_comm|exact mul_assoc|exact mul_add].
Qed.

Add Ring model_ring : model_semiring.

Lemma succ_as_add x : S x = add x one.
Proof. rewrite add_comm, add_succ, add_zero. reflexivity. Qed.

Lemma add_cancel x y z : add x z = add y z -> x = y.
Proof. exact (@Peano.add_eq D (raw_interpretation M) PA x y z). Qed.

Lemma two_mul x : mul (S one) x = add x x.
Proof. rewrite mul_succ, mul_one. reflexivity. Qed.

Lemma consecutive_product_step x :
  mul (S x) (S (S x)) = add (mul x (S x)) (mul (S one) (S x)).
Proof. rewrite (succ_as_add (S x)), (succ_as_add x), (succ_as_add one). ring. Qed.

End Arithmetic.

(** Register the model parameter explicitly at every use site. *)
Arguments add_zero M x : clear implicits.
Arguments add_comm M x y : clear implicits.
Arguments add_assoc M x y z : clear implicits.
Arguments add_succ M x y : clear implicits.
Arguments mul_zero M x : clear implicits.
Arguments mul_comm M x y : clear implicits.
Arguments mul_assoc M x y z : clear implicits.
Arguments mul_succ M x y : clear implicits.
Arguments mul_one M x : clear implicits.
Arguments mul_add M x y z : clear implicits.
Arguments model_semiring M : clear implicits.
Arguments succ_as_add M x : clear implicits.
Arguments add_cancel M x y z : clear implicits.
Arguments two_mul M x : clear implicits.
Arguments consecutive_product_step M x : clear implicits.
