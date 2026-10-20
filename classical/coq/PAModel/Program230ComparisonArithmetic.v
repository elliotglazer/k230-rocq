(** Arithmetic invariant for the program's destructive equality test.
    The residual is represented by addition, without a subtraction symbol. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition program230_difference M x y residual :=
 y=addM M x residual \/ x=addM M y residual.
Definition program230_difference_formula (x y residual:term):form :=
 (y==(x⊕residual)) ∨ (x==(y⊕residual)).

Lemma program230_difference_formula_correct M rho x y residual:
 holds M rho (program230_difference_formula x y residual) <->
 program230_difference M (evalM M rho x) (evalM M rho y) (evalM M rho residual).
Proof.
 unfold program230_difference_formula,program230_difference.
 rewrite holds_or;reflexivity.
Qed.

Lemma program230_difference_left_zero M y:
 program230_difference M (zeroM M) y y.
Proof. left;symmetry;apply coding_add_zero. Qed.

Lemma program230_difference_right_zero M x:
 program230_difference M x (zeroM M) x.
Proof. right;symmetry;apply coding_add_zero. Qed.

Lemma program230_difference_successors M x y residual:
 program230_difference M (succM M x) (succM M y) residual <->
 program230_difference M x y residual.
Proof.
 unfold program230_difference;rewrite !Arithmetic.add_succ.
 split;intros [H|H].
 -left;exact (succ_injective M y (addM M x residual) H).
 -right;exact (succ_injective M x (addM M y residual) H).
 -left;now rewrite H.
 -right;now rewrite H.
Qed.

Theorem program230_difference_zero_iff M x y residual:
 program230_difference M x y residual -> (residual=zeroM M <-> x=y).
Proof.
 intro Hdiff;split.
 -intro Hr;subst residual;destruct Hdiff as [H|H];rewrite coding_add_zero_r in H;congruence.
 -intro Hxy;subst y;destruct Hdiff as [H|H];
  apply (Arithmetic.add_cancel M residual (zeroM M) x);
  rewrite (coding_add_comm M residual x),(coding_add_comm M (zeroM M) x),coding_add_zero_r;
  symmetry;exact H.
Qed.

Lemma program230_difference_nonzero M x y residual:
 program230_difference M x y residual -> x<>y -> residual<>zeroM M.
Proof.
 intros Hdiff Hxy Hr;apply Hxy;exact (proj1 (program230_difference_zero_iff M x y residual Hdiff) Hr).
Qed.

Print Assumptions program230_difference_formula_correct.
Print Assumptions program230_difference_successors.
Print Assumptions program230_difference_zero_iff.
