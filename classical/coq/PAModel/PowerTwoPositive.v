(** Strict positivity at every internal exponent. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalProofs PowerTwoSyntax PowerTwoRecurrence.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition power2_positive_at M n:=forall p,power2 M n p->coding_lt M(zeroM M)p.
Lemma power2_positive_definable M:Definable1 M(power2_positive_at M).
Proof.
 exists(∀(power2_formula $1 $0→Peano.sless zero $0)),(fun _=>zeroM M).
 intro n. unfold power2_positive_at. rewrite holds_all.
 setoid_rewrite holds_imp. setoid_rewrite power2_formula_correct.
 setoid_rewrite less_formula_correct. reflexivity.
Qed.
Theorem power2_positive M:forall n p,power2 M n p->coding_lt M(zeroM M)p.
Proof.
 apply(definable_induction M(power2_positive_at M)(power2_positive_definable M)).
 - intros p Hp. rewrite(power2_zero_value M p Hp). apply coding_zero_lt_succ.
 - intros n IH p Hp. destruct(power2_successor_inv M n p Hp)as[q[Hq Eq]].
   rewrite Eq. apply positive_product;[apply coding_zero_lt_succ|exact(IH q Hq)].
Qed.
Theorem power2_positive_successor M n p:power2 M n p->exists k,p=succM M k.
Proof.
 intro H. destruct(power2_positive M n p H)as[k Hk]. exists k.
 now rewrite coding_add_zero in Hk.
Qed.
Print Assumptions power2_positive.
Print Assumptions power2_positive_successor.
