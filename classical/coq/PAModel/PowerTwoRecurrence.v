(** Totality and uniqueness use ordinary PA-definable induction over n. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 CodeExpressions NumericalProofs PowerTwoSyntax.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
Section Recurrence.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation Twice:=(mulM M(N 2)).

Lemma power2_zero:power2 M O(N 1).
Proof.
 destruct(beta_extension M O O O(N 1))as[b[c[Hpre H0]]].
 exists b,c. split;[|exact H0]. split;[exact H0|].
 intros i Hi. exfalso;exact(coding_not_lt_zero M i Hi).
Qed.
Lemma power2_zero_value p:power2 M O p->p=N 1.
Proof. intros[b[c[[H0 Hstep]Hp]]]. exact(beta_unique M b c O p(N 1)Hp H0). Qed.
Lemma power2_zero_iff p:power2 M O p<->p=N 1.
Proof. split;[apply power2_zero_value|intro E;rewrite E;apply power2_zero]. Qed.

Lemma power2_successor n p:power2 M n p->power2 M(S n)(Twice p).
Proof.
 intros[b[c[[H0 Hstep]Hp]]].
 destruct(beta_extension M b c(S n)(Twice p))as[d[e[Hpre Hlast]]].
 assert(Hread:forall i,coding_lt M i(S n)->forall x,beta M d e i x->beta M b c i x).
 { intros i Hi x Hx. destruct(beta_total M b c i)as[y Hy].
   assert(E:x=y)by(eapply beta_unique;[exact Hx|exact(Hpre i y Hi Hy)]).
   now rewrite E. }
 exists d,e. split;[|exact Hlast]. split.
 - exact(Hpre O(N 1)(coding_zero_lt_succ M n)H0).
 - intros i Hi x y Hx Hy. destruct(proj1(coding_lt_succ_cases M i n)Hi)as[Hin|Ei].
   + apply(Hstep i Hin x y).
     * exact(Hread i Hi x Hx).
     * apply(Hread(S i));[now apply coding_lt_succ_cancel|exact Hy].
   + subst i. assert(Ex:x=p)by(eapply beta_unique;[exact Hx|exact(Hpre n p(coding_lt_succ M n)Hp)]).
     assert(Ey:y=Twice p)by(eapply beta_unique;eassumption).
     now rewrite Ex,Ey.
Qed.
Lemma power2_successor_inv n p:power2 M(S n)p->
 exists q,power2 M n q /\p=Twice q.
Proof.
 intros[b[c[[H0 Hstep]Hp]]]. destruct(beta_total M b c n)as[q Hq].
 exists q. split.
 - exists b,c. split;[|exact Hq]. split;[exact H0|].
   intros i Hi x y Hx Hy. apply(Hstep i);[apply coding_lt_succ_cases;now left|exact Hx|exact Hy].
 - exact(Hstep n(coding_lt_succ M n)q p Hq Hp).
Qed.
Theorem power2_total:forall n,exists p,power2 M n p.
Proof.
 apply(definable_induction M(power2_exists M)(power2_exists_definable M)).
 - exists(N 1);apply power2_zero.
 - intros n[p Hp]. exists(Twice p);now apply power2_successor.
Qed.
Theorem power2_functional:forall n p q,power2 M n p->power2 M n q->p=q.
Proof.
 apply(definable_induction M(power2_unique_at M)(power2_unique_definable M)).
 - intros p q Hp Hq. rewrite(power2_zero_value p Hp),(power2_zero_value q Hq). reflexivity.
 - intros n IH p q Hp Hq.
   destruct(power2_successor_inv n p Hp)as[x[Hx Ex]].
   destruct(power2_successor_inv n q Hq)as[y[Hy Ey]].
   rewrite Ex,Ey,(IH x y Hx Hy). reflexivity.
Qed.
Theorem power2_successor_iff n p q:power2 M n p->
 (power2 M(S n)q<->q=Twice p).
Proof.
 intro Hp;split.
 - intro Hq. exact(power2_functional(S n)q(Twice p)Hq(power2_successor n p Hp)).
 - intro E;rewrite E;now apply power2_successor.
Qed.
End Recurrence.
Print Assumptions power2_total.
Print Assumptions power2_functional.
Print Assumptions power2_successor_inv.
