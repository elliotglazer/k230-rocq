(** Uniform spare-tail totality and functionality by ordinary PA induction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 CodeExpressions NumericalProofs TM230SpareSyntax.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
Section Recurrence.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Notation Next:=(fun x=>addM M(N 6)(mulM M(N 8)x)).

Lemma machine230_spare_zero:machine230_spare M O(O).
Proof.
 destruct(beta_extension M O O O(O))as[b[c[Hpre H0]]].
 exists b,c. split;[|exact H0]. split;[exact H0|].
 intros i Hi. exfalso;exact(coding_not_lt_zero M i Hi).
Qed.
Lemma machine230_spare_zero_value p:machine230_spare M O p->p=O.
Proof. intros[b[c[[H0 Hstep]Hp]]]. exact(beta_unique M b c O p(O)Hp H0). Qed.
Lemma machine230_spare_zero_iff p:machine230_spare M O p<->p=O.
Proof. split;[apply machine230_spare_zero_value|intro E;rewrite E;apply machine230_spare_zero]. Qed.

Lemma machine230_spare_successor n p:machine230_spare M n p->machine230_spare M(S n)(Next p).
Proof.
 intros[b[c[[H0 Hstep]Hp]]].
 destruct(beta_extension M b c(S n)(Next p))as[d[e[Hpre Hlast]]].
 assert(Hread:forall i,coding_lt M i(S n)->forall x,beta M d e i x->beta M b c i x).
 { intros i Hi x Hx. destruct(beta_total M b c i)as[y Hy].
   assert(E:x=y)by(eapply beta_unique;[exact Hx|exact(Hpre i y Hi Hy)]).
   now rewrite E. }
 exists d,e. split;[|exact Hlast]. split.
 - exact(Hpre O(O)(coding_zero_lt_succ M n)H0).
 - intros i Hi x y Hx Hy. destruct(proj1(coding_lt_succ_cases M i n)Hi)as[Hin|Ei].
   + apply(Hstep i Hin x y).
     * exact(Hread i Hi x Hx).
     * apply(Hread(S i));[now apply coding_lt_succ_cancel|exact Hy].
   + subst i. assert(Ex:x=p)by(eapply beta_unique;[exact Hx|exact(Hpre n p(coding_lt_succ M n)Hp)]).
     assert(Ey:y=Next p)by(eapply beta_unique;eassumption).
     now rewrite Ex,Ey.
Qed.
Lemma machine230_spare_successor_inv n p:machine230_spare M(S n)p->
 exists q,machine230_spare M n q /\p=Next q.
Proof.
 intros[b[c[[H0 Hstep]Hp]]]. destruct(beta_total M b c n)as[q Hq].
 exists q. split.
 - exists b,c. split;[|exact Hq]. split;[exact H0|].
   intros i Hi x y Hx Hy. apply(Hstep i);[apply coding_lt_succ_cases;now left|exact Hx|exact Hy].
 - exact(Hstep n(coding_lt_succ M n)q p Hq Hp).
Qed.
Theorem machine230_spare_total:forall n,exists p,machine230_spare M n p.
Proof.
 apply(definable_induction M(machine230_spare_exists M)(machine230_spare_exists_definable M)).
 - exists(O);apply machine230_spare_zero.
 - intros n[p Hp]. exists(Next p);now apply machine230_spare_successor.
Qed.
Theorem machine230_spare_functional:forall n p q,machine230_spare M n p->machine230_spare M n q->p=q.
Proof.
 apply(definable_induction M(machine230_spare_unique_at M)(machine230_spare_unique_definable M)).
 - intros p q Hp Hq. rewrite(machine230_spare_zero_value p Hp),(machine230_spare_zero_value q Hq). reflexivity.
 - intros n IH p q Hp Hq.
   destruct(machine230_spare_successor_inv n p Hp)as[x[Hx Ex]].
   destruct(machine230_spare_successor_inv n q Hq)as[y[Hy Ey]].
   rewrite Ex,Ey,(IH x y Hx Hy). reflexivity.
Qed.
Theorem machine230_spare_successor_iff n p q:machine230_spare M n p->
 (machine230_spare M(S n)q<->q=Next p).
Proof.
 intro Hp;split.
 - intro Hq. exact(machine230_spare_functional(S n)q(Next p)Hq(machine230_spare_successor n p Hp)).
 - intro E;rewrite E;now apply machine230_spare_successor.
Qed.
End Recurrence.
Print Assumptions machine230_spare_total.
Print Assumptions machine230_spare_functional.
Print Assumptions machine230_spare_successor_inv.
