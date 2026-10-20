(** Internal exponent addition and strict growth for the beta recurrence. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalProofs PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition power2_product_at M n p m:=forall q,power2 M m q->
 power2 M(addM M n m)(mulM M p q).
Lemma power2_product_definable M n p:Definable1 M(power2_product_at M n p).
Proof.
 exists(∀(power2_formula $1 $0→power2_formula($2 ⊕ $1)($3 ⊗ $0))),
 (n .:p .:(fun _=>zeroM M)).
 intro m. unfold power2_product_at. rewrite holds_all.
 setoid_rewrite holds_imp. setoid_rewrite power2_formula_correct. reflexivity.
Qed.
Section Laws.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring power_laws_ring:(model_semiring M).
Lemma power_add_succ n k:n+S k=S(n+k).
Proof. rewrite(Arithmetic.add_comm M n(S k)),Arithmetic.add_succ,(Arithmetic.add_comm M k n);reflexivity. Qed.
Theorem power2_add n p:power2 M n p->forall m q,power2 M m q->power2 M(n+m)(p*q).
Proof.
 intro Hnp. apply(definable_induction M(power2_product_at M n p)(power2_product_definable M n p)).
 - intros q Hq. rewrite(power2_zero_value M q Hq),coding_add_zero_r.
   replace(p*N 1)with p by(change(p=p*S O);ring). exact Hnp.
 - intros m IH q Hq. destruct(power2_successor_inv M m q Hq)as[r[Hr Eq]].
   rewrite Eq,power_add_succ. replace(p*(N 2*r))with(N 2*(p*r))by ring.
   apply power2_successor. exact(IH r Hr).
Qed.
Lemma power2_strict_product p r: (exists a,p=S a)->(exists b,r=S b)->
 coding_lt M p(p*(N 2*r)).
Proof.
 intros[a Ha][b Hb]. exists(a+p*(b+b)).
 rewrite(succ_as_add M(p+(a+p*(b+b)))).
 rewrite Ha,Hb. change(S a*(S(S O)*S b)=S a+(a+S a*(b+b))+S O).
 rewrite(succ_as_add M a),(succ_as_add M b),(succ_as_add M(S O)). ring.
Qed.
Theorem power2_strict_mono n m p q:power2 M n p->power2 M m q->
 coding_lt M n m->coding_lt M p q.
Proof.
 intros Hnp Hmq[k Em]. destruct(power2_total M k)as[r Hr].
 pose proof(power2_successor M k r Hr)as Hsr.
 pose proof(power2_add n p Hnp(S k)(N 2*r)Hsr)as Hprod.
 rewrite power_add_succ,<-Em in Hprod.
 assert(Eq:q=p*(N 2*r))by(eapply power2_functional;eassumption).
 rewrite Eq. apply power2_strict_product.
 - exact(power2_positive_successor M n p Hnp).
 - exact(power2_positive_successor M k r Hr).
Qed.
End Laws.
Print Assumptions power2_add.
Print Assumptions power2_strict_mono.
