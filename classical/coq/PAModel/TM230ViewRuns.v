(** Definable exact paths between binary views, with additive lower bounds. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs PowerTwoSyntax
 TM230RegisterWords TM230BinaryStep TM230BitArithmetic TM230LeftView TM230Paths TM230ExactPaths TM230CarryChainSyntax.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_oriented_view M(reverse:bool)q fixed word s:=
 if reverse then machine230_left_view M q fixed word s else machine230_right_view M q fixed word s.
Definition machine230_view_config M(reverse:bool)q fixed h rest:=
 if reverse then machine230_mk_config(carrier M)(code_numeral M q)rest h fixed
 else machine230_mk_config(carrier M)(code_numeral M q)fixed h rest.
Definition machine230_view_run M reverse q time a x b y:=exists s t,
 machine230_oriented_view M reverse q a x s /\machine230_oriented_view M reverse q b y t /\machine230_reaches_in M time s t.
Lemma machine230_oriented_view_decompose M reverse q a x s:
 machine230_oriented_view M reverse q a x s <->exists h rest,
 s=machine230_view_config M reverse q a h rest /\machine230_is_bit M h /\
 x=addM M(mulM M(code_numeral M 2)rest)h.
Proof.
 destruct reverse;destruct s as[sq sl sh sr];
 unfold machine230_oriented_view,machine230_view_config,machine230_left_view,machine230_right_view;
 cbn[machine230_state machine230_left machine230_head machine230_right];split.
 - intros[Hq[Ha[Hbit Hword]]]. subst sq sr. exists sh,sl;auto.
 - intros[h[rest[E[Hbit Hword]]]]. injection E as E1 E2 E3 E4;subst;auto.
 - intros[Hq[Ha[Hbit Hword]]]. subst sq sl. exists sh,sr;auto.
 - intros[h[rest[E[Hbit Hword]]]]. injection E as E1 E2 E3 E4;subst;auto.
Qed.
Lemma machine230_view_run_alternative M reverse q time a x b y:
 machine230_view_run M reverse q time a x b y <->exists h rest h' rest',
 machine230_is_bit M h /\x=addM M(mulM M(code_numeral M 2)rest)h /\
 machine230_is_bit M h' /\y=addM M(mulM M(code_numeral M 2)rest')h' /\
 machine230_reaches_in M time(machine230_view_config M reverse q a h rest)(machine230_view_config M reverse q b h' rest').
Proof.
 split.
 - intros[s[t[Hs[Ht HP]]]]. apply machine230_oriented_view_decompose in Hs,Ht.
   destruct Hs as[h[rest[Es[Hh Hx]]]],Ht as[h'[rest'[Et[Hh' Hy]]]]. subst s t.
   exists h,rest,h',rest';auto.
 - intros[h[rest[h'[rest'[Hh[Hx[Hh'[Hy HP]]]]]]]].
   exists(machine230_view_config M reverse q a h rest),(machine230_view_config M reverse q b h' rest').
   split;[apply machine230_oriented_view_decompose;exists h,rest;auto|].
   split;[apply machine230_oriented_view_decompose;exists h',rest';auto|exact HP].
Qed.
Definition machine230_view_run_formula(reverse:bool)q(time a x b y:term):form:=∃∃∃∃
 (carry_bit_formula $3 ∧(code_lift4 x==num 2⊗$2⊕$3 ∧
 (carry_bit_formula $1 ∧(code_lift4 y==num 2⊗$0⊕$1 ∧
 (if reverse then machine230_reaches_in_formula(code_lift4 time)(num q)$2 $3(code_lift4 a)(num q)$0 $1(code_lift4 b)
 else machine230_reaches_in_formula(code_lift4 time)(num q)(code_lift4 a)$3 $2(num q)(code_lift4 b)$1 $0))))).
Definition machine230_bounded_view_run M reverse q count a x b y:=exists slack,
 machine230_view_run M reverse q(addM M count slack)a x b y.
Definition machine230_bounded_view_run_formula reverse q(count a x b y:term):form:=∃
 machine230_view_run_formula reverse q(count`[↑]⊕$0)a`[↑] x`[↑] b`[↑] y`[↑].
Local Opaque holds machine230_reaches_in_formula.
Theorem machine230_view_run_formula_correct M rho reverse q time a x b y:
 holds M rho(machine230_view_run_formula reverse q time a x b y)<->
 machine230_view_run M reverse q(evalM M rho time)(evalM M rho a)(evalM M rho x)(evalM M rho b)(evalM M rho y).
Proof.
 rewrite machine230_view_run_alternative. destruct reverse;unfold machine230_view_run_formula,machine230_view_config;
 repeat setoid_rewrite holds_ex;repeat setoid_rewrite holds_and;
 setoid_rewrite carry_bit_formula_correct;setoid_rewrite power_holds_equal;
 setoid_rewrite machine230_reaches_in_formula_correct;
 repeat first[progress(setoid_rewrite register_eval_add)|progress(setoid_rewrite register_eval_mul)|progress(setoid_rewrite code_eval_num)|progress(setoid_rewrite code_eval_lift4)];reflexivity.
Qed.
Theorem machine230_bounded_view_run_formula_correct M rho reverse q count a x b y:
 holds M rho(machine230_bounded_view_run_formula reverse q count a x b y)<->
 machine230_bounded_view_run M reverse q(evalM M rho count)(evalM M rho a)(evalM M rho x)(evalM M rho b)(evalM M rho y).
Proof.
 unfold machine230_bounded_view_run_formula,machine230_bounded_view_run.
 rewrite holds_ex. setoid_rewrite machine230_view_run_formula_correct.
 setoid_rewrite register_eval_add. repeat setoid_rewrite register_eval_up. reflexivity.
Qed.
Lemma machine230_oriented_view_total M reverse q a x:exists s,machine230_oriented_view M reverse q a x s.
Proof. destruct reverse;[apply machine230_left_view_total|apply machine230_right_view_total]. Qed.
Lemma machine230_oriented_view_unique M reverse q a x s t:
 machine230_oriented_view M reverse q a x s->machine230_oriented_view M reverse q a x t->s=t.
Proof. destruct reverse;[apply machine230_left_view_unique|apply machine230_right_view_unique]. Qed.
Lemma machine230_view_run_zero M reverse q a x:machine230_view_run M reverse q(zeroM M)a x a x.
Proof.
 destruct(machine230_oriented_view_total M reverse q a x)as[s Hs]. exists s,s. split;[exact Hs|].
 split;[exact Hs|apply machine230_reaches_in_zero].
Qed.
Lemma machine230_view_run_join M reverse q n k a x b y c z:
 machine230_view_run M reverse q n a x b y ->machine230_view_run M reverse q k b y c z ->
 machine230_view_run M reverse q(addM M n k)a x c z.
Proof.
 intros[s[u[Hs[Hu H1]]]][u'[t[Hu'[Ht H2]]]].
 assert(E:u=u')by(eapply machine230_oriented_view_unique;eassumption). subst u'.
 exists s,t. split;[exact Hs|]. split;[exact Ht|]. eapply machine230_reaches_in_join;eassumption.
Qed.
Lemma machine230_bounded_view_run_zero M reverse q a x:
 machine230_bounded_view_run M reverse q(zeroM M)a x a x.
Proof. exists(zeroM M). rewrite coding_add_zero;apply machine230_view_run_zero. Qed.
Section MotionAlgebra.
Variable M:Model.
Add Ring motion_add_ring:(model_semiring M).
Lemma motion_add_shuffle n k d e:addM M(addM M n k)(addM M d e)=addM M(addM M n d)(addM M k e).
Proof. ring. Qed.
End MotionAlgebra.
Lemma machine230_bounded_view_run_join M reverse q n k a x b y c z:
 machine230_bounded_view_run M reverse q n a x b y ->machine230_bounded_view_run M reverse q k b y c z ->
 machine230_bounded_view_run M reverse q(addM M n k)a x c z.
Proof.
 intros[d H1][e H2]. exists(addM M d e).
 replace(addM M(addM M n k)(addM M d e))with(addM M(addM M n d)(addM M k e)).
 -eapply machine230_view_run_join;eassumption.
 -symmetry;apply motion_add_shuffle.
Qed.
Print Assumptions machine230_view_run_formula_correct.
Print Assumptions machine230_bounded_view_run_join.
