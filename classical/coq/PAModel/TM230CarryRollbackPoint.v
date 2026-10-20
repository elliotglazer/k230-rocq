(** Forward and inverse actual block paths share one arithmetic prefix step. *)
From PAModel Require Import Model Arithmetic CodeExpressions PowerTwoSyntax PowerTwoRecurrence
 TM230UnaryBlocks TM230BitArithmetic TM230LeftView TM230ExactPaths TM230CarryPlain
 TM230RollbackBlock TM230CarryPrefixes TM230ViewRuns.
Unset Implicit Arguments.
Section Point.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S O).
Lemma carry_point_time v: addM M one(S v)=S(S v).
Proof. now rewrite Arithmetic.add_succ,Arithmetic.add_zero. Qed.
Theorem machine230_carry_prefix_forward v left out word tail:
 machine230_unary_block M v tail word ->machine230_carry_prefix_step M v left out ->
 machine230_bounded_view_run M false 0 one left word out tail.
Proof.
 intros HW[p[k[Hp[Hk Hout]]]].
 destruct(machine230_right_view_total M 0 left word)as[s Hs].
 destruct(machine230_carry_plain_block M v left tail word s HW Hs)as[q[j[t[Hq[Hj[Ht HP]]]]]].
 assert(Eq:q=p)by(eapply power2_functional;eassumption). subst q.
 assert(Ej:j=k)by(apply(succ_injective M);congruence). subst j.
 rewrite Eq in Ht. rewrite <-Hout in Ht. exists(S v). rewrite carry_point_time.
 exists s,t;auto.
Qed.
Theorem machine230_carry_prefix_backward v left out word tail:
 machine230_unary_block M v tail word ->machine230_carry_prefix_step M v left out ->
 machine230_bounded_view_run M true 97 one tail out word left.
Proof.
 intros HW[p[k[Hp[Hk Hout]]]].
 destruct(machine230_left_view_total M 97 tail out)as[s Hs].
 rewrite Hout in Hs.
 destruct(machine230_rollback_one_block M v p k left tail s Hp Hk Hs)as[w[t[Hw[Ht HP]]]].
 assert(Ew:w=word)by(eapply machine230_unary_block_functional;eassumption). subst w.
 rewrite <-Hout in Hs. exists(S v). rewrite carry_point_time. exists s,t. split;[exact Hs|].
 split;[exact Ht|exact HP].
Qed.
End Point.
Print Assumptions machine230_carry_prefix_forward.
Print Assumptions machine230_carry_prefix_backward.
