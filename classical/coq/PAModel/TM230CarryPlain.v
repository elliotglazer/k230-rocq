(** The checked carry block applied to the exact plain register encoding. *)
From PAModel Require Import Model Arithmetic CodeExpressions PowerTwoSyntax
 TM230UnaryBlocks TM230BitArithmetic TM230ExactPaths TM230CarryBlock.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Plain.
Variable M:Model.
Local Notation O:=(zeroM M).
Local Notation S:=(succM M).
Local Notation two:=(code_numeral M 2).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring carry_plain_ring:(model_semiring M).
Lemma machine230_plain_carry_shape v tail word:
 machine230_unary_block M v tail word->
 exists p k,power2 M v p /\p=S k /\word=two+four*(k+p*tail).
Proof.
 intro H. destruct(machine230_unary_block_has_mark M v tail word H)as[m[[p[k[Hp[Hk Hm]]]]E]].
 exists p,k. split;[exact Hp|]. split;[exact Hk|]. rewrite E,Hm. ring.
Qed.
Theorem machine230_carry_plain_block v left tail word s:
 machine230_unary_block M v tail word->machine230_right_view M 0 left word s->
 exists p k t,power2 M v p /\p=S k /\
 machine230_right_view M 0(p*(four*left+two)+k)tail t /\
 machine230_reaches_in M(S(S v))s t.
Proof.
 intros Hblock Hs. destruct(machine230_plain_carry_shape v tail word Hblock)as[p[k[Hp[Hk E]]]].
 rewrite E in Hs. destruct(machine230_carry_one_block M v p k left tail s Hp Hk Hs)as[t[Ht Hpath]].
 exists p,k,t. auto.
Qed.
End Plain.
Print Assumptions machine230_carry_plain_block.
