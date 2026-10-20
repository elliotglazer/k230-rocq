(** Arithmetic linkage between forward register skips and the exact reverse
    block consumed by the return-file routine. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep TM230BitArithmetic
 TM230LeftView TM230ExactPaths TM230UnaryBlocks TM230ReturnBlock
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_reverse_block M value left word:=exists p k,
 power2 M value p /\p=succM M k /\
 word=addM M(succM M(zeroM M))(mulM M(code_numeral M 2)
 (addM M k(mulM M p(mulM M(code_numeral M 2)left)))).
Section Reverse.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_reverse_ring:(model_semiring M).
Theorem machine230_reverse_block_total value left:exists word,machine230_reverse_block M value left word.
Proof.
 destruct(power2_total M value)as[p Hp]. destruct(power2_positive_successor M value p Hp)as[k Hpk].
 exists(one+two*(k+p*(two*left))),p,k. auto.
Qed.
Theorem machine230_reverse_block_functional value left x y:
 machine230_reverse_block M value left x->machine230_reverse_block M value left y->x=y.
Proof.
 intros[p[k[Hp[Hpk Hx]]]][q[j[Hq[Hqj Hy]]]].
 assert(Ep:p=q)by(exact(power2_functional M value p q Hp Hq)).
 assert(Ek:k=j)by(apply(succ_injective M);congruence). congruence.
Qed.
Theorem machine230_skip_output_reverse value p k left:
 power2 M(S value)p->p=S k->
 machine230_reverse_block M value left(p*(two*left)+k).
Proof.
 intros Hp Hpk. destruct(power2_successor_inv M value p Hp)as[q[Hq Ep]].
 change(p=two*q)in Ep. destruct(power2_positive_successor M value q Hq)as[j Hj].
 assert(Ek:k=S(two*j)).
 {apply(succ_injective M). rewrite <-Hpk,Ep,Hj.
  rewrite(succ_as_add M j),(succ_as_add M(S(two*j))),(succ_as_add M(two*j)),(succ_as_add M one). ring. }
 exists q,j. split;[exact Hq|]. split;[exact Hj|].
 change(p*(two*left)+k=one+two*(j+q*(two*left))).
 rewrite Ep,Ek,Hj. rewrite(succ_as_add M j),(succ_as_add M(two*j)),(succ_as_add M one). ring.
Qed.
Theorem machine230_reverse_block_return q qa qb value left right word s:
 Public230.tmn q true=Some(true,TM.L,qa)->
 Public230.tmn qa true=Some(true,TM.L,qa)->
 Public230.tmn qa false=Some(false,TM.L,qb)->
 machine230_reverse_block M value left word ->machine230_left_view M q right word s ->
 exists restored t,machine230_unary_block M value right restored /\
 machine230_left_view M qb restored left t /\machine230_reaches_in M(S(S value))s t.
Proof.
 intros HE HS HX[p[k[Hp[Hpk Hword]]]]Hs. rewrite Hword in Hs.
 exact(machine230_return_one_block M q qa qb value p k left right s HE HS HX Hp Hpk Hs).
Qed.
End Reverse.
Print Assumptions machine230_skip_output_reverse.
Print Assumptions machine230_reverse_block_return.
