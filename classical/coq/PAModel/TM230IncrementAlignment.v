(** The literal extra-one operation aligns carried suffixes and increments
    exactly the marked register in the reversed ordinary file. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230ReverseBlocks
 TM230CarryPrefixes PowerTwoSyntax PowerTwoRecurrence.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Alignment.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_increment_align_ring:(model_semiring M).
Lemma machine230_increment_four:four=two*two.
Proof.
 change(S(S(S(S Z)))=two*two).
 rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring.
Qed.
Theorem machine230_reverse_block_increment value left word:
 machine230_reverse_block M value left word ->
 machine230_reverse_block M(S value)left(one+two*word).
Proof.
 intros[p[k[Hp[Hpk Hword]]]].
 exists(two*p),(S(two*k)). split.
 -change(power2 M(S value)(mulM M(code_numeral M 2)p)). exact(power2_successor M value p Hp).
 -split.
  +rewrite Hpk,(succ_as_add M k),(succ_as_add M(S(two*k))),(succ_as_add M(two*k)),(succ_as_add M one). ring.
  +change(one+two*word=one+two*(S(two*k)+(two*p)*(two*left))).
   change(word=one+two*(k+p*(two*left)))in Hword.
   rewrite Hword,(succ_as_add M(two*k));ring.
Qed.
Theorem machine230_carry_inserted_one value left out:
 machine230_carry_prefix_step M value left out ->
 machine230_reverse_block M value(one+two*left)(one+two*out).
Proof.
 intros[p[k[Hp[Hpk Hout]]]]. exists p,k. split;[exact Hp|]. split;[exact Hpk|].
 change(out=p*(four*left+two)+k)in Hout.
 change(one+two*out=one+two*(k+p*(two*(one+two*left)))).
 rewrite Hout,machine230_increment_four;ring.
Qed.
End Alignment.
Print Assumptions machine230_reverse_block_increment.
Print Assumptions machine230_carry_inserted_one.
