(** Real q40 return over a finite physical prefix, including the incremented
    marked register. Register values remain arbitrary arithmetic elements. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions
 TM230BinaryStep TM230BitArithmetic TM230LeftView TM230Paths TM230ExactPaths
 TM230UnaryBlocks TM230ReverseBlocks TM230RegisterPrefix TM230IncrementAlignment.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem machine230_return_plain_prefix M values left tail word reverse right s:
 machine230_prefix_frame M values left tail word reverse ->
 machine230_left_view M 40 right reverse s ->
 exists restored t,machine230_blocks_list M values right restored /\
 machine230_left_view M 40 restored left t /\machine230_reaches M s t.
Proof.
 revert left word reverse right s. induction values as[|v vs IH];intros left word reverse right s Hframe Hs.
 -destruct Hframe as[Hw Hr]. subst reverse. exists right,s.
  split;[reflexivity|]. split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hb[Hrev Hframe]]]].
  destruct(IH nextleft middle reverse right s Hframe Hs)as[inside[mid[Hinside[Hmid Hpath]]]].
  destruct(machine230_reverse_block_return M 40 54 40 v left inside nextleft mid
   eq_refl eq_refl eq_refl Hrev Hmid)as[restored[t[Hrestored[Ht Htail]]]].
  exists restored,t. split;[exists inside;auto|]. split;[exact Ht|].
  eapply machine230_reaches_trans;[exact Hpath|].
  eapply machine230_reaches_in_forget;exact Htail.
Qed.
Theorem machine230_increment_return_prefix M prefix value left oldtail oldword reverse normal right s:
 machine230_prefix_frame M prefix left oldtail oldword reverse ->
 machine230_reverse_block M value reverse normal ->
 machine230_left_view M 40 right
  (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)normal))s ->
 exists target restored t,machine230_unary_block M(succM M value)right target /\
 machine230_blocks_list M prefix target restored /\
 machine230_left_view M 40 restored left t /\machine230_reaches M s t.
Proof.
 intros Hframe Hnormal Hs.
 pose proof(machine230_reverse_block_increment M value reverse normal Hnormal)as Hinc.
 destruct(machine230_reverse_block_return M 40 54 40(succM M value)reverse right
  (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)normal))s
  eq_refl eq_refl eq_refl Hinc Hs)as[target[mid[Htarget[Hmid Hpath]]]].
 destruct(machine230_return_plain_prefix M prefix left oldtail oldword reverse target mid Hframe Hmid)
  as[restored[t[Hrestored[Ht Htail]]]].
 exists target,restored,t. split;[exact Htarget|]. split;[exact Hrestored|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[|exact Htail]. eapply machine230_reaches_in_forget;exact Hpath.
Qed.
Print Assumptions machine230_return_plain_prefix.
Print Assumptions machine230_increment_return_prefix.
