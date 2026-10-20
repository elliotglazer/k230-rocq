(** The three literal transitions that erase a target register's marker bit. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230SymbolicCells TM230ExactPaths TM230UnaryBlocks PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Mark.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_mark_ring:(model_semiring M).
Theorem machine230_mark_target_block value left tail word s:
 machine230_unary_block M value tail word ->machine230_right_view M 51 left word s ->
 exists marked t,machine230_marked_block M value tail marked /\
 machine230_left_view M 1 marked left t /\machine230_reaches_in M(code_numeral M 3)s t.
Proof.
 intros Hb Hs. destruct(machine230_marked_block_total M value tail)as[marked Hmarked].
 pose proof(machine230_plain_marked_difference M value tail word marked Hb Hmarked)as Hdiff. change(word=marked+two)in Hdiff.
 destruct Hmarked as[p[k[Hp[Hpk Hmarked]]]].
 change(marked=four*k+(four*p)*tail)in Hmarked.
 set(rest:=k+p*tail).
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 assert(Hmarked':marked=four*rest)by(unfold rest;rewrite Hmarked;ring).
 destruct(machine230_right_view_total M 16(two*left)(one+two*rest))as[s1 Hs1].
 destruct(machine230_left_view_total M 1(two*rest)(two*left))as[s2 Hs2].
 destruct(machine230_left_view_total M 1 marked left)as[t Ht].
 assert(H1:machine230_step M s s1).
 {apply(machine230_right_view_step M 51 false false 16 left(one+two*rest)).
  -reflexivity.
  -change(machine230_right_view M 51 left(Z+two*(one+two*rest))s).
   replace(Z+two*(one+two*rest))with word;[exact Hs|].
   rewrite Hdiff,Hmarked',F,(succ_as_add M one). ring.
  -change(machine230_right_view M 16(two*left+Z)(one+two*rest)s1).
   replace(two*left+Z)with(two*left)by ring. exact Hs1. }
 assert(H2:machine230_step M s1 s2).
 {apply(machine230_right_to_left_step M 16 true false 1(two*left)rest s1 s2).
  -reflexivity.
  -exact Hs1.
  -change(machine230_left_view M 1(Z+two*rest)(two*left)s2).
   replace(Z+two*rest)with(two*rest)by ring. exact Hs2. }
 assert(H3:machine230_step M s2 t).
 {apply(machine230_left_view_step M 1 false false 1(two*rest)left s2 t).
  -reflexivity.
  -change(machine230_left_view M 1(two*rest)(Z+two*left)s2).
   replace(Z+two*left)with(two*left)by ring. exact Hs2.
  -change(machine230_left_view M 1(two*(two*rest)+Z)left t).
   replace(two*(two*rest)+Z)with marked;[exact Ht|]. rewrite Hmarked',F. ring. }
 exists marked,t. split.
 -exists p,k. split;[exact Hp|]. split;[exact Hpk|exact Hmarked].
 -split;[exact Ht|].
  change(machine230_reaches_in M(S(S one))s t).
  exact(machine230_reaches_in_step M s s1 t(S one)H1
   (machine230_reaches_in_step M s1 s2 t one H2(machine230_reaches_in_one M s2 t H3))).
Qed.
End Mark.
Print Assumptions machine230_mark_target_block.
