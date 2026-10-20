(** One complete carry-register block of the literal table. Its value and
    execution length may be nonstandard in the ambient PA model. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230Paths TM230ExactPaths TM230ScanRightExact PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Carry.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_carry_ring:(model_semiring M).
Theorem machine230_carry_one_block v p k left tail s:
 power2 M v p->p=S k->
 machine230_right_view M 0 left(two+four*(k+p*tail))s ->
 exists t,machine230_right_view M 0(p*(four*left+two)+k)tail t /\
 machine230_reaches_in M(S(S v))s t.
Proof.
 intros Hp Hpk Hs.
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 set(rest:=k+p*tail).
 set(left1:=two*left+one). set(left2:=four*left+two).
 destruct(machine230_right_view_total M 94 left1(one+two*rest))as[s1 Hs1].
 destruct(machine230_right_view_total M 0 left2 rest)as[s2 Hs2].
 destruct(machine230_right_view_total M 0(p*left2+k)tail)as[t Ht].
 assert(Hfirst:machine230_step M s s1).
 {apply(machine230_right_view_step M 0 false true 94 left(one+two*rest)).
  -reflexivity.
  -change(machine230_right_view M 0 left(Z+two*(one+two*rest))s).
   replace(Z+two*(one+two*rest))with(two+four*(k+p*tail));[exact Hs|].
   unfold rest;rewrite F,(succ_as_add M one);ring.
  -change(machine230_right_view M 94(two*left+one)(one+two*rest)s1). exact Hs1. }
 assert(Hsecond:machine230_step M s1 s2).
 {apply(machine230_right_view_step M 94 true false 0 left1 rest).
  -reflexivity.
  -exact Hs1.
  -change(machine230_right_view M 0(two*left1+Z)rest s2).
   replace(two*left1+Z)with left2;[exact Hs2|].
   unfold left1,left2;rewrite F,(succ_as_add M one);ring. }
 assert(Hscan:machine230_reaches_in M v s2 t).
 {destruct s2 as[sq sl sh sr],t as[tq tl th tr].
  unfold machine230_right_view in Hs2,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs2,Ht.
  destruct Hs2 as[Hsq[Hsl[Hsh Hsw]]],Ht as[Htq[Htl[Hth Htw]]]. subst sq sl tq tl.
  replace(p*left2+k)with(p*left2+k*machine230_bitM M true)by(change(p*left2+k*one=p*left2+k);rewrite(succ_as_add M Z);ring).
  apply(machine230_scan_right_exact M 0 true true eq_refl v p k left2 sh sr th tr Hp Hpk Hsh Hth).
  change(sh+two*sr=k*one+p*(th+two*tr)).
  unfold rest in Hsw. rewrite Htw in Hsw. replace(sh+two*sr)with(two*sr+sh)by ring.
  rewrite <-Hsw,(succ_as_add M Z). ring. }
 exists t. split;[exact Ht|].
 exact(machine230_reaches_in_step M s s1 t(S v)Hfirst
  (machine230_reaches_in_step M s1 s2 t v Hsecond Hscan)).
Qed.
End Carry.
Print Assumptions machine230_carry_one_block.
