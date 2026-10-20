(** Shared literal control path for passing a plain block or entering the
    marked increment target. The second prefix bit selects the branch. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230ExactPaths TM230ScanRightExact TM230UnaryBlocks PowerTwoSyntax.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_file_scan_state(b:bool):=if b then 64 else 0.
Section Entry.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_file_entry_ring:(model_semiring M).
Theorem machine230_file_entry_block b value p k left tail s:
 power2 M value p->p=S k->
 machine230_right_view M 64 left(two*machine230_bitM M b+four*(k+p*tail))s ->
 exists t,machine230_right_view M(machine230_file_scan_state b)(p*(four*left+one)+k)tail t /\
 machine230_reaches_in M(S(S value))s t.
Proof.
 intros Hp Hpk Hs.
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 set(rest:=k+p*tail). set(left1:=two*left). set(left2:=four*left+one).
 destruct(machine230_right_view_total M 74 left1(machine230_bitM M b+two*rest))as[s1 Hs1].
 destruct(machine230_right_view_total M(machine230_file_scan_state b)left2 rest)as[s2 Hs2].
 destruct(machine230_right_view_total M(machine230_file_scan_state b)(p*left2+k)tail)as[t Ht].
 assert(H1:machine230_step M s s1).
 {apply(machine230_right_view_step M 64 false false 74 left(machine230_bitM M b+two*rest)).
  -reflexivity.
  -change(machine230_right_view M 64 left(Z+two*(machine230_bitM M b+two*rest))s).
   replace(Z+two*(machine230_bitM M b+two*rest))with(two*machine230_bitM M b+four*(k+p*tail));[exact Hs|].
   unfold rest;rewrite F;ring.
  -change(machine230_right_view M 74(two*left+Z)(machine230_bitM M b+two*rest)s1).
   replace(two*left+Z)with left1;[exact Hs1|unfold left1;ring]. }
 assert(H2:machine230_step M s1 s2).
 {apply(machine230_right_view_step M 74 b true(machine230_file_scan_state b)left1 rest).
  -destruct b;reflexivity.
  -exact Hs1.
  -change(machine230_right_view M(machine230_file_scan_state b)(two*left1+one)rest s2).
   replace(two*left1+one)with left2;[exact Hs2|]. unfold left1,left2;rewrite F;ring. }
 assert(Hscan:machine230_reaches_in M value s2 t).
 {destruct s2 as[sq sl sh sr],t as[tq tl th tr].
  unfold machine230_right_view in Hs2,Ht;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs2,Ht.
  destruct Hs2 as[Hsq[Hsl[Hsh Hsw]]],Ht as[Htq[Htl[Hth Htw]]]. subst sq sl tq tl.
  replace(p*left2+k)with(p*left2+k*machine230_bitM M true)by(change(p*left2+k*one=p*left2+k);rewrite(succ_as_add M Z);ring).
  apply(machine230_scan_right_exact M(machine230_file_scan_state b)true true
   ltac:(destruct b;reflexivity)value p k left2 sh sr th tr Hp Hpk Hsh Hth).
  change(sh+two*sr=k*one+p*(th+two*tr)).
  unfold rest in Hsw. rewrite Htw in Hsw. replace(sh+two*sr)with(two*sr+sh)by ring.
  rewrite <-Hsw,(succ_as_add M Z). ring. }
 exists t. split;[exact Ht|]. exact(machine230_reaches_in_step M s s1 t(S value)H1
  (machine230_reaches_in_step M s1 s2 t value H2 Hscan)).
Qed.
End Entry.
Print Assumptions machine230_file_entry_block.
