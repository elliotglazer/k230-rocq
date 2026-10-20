(** Seven literal transitions restoring a zero target and the next block header. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions
 TM230BinaryStep TM230BitArithmetic TM230LeftView TM230SymbolicCells TM230ExactPaths.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section ZeroControl.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Notation four:=(N 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring decrement_zero_ring:(model_semiring M).

Theorem machine230_decrement_zero_control rest left s:
 machine230_right_view M 0 left (four*(two+four*rest)) s ->
 exists t,machine230_left_view M 97 (two+four*(two+four*rest)) left t /\
  machine230_reaches_in M (N 7) s t.
Proof.
 intro Hs.
 assert(F:four=two*two).
 { change(S(S(S(S Z)))=two*two).
   rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),
     (succ_as_add M one);ring. }
 set(tail:=two+four*rest).
 set(a:=two*left+one). set(b:=two*a). set(c:=two*b+one).
 destruct(machine230_right_view_total M 94 a(two*tail))as[s1 Hs1].
 destruct(machine230_right_view_total M 66 b tail)as[s2 Hs2].
 destruct(machine230_right_view_total M 198 c(one+two*rest))as[s3 Hs3].
 destruct(machine230_left_view_total M 113(one+two*rest)c)as[s4 Hs4].
 destruct(machine230_left_view_total M 97 tail b)as[s5 Hs5].
 destruct(machine230_left_view_total M 113(two*tail+one)a)as[s6 Hs6].
 destruct(machine230_left_view_total M 97(two+four*tail)left)as[t Ht].
 assert(H1:machine230_step M s s1).
 { apply(machine230_right_view_step M 0 false true 94 left(two*tail)).
   -reflexivity.
   -change(machine230_right_view M 0 left(Z+two*(two*tail))s).
    replace(Z+two*(two*tail))with(four*(two+four*rest));[exact Hs|].
    unfold tail;rewrite F;ring.
   -exact Hs1. }
 assert(H2:machine230_step M s1 s2).
 { apply(machine230_right_view_step M 94 false false 66 a tail).
   -reflexivity.
   -change(machine230_right_view M 94 a(Z+two*tail)s1).
    replace(Z+two*tail)with(two*tail)by ring;exact Hs1.
   -change(machine230_right_view M 66(two*a+Z)tail s2).
    replace(two*a+Z)with b by(unfold b;ring);exact Hs2. }
 assert(H3:machine230_step M s2 s3).
 { apply(machine230_right_view_step M 66 false true 198 b(one+two*rest)).
   -reflexivity.
   -change(machine230_right_view M 66 b(Z+two*(one+two*rest))s2).
    replace(Z+two*(one+two*rest))with tail;[exact Hs2|].
    unfold tail;rewrite F;ring.
   -exact Hs3. }
 assert(H4:machine230_step M s3 s4).
 { apply(machine230_right_to_left_step M 198 true true 113 c rest).
   -reflexivity.
   -exact Hs3.
   -exact Hs4. }
 assert(H5:machine230_step M s4 s5).
 { apply(machine230_left_view_step M 113 true false 97(one+two*rest)b).
   -reflexivity.
   -change(machine230_left_view M 113(one+two*rest)(one+two*b)s4).
    replace(one+two*b)with c by(unfold c;ring);exact Hs4.
   -change(machine230_left_view M 97(two*(one+two*rest)+Z)b s5).
    replace(two*(one+two*rest)+Z)with tail;[exact Hs5|].
    unfold tail;rewrite F;ring. }
 assert(H6:machine230_step M s5 s6).
 { apply(machine230_left_view_step M 97 false true 113 tail a).
   -reflexivity.
   -change(machine230_left_view M 97 tail(Z+two*a)s5).
    replace(Z+two*a)with b by(unfold b;ring);exact Hs5.
   -exact Hs6. }
 assert(H7:machine230_step M s6 t).
 { apply(machine230_left_view_step M 113 true false 97(two*tail+one)left).
   -reflexivity.
   -change(machine230_left_view M 113(two*tail+one)(one+two*left)s6).
    replace(one+two*left)with a by(unfold a;ring);exact Hs6.
   -change(machine230_left_view M 97(two*(two*tail+one)+Z)left t).
    replace(two*(two*tail+one)+Z)with(two+four*tail);[exact Ht|].
    rewrite F;ring. }
 exists t;split;[exact Ht|].
 change(machine230_reaches_in M(S(S(S(S(S(S one))))))s t).
 eapply machine230_reaches_in_step;[exact H1|].
 eapply machine230_reaches_in_step;[exact H2|].
 eapply machine230_reaches_in_step;[exact H3|].
 eapply machine230_reaches_in_step;[exact H4|].
 eapply machine230_reaches_in_step;[exact H5|].
 eapply machine230_reaches_in_step;[exact H6|].
 now apply machine230_reaches_in_one.
Qed.
End ZeroControl.
Print Assumptions machine230_decrement_zero_control.
