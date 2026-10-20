(** Six literal steps at the all-blank end of a carried increment file. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions
 TM230BinaryStep TM230BitArithmetic TM230LeftView TM230SymbolicCells TM230ExactPaths.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section BlankTail.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring blank_increment_ring:(model_semiring M).
Theorem machine230_increment_blank_tail left s:
 machine230_right_view M 0 left Z s ->
 exists t,machine230_left_view M 40 (N 6) (one+two*left) t /\
  machine230_reaches_in M (N 6) s t.
Proof.
 intro Hs.
 set(a:=two*left+one). set(b:=two*a). set(c:=two*b+one).
 set(r:=two*one+one).
 destruct(machine230_right_view_total M 94 a Z)as[s1 Hs1].
 destruct(machine230_right_view_total M 66 b Z)as[s2 Hs2].
 destruct(machine230_right_view_total M 198 c Z)as[s3 Hs3].
 destruct(machine230_left_view_total M 198 one c)as[s4 Hs4].
 destruct(machine230_left_view_total M 113 r b)as[s5 Hs5].
 destruct(machine230_left_view_total M 40 (two*r) a)as[t Ht].
 assert(H1:machine230_step M s s1).
 { apply(machine230_right_view_step M 0 false true 94 left Z).
   -reflexivity.
   -change(machine230_right_view M 0 left(Z+two*Z)s).
    replace(Z+two*Z)with Z by ring;exact Hs.
   -exact Hs1. }
 assert(H2:machine230_step M s1 s2).
 { apply(machine230_right_view_step M 94 false false 66 a Z).
   -reflexivity.
   -change(machine230_right_view M 94 a(Z+two*Z)s1).
    replace(Z+two*Z)with Z by ring;exact Hs1.
   -change(machine230_right_view M 66(two*a+Z)Z s2).
    replace(two*a+Z)with b by(unfold b;ring);exact Hs2. }
 assert(H3:machine230_step M s2 s3).
 { apply(machine230_right_view_step M 66 false true 198 b Z).
   -reflexivity.
   -change(machine230_right_view M 66 b(Z+two*Z)s2).
    replace(Z+two*Z)with Z by ring;exact Hs2.
   -exact Hs3. }
 assert(H4:machine230_step M s3 s4).
 { apply(machine230_right_to_left_step M 198 false true 198 c Z).
   -reflexivity.
   -change(machine230_right_view M 198 c(Z+two*Z)s3).
    replace(Z+two*Z)with Z by ring;exact Hs3.
   -change(machine230_left_view M 198(one+two*Z)c s4).
    replace(one+two*Z)with one by ring;exact Hs4. }
 assert(H5:machine230_step M s4 s5).
 { apply(machine230_left_view_step M 198 true true 113 one b).
   -reflexivity.
   -change(machine230_left_view M 198 one(one+two*b)s4).
    replace(one+two*b)with c by(unfold c;ring);exact Hs4.
   -exact Hs5. }
 assert(H6:machine230_step M s5 t).
 { apply(machine230_left_view_step M 113 false false 40 r a).
   -reflexivity.
   -change(machine230_left_view M 113 r(Z+two*a)s5).
    replace(Z+two*a)with b by(unfold b;ring);exact Hs5.
   -change(machine230_left_view M 40(two*r+Z)a t).
    replace(two*r+Z)with(two*r)by ring;exact Ht. }
 exists t;split.
 - replace(N 6)with(two*r).
   +replace(one+two*left)with a by(unfold a;ring);exact Ht.
   +unfold r;cbn[code_numeral].
    repeat multimatch goal with
    | |- context[succM M ?x]=>lazymatch x with
      | zeroM _=>fail 0
      | _=>rewrite(succ_as_add M x)
      end
    end;ring.
 - change(machine230_reaches_in M(S(S(S(S(S one)))))s t).
   eapply machine230_reaches_in_step;[exact H1|].
   eapply machine230_reaches_in_step;[exact H2|].
   eapply machine230_reaches_in_step;[exact H3|].
   eapply machine230_reaches_in_step;[exact H4|].
   eapply machine230_reaches_in_step;[exact H5|].
   now apply machine230_reaches_in_one.
Qed.
End BlankTail.
Print Assumptions machine230_increment_blank_tail.
