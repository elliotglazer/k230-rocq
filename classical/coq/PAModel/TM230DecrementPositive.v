(** Four literal transitions decrement a positive marked register. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions
 TM230BinaryStep TM230BitArithmetic TM230LeftView TM230SymbolicCells TM230ExactPaths
 TM230UnaryBlocks PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Decrement.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_decrement_ring:(model_semiring M).
Theorem machine230_decrement_positive_target value left tail word s:
 machine230_marked_block M(S value)tail word ->machine230_right_view M 0 left word s ->
 exists restored t,machine230_unary_block M value tail restored /\
 machine230_left_view M 40 restored(one+two*left)t /\
 machine230_reaches_in M four s t.
Proof.
 intros[big[j[Hbig[Hbigj Hword]]]]Hs.
 destruct(power2_successor_inv M value big Hbig)as[p[Hp Ep]].
 destruct(power2_positive_successor M value p Hp)as[k Hpk].
 change(big=two*p)in Ep.
 assert(Ej:j=S(two*k)).
 {apply(succ_injective M). rewrite <-Hbigj,Ep,Hpk.
  rewrite(succ_as_add M k),(succ_as_add M(S(two*k))),(succ_as_add M(two*k)),(succ_as_add M one). ring. }
 set(rest:=k+p*tail).
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 assert(Hword':word=two*(two*(one+two*rest))).
 {change(word=four*j+(four*big)*tail)in Hword. rewrite Hword,Ej,Ep,F.
  unfold rest. rewrite(succ_as_add M(two*k)),(succ_as_add M one). ring. }
 set(restored:=two*(one+two*rest)).
 destruct(machine230_right_view_total M 94(two*left+one)(two*(one+two*rest)))as[s1 Hs1].
 destruct(machine230_right_view_total M 66(two*(two*left+one))(one+two*rest))as[s2 Hs2].
 destruct(machine230_left_view_total M 54(one+two*rest)(two*(two*left+one)))as[s3 Hs3].
 destruct(machine230_left_view_total M 40 restored(one+two*left))as[t Ht].
 assert(H1:machine230_step M s s1).
 {apply(machine230_right_view_step M 0 false true 94 left(two*(one+two*rest))).
  -reflexivity.
  -change(machine230_right_view M 0 left(Z+two*(two*(one+two*rest)))s).
   replace(Z+two*(two*(one+two*rest)))with word;[exact Hs|rewrite Hword';ring].
  -exact Hs1. }
 assert(H2:machine230_step M s1 s2).
 {apply(machine230_right_view_step M 94 false false 66(two*left+one)(one+two*rest)).
  -reflexivity.
  -change(machine230_right_view M 94(two*left+one)(Z+two*(one+two*rest))s1).
   replace(Z+two*(one+two*rest))with(two*(one+two*rest))by ring;exact Hs1.
  -change(machine230_right_view M 66(two*(two*left+one)+Z)(one+two*rest)s2).
   replace(two*(two*left+one)+Z)with(two*(two*left+one))by ring;exact Hs2. }
 assert(H3:machine230_step M s2 s3).
 {exact(machine230_right_to_left_step M 66 true true 54(two*(two*left+one))rest s2 s3 eq_refl Hs2 Hs3). }
 assert(H4:machine230_step M s3 t).
 {apply(machine230_left_view_step M 54 false false 40(one+two*rest)(one+two*left)).
  -reflexivity.
  -change(machine230_left_view M 54(one+two*rest)(Z+two*(one+two*left))s3).
   replace(Z+two*(one+two*left))with(two*(two*left+one))by ring;exact Hs3.
  -change(machine230_left_view M 40(two*(one+two*rest)+Z)(one+two*left)t).
   replace(two*(one+two*rest)+Z)with restored by(unfold restored;ring);exact Ht. }
 exists restored,t. split.
 -exists big,j. split;[exact Hbig|]. split;[exact Hbigj|].
  change(restored=two*j+(two*big)*tail). unfold restored,rest.
  rewrite Ej,Ep,(succ_as_add M(two*k)),(succ_as_add M one). ring.
 -split;[exact Ht|].
  change(machine230_reaches_in M(S(S(S one)))s t).
  exact(machine230_reaches_in_step M s s1 t(S(S one))H1
   (machine230_reaches_in_step M s1 s2 t(S one)H2
    (machine230_reaches_in_step M s2 s3 t one H3(machine230_reaches_in_one M s3 t H4)))).
Qed.
End Decrement.
Print Assumptions machine230_decrement_positive_target.

