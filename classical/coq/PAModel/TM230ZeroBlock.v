(** The actual zero register branch requires one ordinary following block. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230BitArithmetic
 TM230LeftView TM230Paths TM230ExactPaths TM230UnaryBlocks TM230CarryPlain
 TM230DecrementZeroControl PowerTwoSyntax PowerTwoRecurrence.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Zero.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Notation four:=(code_numeral M 4).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_zero_block_ring:(model_semiring M).
Lemma machine230_zero_marked tail:machine230_marked_block M Z tail(four*tail).
Proof.
 exists one,Z. split;[apply power2_zero_iff;reflexivity|]. split;[reflexivity|].
 change(four*tail=four*Z+(four*one)*tail). rewrite(succ_as_add M Z);ring.
Qed.
Lemma machine230_zero_plain tail:machine230_unary_block M Z tail(two+four*tail).
Proof.
 assert(Hp:power2 M one two).
 {replace two with(mulM M(code_numeral M 2)one)by(change(two*one=two);rewrite(succ_as_add M Z);ring).
  exact(power2_successor M Z one(proj2(power2_zero_iff M one)eq_refl)). }
 exists two,one. split;[exact Hp|]. split;[reflexivity|].
 change(two+four*tail=two*one+(two*two)*tail).
 assert(F:four=two*two).
 {change(S(S(S(S Z)))=two*two). rewrite(succ_as_add M(S(S(S Z)))),(succ_as_add M(S(S Z))),(succ_as_add M one). ring. }
 rewrite F,(succ_as_add M Z);ring.
Qed.
Theorem machine230_decrement_zero_target nextvalue left tail next target s:
 machine230_unary_block M nextvalue tail next ->machine230_marked_block M Z next target ->
 machine230_right_view M 0 left target s ->
 exists restored t,machine230_unary_block M Z next restored /\
 machine230_left_view M 97 restored left t /\machine230_reaches_in M(code_numeral M 7)s t.
Proof.
 intros Hnext Htarget Hs.
 assert(Et:target=four*next)by(eapply machine230_marked_block_functional;[exact Htarget|apply machine230_zero_marked]).
 destruct(machine230_plain_carry_shape M nextvalue tail next Hnext)as[p[k[Hp[Hpk Enext]]]].
 change(next=two+four*(k+p*tail))in Enext.
 rewrite Et,Enext in Hs.
 destruct(machine230_decrement_zero_control M(k+p*tail)left s Hs)as[t[Ht HP]].
 exists(two+four*next),t. split;[apply machine230_zero_plain|]. split;[now rewrite Enext|exact HP].
Qed.
End Zero.
Print Assumptions machine230_decrement_zero_target.

