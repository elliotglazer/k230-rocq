(** Complete positive-decrement branch over every finite physical prefix. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BitArithmetic
 TM230LeftView TM230Paths TM230ExactPaths TM230UnaryBlocks TM230RegisterPrefix
 TM230CarryPhysicalPrefix TM230DecrementPositive TM230IncrementReturn.
Unset Implicit Arguments.
Theorem machine230_box_decrement_positive M prefix value left tail target word s:
 machine230_marked_block M(succM M value)tail target ->
 machine230_blocks_list M prefix target word ->machine230_right_view M 0 left word s ->
 exists target' restored t,machine230_unary_block M value tail target' /\
 machine230_blocks_list M prefix target' restored /\
 machine230_left_view M 40 restored
  (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)left))t /\machine230_reaches M s t.
Proof.
 intros Htarget Hprefix Hs.
 destruct(machine230_carry_physical_prefix M prefix left target word s Hprefix Hs)
  as[out[mid[Hframe[Hmid Hcarry]]]].
 destruct(machine230_decrement_positive_target M value out tail target mid Htarget Hmid)
  as[target'[next[Htarget'[Hnext Hpoint]]]].
 destruct(machine230_return_plain_prefix M prefix
  (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)left))target word
  (addM M(succM M(zeroM M))(mulM M(code_numeral M 2)out))target' next Hframe Hnext)
  as[restored[t[Hrestored[Ht Hreturn]]]].
 exists target',restored,t. split;[exact Htarget'|]. split;[exact Hrestored|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[exact Hcarry|]. eapply machine230_reaches_trans;[|exact Hreturn].
 eapply machine230_reaches_in_forget;exact Hpoint.
Qed.
Print Assumptions machine230_box_decrement_positive.
