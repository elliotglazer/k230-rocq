(** Complete zero-decrement branch: the target and its next block are restored,
    then every carried physical-prefix block is rolled back. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BitArithmetic TM230LeftView
 TM230Paths TM230ExactPaths TM230UnaryBlocks TM230RegisterPrefix TM230CarryFrames TM230ZeroBlock.
Unset Implicit Arguments.
Theorem machine230_box_decrement_zero M prefix nextvalue left tail next target word s:
 machine230_unary_block M nextvalue tail next ->machine230_marked_block M(zeroM M)next target ->
 machine230_blocks_list M prefix target word ->machine230_right_view M 0 left word s ->
 exists target' restored t,machine230_unary_block M(zeroM M)next target' /\
 machine230_blocks_list M prefix target' restored /\machine230_left_view M 97 restored left t /\
 machine230_reaches M s t.
Proof.
 intros Hnext Htarget Hprefix Hs.
 destruct(machine230_carry_frame_construct M prefix left target word Hprefix)as[out Hframe].
 destruct(machine230_carry_frame_forward M prefix left target word out s Hframe Hs)as[mid[Hmid HF]].
 destruct(machine230_decrement_zero_target M nextvalue out tail next target mid Hnext Htarget Hmid)
  as[target'[nextState[Htarget'[HnextState Hpoint]]]].
 destruct(machine230_carry_frame_rollback M prefix left target word out target' nextState Hframe HnextState)
  as[restored[t[Hrestored[Ht HR]]]].
 exists target',restored,t. split;[exact Htarget'|]. split;[exact Hrestored|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[exact HF|]. eapply machine230_reaches_trans;[|exact HR].
 eapply machine230_reaches_in_forget;exact Hpoint.
Qed.
Print Assumptions machine230_box_decrement_zero.
