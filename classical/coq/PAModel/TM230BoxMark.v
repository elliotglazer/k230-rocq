(** The complete marker oracle for every physical register 0..8. *)
From PAModel Require Import Model CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230UnaryBlocks TM230ReturnBlock TM230ReverseBlocks
 TM230SkipBlock TM230MarkBlock TM230RegisterPrefix.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_return_exit{A}(q:nat)(values:list A):nat:=match values with[]=>q|_=>3 end.
Theorem machine230_return_prefix M values left tail word reverse q right s:
 Public230.tmn q true=Some(true,TM.L,2)->
 machine230_prefix_frame M values left tail word reverse ->machine230_left_view M q right reverse s ->
 exists restored t,machine230_blocks_list M values right restored /\
 machine230_left_view M(machine230_return_exit q values)restored left t /\machine230_reaches M s t.
Proof.
 revert left word reverse q right s. induction values as[|v vs IH];intros left word reverse q right s HE Hframe Hs.
 -destruct Hframe as[Hw Hr]. subst reverse. exists right,s. split;[reflexivity|]. split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hblock[Hreverse Hframe]]]].
  destruct(IH nextleft middle reverse q right s HE Hframe Hs)as[inside[mid[Hinside[Hmid Hpath]]]].
  assert(Hentry:Public230.tmn(machine230_return_exit q vs)true=Some(true,TM.L,2)).
  {destruct vs;[exact HE|reflexivity]. }
  destruct(machine230_reverse_block_return M(machine230_return_exit q vs)2 3 v left inside nextleft mid
   Hentry eq_refl eq_refl Hreverse Hmid)as[restored[t[Hrestored[Ht Htail]]]].
  exists restored,t. split;[exists inside;auto|]. split;[exact Ht|].
  eapply machine230_reaches_trans;[exact Hpath|]. eapply machine230_reaches_in_forget;exact Htail.
Qed.
Definition machine230_marked_file M prefix value tail marked:=exists target,
 machine230_marked_block M value tail target /\machine230_blocks_list M prefix target marked.
Theorem machine230_box_mark M prefix value left tail target word s:
 (length prefix<9)%nat ->machine230_unary_block M value tail target ->
 machine230_blocks_list M prefix target word ->
 machine230_right_view M(machine230_skip_label(length prefix))left word s ->
 exists marked t,machine230_marked_file M prefix value tail marked /\
 machine230_left_view M(machine230_return_exit 1 prefix)marked left t /\machine230_reaches M s t.
Proof.
 intros Hlength Htarget Hprefix Hs.
 destruct(machine230_prefix_frame_construct M prefix left target word Hprefix)as[reverse Hframe].
 assert(Hs':machine230_right_view M(machine230_skip_label(length prefix+0))left word s)
  by(now rewrite Nat.add_0_r).
 destruct(machine230_skip_prefix M prefix left target word reverse 0 s ltac:(lia)Hframe Hs')
  as[mid[Hmid Hskip]].
 change(machine230_right_view M 51 reverse target mid)in Hmid.
 destruct(machine230_mark_target_block M value reverse tail target mid Htarget Hmid)
  as[markedTarget[markedState[Hmarked[HmarkedState HmarkPath]]]].
 destruct(machine230_return_prefix M prefix left target word reverse 1 markedTarget markedState
  eq_refl Hframe HmarkedState)as[marked[t[Hrestored[Ht Hreturn]]]].
 exists marked,t. split;[exists markedTarget;auto|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[exact Hskip|]. eapply machine230_reaches_trans;[|exact Hreturn].
 eapply machine230_reaches_in_forget;exact HmarkPath.
Qed.
Print Assumptions machine230_return_prefix.
Print Assumptions machine230_box_mark.
