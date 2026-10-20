(** Complete increment of a marked physical register with an internally long
    suffix. All source and output suffix histories are genuine beta tables. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions TM230BitArithmetic
 TM230LeftView TM230Paths TM230UnaryBlocks TM230RegisterPrefix TM230ReverseBlocks
 TM230FileForward TM230IncrementReturn TM230CarryChainSyntax TM230PrefixAlignment TM230IncrementSuffix.
Unset Implicit Arguments.
Theorem machine230_box_increment M prefix value left tail target word vb vc wb wc count s:
 machine230_marked_block M value tail target ->machine230_blocks_list M prefix target word ->
 machine230_carry_chain M vb vc wb wc count ->beta M wb wc(zeroM M)tail ->
 beta M wb wc count(zeroM M) ->machine230_right_view M 64 left word s ->
 exists ob oc output target' restored t,machine230_carry_chain M vb vc ob oc count /\
 beta M ob oc(zeroM M)output /\beta M ob oc count(code_numeral M 6) /\
 machine230_unary_block M(succM M value)output target' /\
 machine230_blocks_list M prefix target' restored /\machine230_left_view M 40 restored left t /\
 machine230_reaches M s t.
Proof.
 intros Htarget Hprefix HC Hfirst Hlast Hs.
 destruct(machine230_prefix_frame_construct M prefix left target word Hprefix)as[reverse Hframe].
 destruct(machine230_forward_prefix M prefix left target word reverse s Hframe Hs)as[mid[Hmid HF]].
 destruct(machine230_encoded_file_entry M false value reverse tail target mid Htarget Hmid)
  as[normal[next[Hnormal[Hnext Hentry]]]].
 destruct(machine230_increment_internal_suffix M vb vc wb wc count normal tail next HC Hfirst Hlast Hnext)
  as[ob[oc[output[returnState[HO[HO0[HOn[HreturnState Hsuffix]]]]]]]].
 destruct(machine230_increment_return_prefix M prefix value left target word reverse normal output returnState
  Hframe Hnormal HreturnState)as[target'[restored[t[Htarget'[Hrestored[Ht HR]]]]]].
 exists ob,oc,output,target',restored,t.
 split;[exact HO|]. split;[exact HO0|]. split;[exact HOn|]. split;[exact Htarget'|].
 split;[exact Hrestored|]. split;[exact Ht|].
 eapply machine230_reaches_trans;[exact HF|].
 eapply machine230_reaches_trans;[eapply machine230_reaches_in_forget;exact Hentry|].
 eapply machine230_reaches_trans;[exact Hsuffix|exact HR].
Qed.
Print Assumptions machine230_box_increment.
