(** Finite physical prefixes retain the actual carried left-word witnesses.
    Both forward carry and q97 rollback are constructed from literal paths. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230BitArithmetic
 TM230LeftView TM230Paths TM230ExactPaths TM230UnaryBlocks TM230ReverseBlocks TM230RegisterPrefix
 TM230CarryPlain TM230CarryPrefixes TM230RollbackBlock PowerTwoRecurrence.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint machine230_carry_frame M(values:list(carrier M))left tail word out:Prop:=
 match values with
 |[]=>word=tail /\out=left
 |v::vs=>exists middle nextleft,machine230_unary_block M v middle word /\
   machine230_carry_prefix_step M v left nextleft /\machine230_carry_frame M vs nextleft tail middle out
 end.
Lemma machine230_carry_prefix_step_functional M v left out out':
 machine230_carry_prefix_step M v left out->machine230_carry_prefix_step M v left out'->out=out'.
Proof.
 intros[p[k[Hp[Hpk Hout]]]][q[j[Hq[Hqj Hout']]]].
 assert(Ep:p=q)by(eapply power2_functional;eassumption).
 assert(Ek:k=j)by(apply(succ_injective M);congruence). congruence.
Qed.
Theorem machine230_carry_frame_construct M values left tail word:
 machine230_blocks_list M values tail word->exists out,machine230_carry_frame M values left tail word out.
Proof.
 revert left word. induction values as[|v vs IH];intros left word H.
 -exists left. split;[exact H|reflexivity].
 -destruct H as[middle[Htail Hhead]].
  destruct(machine230_carry_prefix_step_total M v left)as[nextleft Hnext].
  destruct(IH nextleft middle Htail)as[out Hframe]. exists out,middle,nextleft;auto.
Qed.
Theorem machine230_carry_frame_forward M values left tail word out s:
 machine230_carry_frame M values left tail word out ->machine230_right_view M 0 left word s ->
 exists t,machine230_right_view M 0 out tail t /\machine230_reaches M s t.
Proof.
 revert left word out s. induction values as[|v vs IH];intros left word out s Hframe Hs.
 -destruct Hframe as[-> ->]. exists s;split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hhead[Hstep Hframe]]]].
  destruct(machine230_carry_plain_block M v left middle word s Hhead Hs)
   as[p[k[mid[Hp[Hpk[Hmid Hpath]]]]]].
  assert(Hactual:machine230_carry_prefix_step M v left
   (addM M(mulM M p(addM M(mulM M(code_numeral M 4)left)(code_numeral M 2)))k)).
  {exists p,k;auto. }
  assert(E:addM M(mulM M p(addM M(mulM M(code_numeral M 4)left)(code_numeral M 2)))k=nextleft)
   by(eapply machine230_carry_prefix_step_functional;eassumption).
  rewrite E in Hmid. destruct(IH nextleft middle out mid Hframe Hmid)as[t[Ht Htail]].
  exists t. split;[exact Ht|]. eapply machine230_reaches_trans;[|exact Htail].
  eapply machine230_reaches_in_forget;exact Hpath.
Qed.
Theorem machine230_carry_frame_rollback M values left tail word out right s:
 machine230_carry_frame M values left tail word out ->machine230_left_view M 97 right out s ->
 exists restored t,machine230_blocks_list M values right restored /\
 machine230_left_view M 97 restored left t /\machine230_reaches M s t.
Proof.
 revert left word out right s. induction values as[|v vs IH];intros left word out right s Hframe Hs.
 -destruct Hframe as[Hw ->]. exists right,s.
  split;[reflexivity|]. split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hhead[Hstep Hframe]]]].
  destruct(IH nextleft middle out right s Hframe Hs)as[inside[mid[Hinside[Hmid Hpath]]]].
  destruct Hstep as[p[k[Hp[Hpk Hnext]]]]. rewrite Hnext in Hmid.
  destruct(machine230_rollback_one_block M v p k left inside mid Hp Hpk Hmid)
   as[restored[t[Hrestored[Ht Htail]]]].
  exists restored,t. split;[exists inside;auto|]. split;[exact Ht|].
  eapply machine230_reaches_trans;[exact Hpath|].
  eapply machine230_reaches_in_forget;exact Htail.
Qed.
Print Assumptions machine230_carry_frame_construct.
Print Assumptions machine230_carry_frame_forward.
Print Assumptions machine230_carry_frame_rollback.
