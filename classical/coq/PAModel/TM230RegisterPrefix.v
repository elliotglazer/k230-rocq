(** A fixed physical-register prefix with arbitrary arithmetic register values. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230BitArithmetic TM230Paths
 TM230ExactPaths TM230UnaryBlocks TM230SkipBlock TM230ReverseBlocks.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint machine230_blocks_list M(values:list(carrier M))tail word:Prop:=
 match values with[]=>word=tail|v::vs=>exists middle,
 machine230_blocks_list M vs tail middle /\machine230_unary_block M v middle word end.
Fixpoint machine230_prefix_frame M(values:list(carrier M))left tail word reverse:Prop:=
 match values with
 |[]=>word=tail /\reverse=left
 |v::vs=>exists middle nextleft,machine230_unary_block M v middle word /\
 machine230_reverse_block M v left nextleft /\machine230_prefix_frame M vs nextleft tail middle reverse
 end.
Lemma machine230_prefix_frame_construct M values left tail word:
 machine230_blocks_list M values tail word->exists reverse,machine230_prefix_frame M values left tail word reverse.
Proof.
 revert left word. induction values as[|v vs IH];intros left word H.
 -exists left. split;[exact H|reflexivity].
 -destruct H as[middle[Htail Hhead]].
  destruct(machine230_reverse_block_total M v left)as[nextleft Hnext].
  destruct(IH nextleft middle Htail)as[reverse Hframe].
  exists reverse,middle,nextleft. auto.
Qed.
Lemma machine230_reaches_in_forget M n s t:
 machine230_reaches_in M n s t->machine230_reaches M s t.
Proof. intros[b[c H]]. exists b,c,n. exact H. Qed.
Theorem machine230_skip_prefix M values left tail word reverse m s:
 (length values+m<9)%nat->machine230_prefix_frame M values left tail word reverse ->
 machine230_right_view M(machine230_skip_label(length values+m))left word s ->
 exists t,machine230_right_view M(machine230_skip_label m)reverse tail t /\machine230_reaches M s t.
Proof.
 revert left word reverse s. induction values as[|v vs IH];intros left word reverse s Hbound Hframe Hs.
 -destruct Hframe as[-> ->]. exists s. split;[exact Hs|apply machine230_reaches_refl].
 -destruct Hframe as[middle[nextleft[Hblock[Hreverse Hframe]]]].
  change(machine230_right_view M(machine230_skip_label(Datatypes.S(length vs+m)))left word s)in Hs.
  destruct(machine230_skip_register M(length vs+m)v left middle word s ltac:(cbn in Hbound;lia)Hblock Hs)
   as[p[k[mid[Hp[Hpk[Hmid Hpath]]]]]].
  pose proof(machine230_skip_output_reverse M v p k left Hp Hpk)as Hreverse'.
  assert(E:addM M(mulM M p(mulM M(code_numeral M 2)left))k=nextleft)
   by(eapply machine230_reverse_block_functional;eassumption).
  rewrite E in Hmid.
  destruct(IH nextleft middle reverse mid ltac:(cbn in Hbound;lia)Hframe Hmid)as[t[Ht Htail]].
  exists t. split;[exact Ht|]. eapply machine230_reaches_trans;[|exact Htail].
  eapply machine230_reaches_in_forget;exact Hpath.
Qed.
Print Assumptions machine230_prefix_frame_construct.
Print Assumptions machine230_skip_prefix.
