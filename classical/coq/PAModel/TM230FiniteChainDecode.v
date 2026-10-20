(** Decode a finite physical prefix and extract its genuine internal suffix
    from any actual returned history, independently of how that history was packed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions TM230UnaryBlocks
 TM230RegisterPrefix TM230CarryChainSyntax TM230FinitePrefixChain TM230ChainSuffix.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Decode.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Theorem machine230_finite_chain_decode values vb vc wb wc total start first last:
 machine230_carry_chain M vb vc wb wc total ->
 (forall j,(j<length values)%nat->coding_lt M(start+N j)total /\
  beta M vb vc(start+N j)(nth j values Z))->
 beta M wb wc start first ->beta M wb wc(start+N(length values))last ->
 machine230_blocks_list M values last first.
Proof.
 intros HC. revert start first. induction values as[|v values IH];intros start first HV HF HT.
 -change(first=last). change(beta M wb wc(start+Z)last)in HT.
  rewrite coding_add_zero_r in HT. eapply beta_unique;eassumption.
 -destruct(HV 0 ltac:(cbn;lia))as[Hbound Hvalue].
  change(coding_lt M(start+Z)total)in Hbound. change(beta M vb vc(start+Z)v)in Hvalue.
  rewrite coding_add_zero_r in Hbound,Hvalue.
  destruct(HC start Hbound)as[value[word[next[Hval[Hword[Hnext Hblock]]]]]].
  assert(Eval:value=v)by(eapply beta_unique;eassumption). subst value.
  assert(Eword:word=first)by(eapply beta_unique;eassumption). subst word.
  exists next;split;[|exact Hblock]. apply(IH(S start)next).
  +intros j Hj. destruct(HV(Datatypes.S j)ltac:(cbn;lia))as[Hjbound Hjvalue].
   change(coding_lt M(start+S(N j))total)in Hjbound.
   change(beta M vb vc(start+S(N j))(nth j values Z))in Hjvalue.
   rewrite(prefix_add_succ_right M start(N j)),<-(Arithmetic.add_succ M start(N j))in Hjbound,Hjvalue.
   split;assumption.
  +exact Hnext.
  +change(beta M wb wc(start+S(N(length values)))last)in HT.
   rewrite(prefix_add_succ_right M start(N(length values))),<-(Arithmetic.add_succ M start(N(length values)))in HT.
   exact HT.
Qed.
Theorem machine230_finite_prefix_suffix_decode values vb vc sb sc wb wc count output tail:
 machine230_carry_chain M vb vc wb wc(N(length values)+count) ->
 (forall j,(j<length values)%nat->beta M vb vc(N j)(nth j values Z))->
 (forall i v,coding_lt M i count->(beta M sb sc i v<->beta M vb vc(N(length values)+i)v))->
 beta M wb wc Z output ->beta M wb wc(N(length values)+count)tail ->
 exists suffix db dc,machine230_blocks_list M values suffix output /\
 machine230_carry_chain M sb sc db dc count /\beta M db dc Z suffix /\beta M db dc count tail.
Proof.
 intros HC Hprefix Hsuffix HF HT.
 destruct(beta_total M wb wc(N(length values)))as[suffix HS].
 assert(Hblocks:machine230_blocks_list M values suffix output).
 {apply(machine230_finite_chain_decode values vb vc wb wc(N(length values)+count)Z output suffix HC).
  -intros j Hj. rewrite Arithmetic.add_zero. split.
   +exact(prefix_lt_add_right M(N j)(N(length values))count(prefix_numeral_lt M j(length values)Hj)).
   +exact(Hprefix j Hj).
  -exact HF.
  -rewrite Arithmetic.add_zero;exact HS. }
 destruct(machine230_carry_chain_suffix M vb vc sb sc wb wc(N(length values))count suffix tail
  HC Hsuffix HS HT)as[db[dc[Hchain[Hstart Hend]]]].
 exists suffix,db,dc;split;[exact Hblocks|]. split;[exact Hchain|]. split;assumption.
Qed.
End Decode.
Print Assumptions machine230_finite_chain_decode.
Print Assumptions machine230_finite_prefix_suffix_decode.
