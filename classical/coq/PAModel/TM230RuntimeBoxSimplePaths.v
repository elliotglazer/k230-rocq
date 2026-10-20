(** Actual marker and decrement paths for the concrete physical runtime box. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions TM230UnaryBlocks
 TM230RegisterPrefix TM230SpareSyntax TM230SpareRecurrence TM230SpareBlocks
 TM230RuntimeBox TM230RuntimeBoxProperties TM230BoxMark TM230BoxDecrementZero TM230BoxDecrementPositive
 TM230BitArithmetic TM230LeftView TM230Paths TM230SkipBlock.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Simple.
Variable M:Model.
Local Notation Z:=(zeroM M).
Lemma machine230_runtime_nth_value values r v:
 nth_error values r=Some v->nth r values Z=v.
Proof.
 induction values as[|x values IH]in r|-*;destruct r;cbn;intro H;try discriminate.
 -now injection H as <-.
 -now apply IH.
Qed.
Lemma machine230_runtime_firstn_length(values:list(carrier M))r:
 length values=9%nat->(r<9)%nat->length(firstn r values)=r.
Proof. intros HL HR;rewrite firstn_length,HL;lia. Qed.
Lemma machine230_runtime_return_exit(prefix:list(carrier M))r:
 length prefix=r->machine230_return_exit 1 prefix=Runtime230.mark_exit r.
Proof. destruct prefix as[|x prefix];cbn[length];intro H;subst r;reflexivity. Qed.
Lemma machine230_runtime_spare_head E spare:
 coding_lt M Z E->machine230_spare M E spare->
 exists value tail,machine230_unary_block M value tail spare.
Proof.
 intros HE HS. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
 (fun ax H rho=>axioms M ax rho H)E)as[EE|[d EE]];subst E.
 -exfalso;exact(coding_not_lt_zero M Z HE).
 -destruct(machine230_spare_successor_inv M d spare HS)as[tail[HT ET]].
  exists(code_numeral M 1),tail. apply(proj2(machine230_unary_block_one M tail spare));exact ET.
Qed.
Lemma machine230_runtime_suffix_head values E spare word:
 coding_lt M Z E->machine230_spare M E spare->machine230_blocks_list M values spare word->
 exists value tail,machine230_unary_block M value tail word.
Proof.
 destruct values as[|v values];cbn[machine230_blocks_list];intros HE HS HB.
 -subst word;exact(machine230_runtime_spare_head E spare HE HS).
 -destruct HB as[tail[HT HV]]. exists v,tail;exact HV.
Qed.
Theorem machine230_runtime_mark_path values E r left word s:
 (r<9)%nat->machine230_runtime_box M values E(Runtime230.BPlain Runtime230.FNone)word->
 machine230_right_view M(machine230_skip_label r)left word s->
 exists output t,machine230_runtime_box M values E(Runtime230.BMark r)output /\
 machine230_left_view M(Runtime230.mark_exit r)output left t /\machine230_reaches M s t.
Proof.
 intros HR[HL[HE[updated[spare[HU[HS HW]]]]]]HV. change(updated=values)in HU;subst updated.
 destruct(nth_error values r)as[v|]eqn:HN;[|apply nth_error_None in HN;lia].
 destruct(machine230_blocks_list_split M values r v spare word HN HW)as[inside[target[HI[HT HP]]]].
 pose proof(machine230_runtime_firstn_length values r HL HR)as Hlength.
 rewrite <-Hlength in HV.
 destruct(machine230_box_mark M(firstn r values)v left inside target word s ltac:(lia)HT HP HV)
 as[output[t[[target'[HT' HP']][HTview Hpath]]]].
 exists output,t. split.
 -split;[exact HL|]. split;[exact HE|]. exists spare;split;[exact HS|].
  exact(machine230_marked_blocks_join M values r v spare inside target' output HN HI HT' HP').
 -split;[|exact Hpath]. rewrite(machine230_runtime_return_exit(firstn r values)r Hlength)in HTview. exact HTview.
Qed.
Theorem machine230_runtime_decrement_zero_path values E r left word s:
 (r<9)%nat->nth r values Z=Z->machine230_runtime_box M values E(Runtime230.BMark r)word->
 machine230_right_view M 0 left word s->
 exists output t,machine230_runtime_box M values E(Runtime230.BPlain Runtime230.FNone)output /\
 machine230_left_view M 97 output left t /\machine230_reaches M s t.
Proof.
 intros HR Hzero[HL[HE[spare[HS HW]]]]HV.
 destruct(nth_error values r)as[v|]eqn:HN;[|apply nth_error_None in HN;lia].
 assert(Ev:v=Z)by(pose proof(machine230_runtime_nth_value values r v HN);congruence). subst v.
 destruct(machine230_marked_blocks_split M values r Z spare word HN HW)as[inside[target[HI[HT HP]]]].
 destruct(machine230_runtime_suffix_head(skipn(S r)values)E spare inside HE HS HI)as[nextvalue[tail Hnext]].
 destruct(machine230_box_decrement_zero M(firstn r values)nextvalue left tail inside target word s Hnext HT HP HV)
 as[target'[output[t[HT'[HP'[HTview Hpath]]]]]].
 exists output,t. split.
 -split;[exact HL|]. split;[exact HE|]. exists values,spare. split;[reflexivity|]. split;[exact HS|].
  exact(machine230_blocks_list_join M values r Z spare inside target' output HN HI HT' HP').
 -auto.
Qed.
Theorem machine230_runtime_decrement_positive_path values E r left word s:
 (r<9)%nat->nth r values Z<>Z->machine230_runtime_box M values E(Runtime230.BMark r)word->
 machine230_right_view M 0 left word s->
 exists output t,machine230_runtime_box M values E(Runtime230.BPlain(Runtime230.FDec r))output /\
 machine230_left_view M 40 output(addM M(code_numeral M 1)(mulM M(code_numeral M 2)left))t /\
 machine230_reaches M s t.
Proof.
 intros HR Hpositive[HL[HE[spare[HS HW]]]]HV.
 destruct(nth_error values r)as[v|]eqn:HN;[|apply nth_error_None in HN;lia].
 assert(Hv:v<>Z)by(pose proof(machine230_runtime_nth_value values r v HN);congruence).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
 (fun ax H rho=>axioms M ax rho H)v)as[Ev|[new Ev]];[contradiction|]. subst v.
 destruct(machine230_marked_blocks_split M values r(succM M new)spare word HN HW)
 as[inside[target[HI[HT HP]]]].
 destruct(machine230_box_decrement_positive M(firstn r values)new left inside target word s HT HP HV)
 as[target'[output[t[HT'[HP'[HTview Hpath]]]]]].
 exists output,t. split.
 -split;[exact HL|]. split;[exact HE|]. exists(machine230_update_values r new values),spare.
  split.
  +exists(succM M new),new. split;[exact HN|]. split;[now right|reflexivity].
  +split;[exact HS|]. exact(machine230_blocks_list_update M values r(succM M new)new spare inside target' output HN HI HT' HP').
 -auto.
Qed.
End Simple.
Print Assumptions machine230_runtime_mark_path.
Print Assumptions machine230_runtime_decrement_zero_path.
Print Assumptions machine230_runtime_decrement_positive_path.