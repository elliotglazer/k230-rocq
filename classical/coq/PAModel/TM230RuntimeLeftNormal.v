(** Arithmetic preservation when normL erases a final blank run. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230RunPrefixes
 TM230SymbolicSegments TM230RuntimeWords TM230RuntimeTokens PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_runtime_push_run_wf b a c ts:
 machine230_runtime_tokens_wf ts ->machine230_runtime_tokens_wf(Runtime230.push(Runtime230.TRun b a c)ts).
Proof.
 intro H. destruct a,c;cbn[Runtime230.push];try exact H;
 destruct ts as[|[b' a' c'|x]ts];cbn[machine230_runtime_tokens_wf];try exact I;try exact H;
 destruct(Bool.eqb b b');exact H.
Qed.
Theorem machine230_runtime_norm_wf ss:
 machine230_runtime_segments_wf ss ->machine230_runtime_tokens_wf(Runtime230.norm ss).
Proof.
 induction ss as[|[b|b a c|x]ss IH];intro H;[exact I| | |].
 -apply machine230_runtime_push_run_wf. exact(IH H).
 -apply machine230_runtime_push_run_wf. exact(IH H).
 -change(ss=[])in H;subst ss;reflexivity.
Qed.
Section LeftNormal.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_left_normal_ring:(model_semiring M).
Lemma machine230_run_prefix_false_zero n word:
 machine230_run_prefix M false n Z word <->word=Z.
Proof.
 split.
 -intros[p[k[Hp[Hpk Hw]]]]. change(word=k*Z+p*Z)in Hw. rewrite Hw;ring.
 -intro E;subst word. destruct(power2_total M n)as[p Hp].
  destruct(power2_positive_successor M n p Hp)as[k Hpk].
  exists p,k. split;[exact Hp|]. split;[exact Hpk|]. change(Z=k*Z+p*Z);ring.
Qed.
Lemma machine230_runtime_false_token_zero gap Box a c word:
 machine230_runtime_tokens M gap Box[Runtime230.TRun false a c]word <->word=Z.
Proof.
 cbn[machine230_runtime_tokens]. split.
 -intros[mid[-> H]]. exact(proj1(machine230_run_prefix_false_zero _ word)H).
 -intro E;subst word. exists Z. split;[reflexivity|]. apply machine230_run_prefix_false_zero;reflexivity.
Qed.
Theorem machine230_runtime_drop_false gap Box ts a c word:
 machine230_runtime_tokens_wf(ts++[Runtime230.TRun false a c])->
 (machine230_runtime_tokens M gap Box(ts++[Runtime230.TRun false a c])word <->
 machine230_runtime_tokens M gap Box ts word).
Proof.
 revert word. induction ts as[|[b aa cc|x]ts IH];intros word Hwf.
 -apply machine230_runtime_false_token_zero.
 -cbn[app machine230_runtime_tokens]. setoid_rewrite(IH _ Hwf). reflexivity.
 -change(ts++[Runtime230.TRun false a c]=[])in Hwf.
  exfalso;apply(app_cons_not_nil ts [] (Runtime230.TRun false a c));symmetry;exact Hwf.
Qed.
Theorem machine230_runtime_tokens_dropz gap Box ts word:
 machine230_runtime_tokens_wf ts ->
 (machine230_runtime_tokens M gap Box ts word <->
 machine230_runtime_tokens M gap Box
  (match rev ts with Runtime230.TRun false _ _::rest=>rev rest|rest=>rev rest end)word).
Proof.
 intro Hwf. pose proof(rev_involutive ts)as E.
 destruct(rev ts)as[|[b a c|x]rest]eqn:Er.
 -cbn in E. now rewrite <-E.
 -destruct b.
  +now rewrite <-E.
  +cbn[rev]in E. rewrite <-E in Hwf|-*.
   apply machine230_runtime_drop_false;exact Hwf.
 -now rewrite <-E.
Qed.
Theorem machine230_runtime_normL_correct gap Box ss word:
 machine230_runtime_segments_wf ss ->
 (machine230_runtime_flat M gap Box ss word <->
 machine230_runtime_tokens M gap Box(Runtime230.normL ss)word).
Proof.
 intro Hwf. rewrite(machine230_runtime_norm_correct M gap Box ss word Hwf).
 unfold Runtime230.normL. apply machine230_runtime_tokens_dropz.
 now apply machine230_runtime_norm_wf.
Qed.
End LeftNormal.
Print Assumptions machine230_runtime_norm_wf.
Print Assumptions machine230_runtime_tokens_dropz.
Print Assumptions machine230_runtime_normL_correct.
