(** Arithmetic faithfulness of the literal runtime's token merging and norm.
    The finite wellformedness condition excludes nonfinal SBox segments. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230RunPrefixes
 TM230SymbolicSegments TM230SymbolicCells TM230RuntimeWords.
From K230 Require Runtime230Core.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint machine230_runtime_tokens M gap(Box:Runtime230.boxst->carrier M->Prop)
 (ts:list Runtime230.tok)(word:carrier M):Prop:=
 match ts with
 |[]=>word=zeroM M
 |Runtime230.TRun b a c::ts=>exists middle,machine230_runtime_tokens M gap Box ts middle /\
   machine230_segment_value M gap(machine230_make_segment b a c)middle word
 |Runtime230.TBox x::ts=>ts=[] /\Box x word
 end.
Fixpoint machine230_runtime_segments_wf(ss:list Runtime230.seg):Prop:=
 match ss with[]=>True|Runtime230.SBox _::ss=>ss=[]|_::ss=>machine230_runtime_segments_wf ss end.
Fixpoint machine230_runtime_tokens_wf(ts:list Runtime230.tok):Prop:=
 match ts with[]=>True|Runtime230.TBox _::ts=>ts=[]|_::ts=>machine230_runtime_tokens_wf ts end.
Lemma machine230_runtime_flat_wf M gap Box ss word:
 machine230_runtime_flat M gap Box ss word->machine230_runtime_segments_wf ss.
Proof.
 revert word. induction ss as[|[b|b a c|x]ss IH];intros word H;[exact I| | |exact(proj1 H)].
 -destruct H as[mid[Htail _]];exact(IH mid Htail).
 -destruct H as[mid[Htail _]];exact(IH mid Htail).
Qed.
Section Tokens.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_runtime_tokens_ring:(model_semiring M).
Lemma machine230_runtime_numeral_add a b:N(a+b)=N a+N b.
Proof.
 induction a as[|a IH];cbn[Nat.add code_numeral];[symmetry;apply Arithmetic.add_zero|].
 now rewrite Arithmetic.add_succ,IH.
Qed.
Lemma machine230_runtime_prefix_split b n m tail word:
 machine230_run_prefix M b(n+m)tail word <->exists middle,
 machine230_run_prefix M b m tail middle /\machine230_run_prefix M b n middle word.
Proof.
 split.
 -intro H. destruct(machine230_run_prefix_total M b m tail)as[mid HM].
  destruct(machine230_run_prefix_total M b n mid)as[out HO].
  pose proof(machine230_run_prefix_add M b n m tail mid out HM HO)as Hall.
  assert(E:out=word)by(eapply machine230_run_prefix_functional;eassumption). subst out.
  exists mid;auto.
 -intros[mid[HM HN]];exact(machine230_run_prefix_add M b n m tail mid word HM HN).
Qed.
Theorem machine230_runtime_segment_merge gap b a c a' c' tail word:
 machine230_segment_value M gap(machine230_make_segment b(a+a')(c+c'))tail word <->
 exists middle,machine230_segment_value M gap(machine230_make_segment b a' c')tail middle /\
 machine230_segment_value M gap(machine230_make_segment b a c)middle word.
Proof.
 unfold machine230_segment_value,machine230_segment_length.
 cbn[machine230_segment_bit machine230_segment_factor machine230_segment_constant].
 rewrite !machine230_runtime_numeral_add.
 replace((N a+N a')*gap+(N c+N c'))with((N a*gap+N c)+(N a'*gap+N c'))by ring.
 apply machine230_runtime_prefix_split.
Qed.
Lemma machine230_runtime_token_zero gap Box b ts word:
 machine230_runtime_tokens M gap Box(Runtime230.TRun b 0 0::ts)word <->
 machine230_runtime_tokens M gap Box ts word.
Proof.
 cbn[machine230_runtime_tokens]. unfold machine230_segment_value,machine230_segment_length.
 cbn[machine230_segment_factor machine230_segment_constant code_numeral].
 rewrite Arithmetic.mul_zero,Arithmetic.add_zero. setoid_rewrite machine230_run_prefix_zero.
 split;[intros[mid[H ->]];exact H|intro H;exists word;auto].
Qed.
Lemma machine230_runtime_push_run gap Box b a c ts word:
 (a<>0\/c<>0)->
 (machine230_runtime_tokens M gap Box(Runtime230.push(Runtime230.TRun b a c)ts)word <->
 machine230_runtime_tokens M gap Box(Runtime230.TRun b a c::ts)word).
Proof.
 intro Hnz.
 assert(EP:Runtime230.push(Runtime230.TRun b a c)ts=
  match ts with
  |Runtime230.TRun b' a' c'::rest=>if Bool.eqb b b' then Runtime230.TRun b(a+a')(c+c')::rest
     else Runtime230.TRun b a c::ts
  |_=>Runtime230.TRun b a c::ts end).
 {destruct a,c;try reflexivity;exfalso;tauto. }
 rewrite EP. destruct ts as[|[b' a' c'|x]ts];try reflexivity.
 destruct(Bool.eqb b b')eqn:E;[apply Bool.eqb_prop in E;subst b'|reflexivity].
 cbn[machine230_runtime_tokens]. split.
 -intros[tail[HT HM]].
  destruct(proj1(machine230_runtime_segment_merge gap b a c a' c' tail word)HM)as[mid[Hright Hleft]].
  exists mid;split;[exists tail;auto|exact Hleft].
 -intros[mid[[tail[HT Hright]]Hleft]]. exists tail;split;[exact HT|].
  apply(proj2(machine230_runtime_segment_merge gap b a c a' c' tail word));exists mid;auto.
Qed.
Theorem machine230_runtime_push_correct gap Box tok ts word:
 machine230_runtime_tokens M gap Box(Runtime230.push tok ts)word <->
 machine230_runtime_tokens M gap Box(tok::ts)word.
Proof.
 destruct tok as[b a c|x];[|reflexivity].
 destruct(Nat.eq_dec a 0)as[->|Ha],(Nat.eq_dec c 0)as[->|Hc].
 -cbn[Runtime230.push];symmetry;apply machine230_runtime_token_zero.
 -apply machine230_runtime_push_run;tauto.
 -apply machine230_runtime_push_run;tauto.
 -apply machine230_runtime_push_run;tauto.
Qed.
Theorem machine230_runtime_norm_correct gap Box ss word:
 machine230_runtime_segments_wf ss ->
 (machine230_runtime_flat M gap Box ss word <->machine230_runtime_tokens M gap Box(Runtime230.norm ss)word).
Proof.
 revert word. induction ss as[|[b|b a c|x]ss IH];intros word HW;[reflexivity| | |].
 -change(machine230_runtime_flat M gap Box(Runtime230.SB b::ss)word <->
   machine230_runtime_tokens M gap Box(Runtime230.push(Runtime230.TRun b 0 1)(Runtime230.norm ss))word).
  rewrite machine230_runtime_push_correct. cbn[machine230_runtime_flat machine230_runtime_tokens].
  setoid_rewrite <- (IH _ HW). reflexivity.
 -change(machine230_runtime_flat M gap Box(Runtime230.SR b a c::ss)word <->
   machine230_runtime_tokens M gap Box(Runtime230.push(Runtime230.TRun b a c)(Runtime230.norm ss))word).
  rewrite machine230_runtime_push_correct. cbn[machine230_runtime_flat machine230_runtime_tokens].
  setoid_rewrite <- (IH _ HW). reflexivity.
 -change(ss=[])in HW;subst ss;cbn[Runtime230.norm Runtime230.tok_of Runtime230.push fold_right machine230_runtime_flat machine230_runtime_tokens];intuition.
Qed.
End Tokens.
Print Assumptions machine230_runtime_prefix_split.
Print Assumptions machine230_runtime_segment_merge.
Print Assumptions machine230_runtime_push_correct.
Print Assumptions machine230_runtime_norm_correct.






