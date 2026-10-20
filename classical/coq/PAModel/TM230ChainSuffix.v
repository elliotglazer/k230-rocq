(** Extract a genuine internally coded suffix of an ordinary register history. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions
 TM230CarryChainSyntax TM230BetaInterval.
Unset Implicit Arguments.
Theorem machine230_carry_chain_suffix M vb vc sb sc wb wc offset count first last:
 machine230_carry_chain M vb vc wb wc(addM M offset count) ->
 (forall i v,coding_lt M i count->(beta M sb sc i v<->beta M vb vc(addM M offset i)v))->
 beta M wb wc offset first ->beta M wb wc(addM M offset count)last ->
 exists db dc,machine230_carry_chain M sb sc db dc count /\
 beta M db dc(zeroM M)first /\beta M db dc count last.
Proof.
 intros HC HV HF HT.
 destruct(machine230_beta_interval M wb wc offset(succM M count))as[db[dc HP]].
 exists db,dc. split.
 -intros i Hi. destruct(HC(addM M offset i)(coding_lt_add_left M offset i count Hi))
  as[v[w[next[Hval[Hw[Hnext Hblock]]]]]].
  exists v,w,next;split;[apply(proj2(HV i v Hi));exact Hval|]. split.
  +apply(proj1(HP i w(proj2(coding_lt_succ_cases M i count)(or_introl Hi))));exact Hw.
  +split;[|exact Hblock]. apply(proj1(HP(succM M i)next(proj2(coding_lt_succ_cancel M i count)Hi))).
   replace(addM M offset(succM M i))with(succM M(addM M offset i));[exact Hnext|].
   rewrite(Arithmetic.add_comm M offset(succM M i)),(Arithmetic.add_succ M i offset),(Arithmetic.add_comm M i offset);reflexivity.
 -split.
  +apply(proj1(HP(zeroM M)first(coding_zero_lt_succ M count))).
   now rewrite coding_add_zero_r.
  +apply(proj1(HP count last(coding_lt_succ M count)));exact HT.
Qed.
Print Assumptions machine230_carry_chain_suffix.

