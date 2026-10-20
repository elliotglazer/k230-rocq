(** Actual machine witnesses extracted from the unchanged finite site checks.
    The run-to leaf deliberately exposes its exact matching configuration;
    normL faithfulness will identify it with the requested target. *)
From PAModel Require Import Model CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230MacroProgress TM230RuntimeWords
 TM230RuntimeStep TM230RuntimeExec.
From K230 Require Runtime230Core Interpreter230Sites TM230.
From Stdlib Require Import Bool.Bool Arith.Arith.
Unset Implicit Arguments.
Module Sites230:=K230.Interpreter230Sites.
Lemma machine230_runtime_control M gap Box q onleft ls rs s:
 machine230_runtime_view M gap Box(q,onleft,ls,rs)s->machine230_state s=code_numeral M q.
Proof. intros[l[r[HL[HR HS]]]]. destruct onleft;exact(proj1 HS). Qed.
Theorem machine230_runtime_site_run_raw M gap Box br Q expected s:
 (forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail)->
 machine230_runtime_oracle_paths M Box br ->Sites230.run_to br Q expected=true ->
 machine230_runtime_view M gap Box(Sites230.start Q)s ->
 exists actual t,Runtime230.matches actual expected=true /\
 machine230_runtime_view M gap Box actual t /\machine230_progresses M s t.
Proof.
 intros Hhead Horacle. unfold Sites230.run_to.
 destruct(Runtime230.exec Sites230.FUEL br(fun conf=>Runtime230.matches conf expected)
  (Sites230.start Q)false)as[actual|]eqn:HE;[|discriminate]. intros _ HV.
 destruct(machine230_runtime_exec_sound M gap Box br Hhead Horacle Sites230.FUEL
  (fun conf=>Runtime230.matches conf expected)(Sites230.start Q)false actual s HE HV)
  as[HM[t[HT[HR HP]]]].
 exists actual,t;split;[exact HM|]. split;[exact HT|exact(HP eq_refl)].
Qed.
Theorem machine230_runtime_site_halt M gap Box Q s:
 (forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail)->
 machine230_runtime_oracle_paths M Box None ->Sites230.run_halt Q=true ->
 machine230_runtime_view M gap Box(Sites230.start Q)s ->
 exists t,machine230_state t=code_numeral M 230 /\machine230_progresses M s t.
Proof.
 intros Hhead Horacle. unfold Sites230.run_halt.
 destruct(Runtime230.exec Sites230.FUEL None Sites230.is_halt(Sites230.start Q)false)
  as[actual|]eqn:HE;[|discriminate]. intros _ HV.
 destruct(machine230_runtime_exec_sound M gap Box None Hhead Horacle Sites230.FUEL
  Sites230.is_halt(Sites230.start Q)false actual s HE HV)as[HH[t[HT[HR HP]]]].
 destruct actual as[[[q onleft]ls]rs]. unfold Sites230.is_halt in HH.
 apply Nat.eqb_eq in HH. change(q=230)in HH. subst q.
 exists t;split;[exact(machine230_runtime_control M gap Box 230 onleft ls rs t HT)|exact(HP eq_refl)].
Qed.
Print Assumptions machine230_runtime_site_run_raw.
Print Assumptions machine230_runtime_site_halt.
