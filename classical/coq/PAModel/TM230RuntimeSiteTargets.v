(** Literal successful site certificates reach their exact symbolic target.
    Matching normalization and target wellformedness are fully discharged. *)
From PAModel Require Import Model CodeExpressions TM230Paths TM230MacroProgress TM230RuntimeWords
 TM230RuntimeTokens TM230RuntimeMatches TM230RuntimeStep TM230RuntimeSites.
From K230 Require Runtime230Core Interpreter230Sites RM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_runtime_cells_wf bits tail:
 machine230_runtime_segments_wf tail->machine230_runtime_segments_wf(map Runtime230.SB bits++tail).
Proof. induction bits;cbn;auto. Qed.
Theorem machine230_runtime_target_wf bits overflow box:
 machine230_runtime_conf_wf(Sites230.tgt_conf bits overflow box).
Proof.
 unfold Sites230.tgt_conf,machine230_runtime_conf_wf.
 split;[exact I|]. apply machine230_runtime_cells_wf;cbn;reflexivity.
Qed.
Theorem machine230_runtime_site_run M gap Box br Q expected s:
 (forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail)->
 machine230_runtime_oracle_paths M Box br ->Sites230.run_to br Q expected=true ->
 machine230_runtime_conf_wf expected ->machine230_runtime_view M gap Box(Sites230.start Q)s ->
 exists t,machine230_runtime_view M gap Box expected t /\machine230_progresses M s t.
Proof.
 intros HH HO HC HW HV. destruct(machine230_runtime_site_run_raw M gap Box br Q expected s HH HO HC HV)
  as[actual[t[HM[HT HP]]]].
 exists t;split;[exact(machine230_runtime_matches_sound M gap Box actual expected t HM HW HT)|exact HP].
Qed.
Definition machine230_site_branch(op:Sites230.op)(zero_branch:bool):Runtime230.branch:=
 match op with Sites230.ODec r=>Some(r,zero_branch)|_=>None end.
Definition machine230_site_target bits(op:Sites230.op)(zero_branch:bool):option Runtime230.sconf:=
 match op with
 |Sites230.OInc r=>Some(Sites230.tgt_conf(K230.RM.inc_path bits)(Sites230.allones bits)(Runtime230.BPlain(Runtime230.FInc r)))
 |Sites230.ODec r=>Some(if zero_branch then
   Sites230.tgt_conf(K230.RM.brk 1 bits)(Sites230.allones(K230.RM.strip_path false 1 bits))(Runtime230.BPlain Runtime230.FNone)
   else Sites230.tgt_conf(K230.RM.inc_path bits)(Sites230.allones bits)(Runtime230.BPlain(Runtime230.FDec r)))
 |Sites230.OBrk k=>Some(Sites230.tgt_conf(K230.RM.brk k bits)(Sites230.allones(K230.RM.strip_path false k bits))(Runtime230.BPlain Runtime230.FNone))
 |Sites230.OCont k=>Some(Sites230.tgt_conf(K230.RM.cont k bits)false(Runtime230.BPlain Runtime230.FNone))
 |Sites230.OHalt=>None
 end.
Lemma machine230_checked_site_target bits op z expected:
 Sites230.check_site bits op=true ->machine230_site_target bits op z=Some expected ->
 Sites230.run_to(machine230_site_branch op z)bits expected=true.
Proof.
 destruct op as[r|r|k|k|];cbn[machine230_site_target machine230_site_branch Sites230.check_site];
 intros HC HE;try discriminate;try(injection HE as <-;exact HC).
 apply andb_true_iff in HC as[HZ HP]. destruct z;injection HE as <-;assumption.
Qed.
Lemma machine230_site_target_wf bits op z expected:
 machine230_site_target bits op z=Some expected ->machine230_runtime_conf_wf expected.
Proof.
 destruct op as[r|r|k|k|];cbn[machine230_site_target];intro H;try discriminate;
 try(injection H as <-;apply machine230_runtime_target_wf).
 destruct z;injection H as <-;apply machine230_runtime_target_wf.
Qed.
Theorem machine230_runtime_checked_site M gap Box bits op z expected s:
 (forall x word,Box x word->exists tail,word=mulM M(code_numeral M 2)tail)->
 machine230_runtime_oracle_paths M Box(machine230_site_branch op z)->
 Sites230.check_site bits op=true ->machine230_site_target bits op z=Some expected ->
 machine230_runtime_view M gap Box(Sites230.start bits)s ->
 exists t,machine230_runtime_view M gap Box expected t /\machine230_progresses M s t.
Proof.
 intros HH HO HC HE HV. apply(machine230_runtime_site_run M gap Box(machine230_site_branch op z)bits expected s HH HO).
 -exact(machine230_checked_site_target bits op z expected HC HE).
 -exact(machine230_site_target_wf bits op z expected HE).
 -exact HV.
Qed.
Print Assumptions machine230_runtime_site_run.
Print Assumptions machine230_runtime_checked_site.
