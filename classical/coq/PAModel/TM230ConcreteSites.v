(** Actual arithmetic site simulation with every register-box and matching
    obligation discharged. The only certificate premise is the literal
    computable public run_to/run_halt check. *)
From PAModel Require Import Model CodeExpressions TM230BinaryStep TM230Paths TM230MacroProgress
 TM230RuntimeWords TM230RuntimeStep TM230RuntimeSites TM230RuntimeSiteTargets TM230DispatchWords
 TM230RuntimeBox TM230RuntimeBoxProperties TM230RuntimeBoxOracle.
Unset Implicit Arguments.
Theorem machine230_concrete_dispatch_site M values E br bits target overflow outbox gap input s:
 machine230_runtime_branch_valid M values br ->
 Sites230.run_to br bits(Sites230.tgt_conf target overflow outbox)=true ->
 machine230_runtime_box M values E(Runtime230.BPlain Runtime230.FNone)input ->
 machine230_dispatch_view M bits gap(Sites230.D0-length bits)input s ->
 exists output t,machine230_runtime_box M values E outbox output /\
 machine230_dispatch_view M target gap
  (Sites230.D0+(if overflow then 1 else 0)+Sites230.growth outbox-length target)output t /\
 machine230_progresses M s t.
Proof.
 intros HB HC HX HS.
 assert(Hstart:machine230_runtime_view M gap(machine230_runtime_box M values E)(Sites230.start bits)s).
 {apply(proj2(machine230_runtime_start_words M gap(machine230_runtime_box M values E)bits s));exists input;auto. }
 destruct(machine230_runtime_site_run M gap(machine230_runtime_box M values E)br bits
  (Sites230.tgt_conf target overflow outbox)s(machine230_runtime_box_head M values E)
  (machine230_concrete_runtime_oracle M values E br HB)HC(machine230_runtime_target_wf target overflow outbox)Hstart)
  as[t[HT HP]].
 apply machine230_runtime_target_words in HT. destruct HT as[output[Houtput Hview]].
 exists output,t;split;[exact Houtput|]. split;assumption.
Qed.
Theorem machine230_concrete_dispatch_halt M values E bits gap input s:
 Sites230.run_halt bits=true ->
 machine230_runtime_box M values E(Runtime230.BPlain Runtime230.FNone)input ->
 machine230_dispatch_view M bits gap(Sites230.D0-length bits)input s ->
 exists t,machine230_state t=code_numeral M 230 /\machine230_progresses M s t.
Proof.
 intros HC HX HS. apply(machine230_runtime_site_halt M gap(machine230_runtime_box M values E)bits s
  (machine230_runtime_box_head M values E)(machine230_concrete_runtime_oracle M values E None I)HC).
 apply(proj2(machine230_runtime_start_words M gap(machine230_runtime_box M values E)bits s));exists input;auto.
Qed.
Print Assumptions machine230_concrete_dispatch_site.
Print Assumptions machine230_concrete_dispatch_halt.
