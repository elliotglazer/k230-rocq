(** A checked halt site consumes the same arithmetic dispatcher invariant. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230MacroProgress
 TM230RuntimeBox TM230RuntimeWords TM230RuntimeSites TM230ConcreteSites TM230PhysicalRegisters
 Program230PathCode TM230DispatchCode TM230DispatchNormalization.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem machine230_dispatch_code_halt M P Q read R pc E depth gap excess input s:
 (length Q<=40)%nat->Sites230.run_halt Q=true ->
 Q=firstn read(P++repeat false read)->Forall(eq false)(skipn read P)->
 depth=code_numeral M(length P)->pc=program230_path_value M P ->
 addM M depth gap=addM M excess(code_numeral M Sites230.D0) ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)input ->
 machine230_dispatch_code_view M pc depth gap input s ->
 exists t,machine230_state t=code_numeral M 230 /\machine230_progresses M s t.
Proof.
 intros HQ HC EQ Hclean Ed Ep Hpos HX HS.
 assert(HQB:(length Q<=Sites230.D0)%nat)by(unfold Sites230.D0;lia).
 pose proof(machine230_dispatch_code_read_start M Sites230.D0 P Q read pc depth gap excess input s
  HQB EQ Hclean Ed Ep Hpos HS)as Hstart.
 exact(machine230_concrete_dispatch_halt M(machine230_physical_values M R)E Q excess input s HC HX Hstart).
Qed.
Print Assumptions machine230_dispatch_code_halt.
