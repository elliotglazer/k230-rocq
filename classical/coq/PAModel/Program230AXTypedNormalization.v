(** Exact typed public-schedule projection into the checked symbolic evaluator. *)
From PAModel Require Import CodeExpressions Program230Configurations Program230AXPathSchedule
 Program230AXPrimitiveSchedule Program230AXSymbolic Program230AXNativeSymbolic Program230AXSymbolicTrace.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_native_of(op:ax_primitive_op):option p230_ax_native_operation:=
 match op with
 |APush=>Some ANPush |ALoad r=>Some(ANLoad r)|AImplies=>Some ANCons
 |AIncrement 1=>Some ANInc|AUnpair 8=>Some ANUnpair
 |ATransfer a b=>Some(ANTransfer a b)|_=>None end.
Definition p230_ax_typed_operations:=map(fun item=>fst(snd item))p230_ax_primitive_schedule.
Theorem p230_ax_exact_typed_projection:
 map p230_ax_native_of p230_ax_typed_operations=map Some p230_ax_native_program.
Proof. vm_compute;reflexivity. Qed.
Definition p230_ax_typed_step(op:ax_primitive_op)(before:program230_configuration code_expr):=
 match p230_ax_native_of op with Some native=>p230_ax_native_step native before|None=>None end.
Fixpoint p230_ax_typed_execute(ops:list ax_primitive_op)(before:program230_configuration code_expr):=
 match ops with
 |[]=>Some before
 |op::tail=>match p230_ax_typed_step op before with Some after=>p230_ax_typed_execute tail after|None=>None end end.
Theorem p230_ax_exact_typed_normalization:
 p230_ax_typed_execute p230_ax_typed_operations p230_ax_symbolic_initial=Some p230_ax_symbolic_final.
Proof. vm_compute;reflexivity. Qed.
Definition p230_ax_typed_rows:=combine p230_ax_primitive_schedule p230_ax_native_rows.
Theorem p230_ax_typed_rows_positions:map fst p230_ax_typed_rows=p230_ax_primitive_schedule.
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_typed_rows_states:map snd p230_ax_typed_rows=p230_ax_native_rows.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions p230_ax_exact_typed_projection.
Print Assumptions p230_ax_exact_typed_normalization.
Print Assumptions p230_ax_typed_rows_positions.
Print Assumptions p230_ax_typed_rows_states.
