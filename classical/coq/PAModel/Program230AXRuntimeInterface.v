(** Common actual-history result for the AX primitive consumers. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs CodeExpressions Program230Configurations
 Program230Histories Program230InstructionFormula Program230PathCode
 Program230AXSymbolicGraphs.
From Stdlib Require Import Lists.List Bool.Bool.
Unset Implicit Arguments.
Definition p230_ax_runtime_result M env after start (exit:list bool) : Prop :=
 exists b c time last,
 program230_history M p230_instruction_formula b c time start /\
 program230_state_at M b c time last /\
 coding_lt M (zeroM M) time /\
 program230_pc last=program230_path_value M exit /\
 p230_ax_register_graph M env after last.
