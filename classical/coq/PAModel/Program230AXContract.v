(** Exact remaining AX action boundary. This definition is not an implementation theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing SearchStep
 Program230Configurations Program230Histories Program230InstructionFormula
 Program230PathCode Program230Selector Program230SelectorReturn.
Unset Implicit Arguments.

Definition p230_ax_result M(start:program230_configuration(carrier M))top stack pl:=
 mkProgram230Configuration(carrier M)(program230_path_value M p230_selector_return_exit)
 (program230_register start 0)top stack(zeroM M)(zeroM M)(zeroM M)(zeroM M)(zeroM M)pl.

Definition p230_ax_action_contract M:=
 forall start y pl4 u pl5 b top stack,
 program230_pc start=program230_path_value M p230_selector_ax ->
 program230_register start 6=zeroM M ->program230_register start 7=zeroM M ->
 pair_graph M y pl4(program230_register start 8) ->pair_graph M u pl5 pl4 ->
 b=addM M(program230_register start 5)y ->
 search_stack M(program230_register start 4)(program230_register start 5)b
  (program230_register start 3)u(program230_register start 1)(program230_register start 2)stack ->
 (((program230_register start 3=program230_register start 4 \/program230_register start 3=b) /\top=zeroM M) \/
  (program230_register start 3<>program230_register start 4 /\program230_register start 3<>b /\
   search_bundle M(program230_register start 4)b(program230_register start 3)top)) ->
 exists v w time,program230_history M p230_instruction_formula v w time start /\
 program230_state_at M v w time(p230_ax_result M start top stack pl5) /\
 coding_lt M(zeroM M)time.
