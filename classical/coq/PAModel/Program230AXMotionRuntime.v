(** Literal increment and transfer executions in the AX register graph. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryConstructors Program230InstructionFormula
 Program230PathCode Program230Read Program230Walk Program230Edges Program230Transition
 Program230TransferStates Program230TransferProgram Program230TransferCycle Program230TransferLoop Program230TransferEntry
 Program230RegisterLoops Program230AXSymbolic Program230AXSymbolicGraphs Program230AXGraphEffects
 Program230AXNativeSymbolic Program230AXRuntimeInterface.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_ax_runtime_increment M env symbolic start P:
 fol p230(ENode(root p230))P=Some(EInc 1) ->
 program230_pc start=program230_path_value M P ->p230_ax_register_graph M env symbolic start ->
 p230_ax_runtime_result M env(p230_ax_set symbolic 1(p230_ax_native_succ(program230_register symbolic 1)))start(inc_path P).
Proof.
 intros HF HP HG.
 set(last:=p230_ax_actual_set M start 1(succM M(program230_register start 1))(program230_path_value M(inc_path P))).
 assert(HS:Program230Histories.program230_step M p230_instruction_formula start last).
 {apply p230_instruction_formula_correct;rewrite HP.
  exists(EInc 1),P,(succM M(zeroM M));split.
  -split;[apply program230_read_exact_path|split;[exact HF|reflexivity]].
  -split;[lia|split;[reflexivity|]].
   intros i Hi;unfold last;rewrite p230_ax_actual_set_register by exact Hi;reflexivity. }
 destruct(program230_history_one M p230_instruction_formula start last HS)as[b[c[HR HT]]].
 exists b,c,(succM M(zeroM M)),last;split;[exact HR|split;[exact HT|]].
 split;[apply coding_zero_lt_succ|split;[reflexivity|unfold last;apply p230_ax_graph_inc;exact HG]].
Qed.
Lemma p230_ax_runtime_transfer M env symbolic start P a b n m:
 (a<9)%nat->(b<9)%nat->a<>b->program230_transfer_occurrence p230 P a b n m ->
 env 2=addM M(env 1)(env 11) ->program230_pc start=program230_path_value M P ->
 p230_ax_register_graph M env symbolic start ->
 p230_ax_runtime_result M env
 (p230_ax_set(p230_ax_set symbolic b(p230_ax_native_add(program230_register symbolic b)(program230_register symbolic a)))a(CEconst 0))start(inc_path P).
Proof.
 intros Ha Hb Hab HO HE HP HG.
 destruct(p230_transfer_record M P P a b n m start(program230_register start a)Ha Hb Hab HO HP(fun i=>eq_refl)eq_refl)
 as[u[v[HR HT]]].
 set(last:=program230_transfer_state a b start(program230_path_value M(inc_path P))(zeroM M)
 (addM M(program230_register start b)(program230_register start a))).
 exists u,v,(program230_transfer_time M(program230_register start a)),last.
 split;[exact HR|split;[exact HT|split;[apply program230_transfer_time_positive|split;[reflexivity|]]]].
 assert(E:last=p230_ax_actual_set M(p230_ax_actual_set M start b(addM M(program230_register start b)(program230_register start a))(program230_path_value M(inc_path P)))a(zeroM M)(program230_path_value M(inc_path P))).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
  change(program230_register(program230_transfer_state a b start(program230_path_value M(inc_path P))(zeroM M)
  (addM M(program230_register start b)(program230_register start a)))j=
  program230_register(p230_ax_actual_set M(p230_ax_actual_set M start b(addM M(program230_register start b)(program230_register start a))(program230_path_value M(inc_path P)))a(zeroM M)(program230_path_value M(inc_path P)))j).
  rewrite program230_transfer_register,!p230_ax_actual_set_register by lia.
  destruct(Nat.eqb j a), (Nat.eqb j b);reflexivity. }
 rewrite E;apply p230_ax_graph_transfer;assumption.
Qed.
Print Assumptions p230_ax_runtime_increment.
Print Assumptions p230_ax_runtime_transfer.
