(** The literal restore-c and destructive load-a between AX equality tests. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230HistoryJoin Program230InstructionFormula
 Program230PathCode Program230RegisterLoops Program230TransferStates Program230TransferLoop
 Program230TransferEntry Program230AXGateSites Program230ComparisonGuards Program230UnpairRestore.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_gate_state M(base:program230_configuration(carrier M))pc c a b top s t:=
 mkProgram230Configuration(carrier M)pc(program230_register base 0)top
 (program230_register base 2)c a b s t(program230_register base 8).
Theorem p230_ax_gate_reload M base a c top Q:
 ipeq Q p230_ax_gate_restore ->
 exists b d,program230_history M p230_instruction_formula b d
  (addM M(program230_transfer_time M c)(program230_transfer_time M a))
  (p230_ax_gate_state M base(program230_path_value M Q)(zeroM M)a(zeroM M)top(zeroM M)c) /\
 program230_state_at M b d(addM M(program230_transfer_time M c)(program230_transfer_time M a))
  (p230_ax_gate_state M base(program230_path_value M(p230_comparison_parent_path_1++[false]))
   (zeroM M)(zeroM M)a top c(zeroM M)).
Proof.
 intro HQ.
 set(start:=p230_ax_gate_state M base(program230_path_value M Q)(zeroM M)a(zeroM M)top(zeroM M)c).
 destruct(p230_transfer_record M p230_ax_gate_restore Q 7 6 4965 4966 start c
 ltac:(lia)ltac:(lia)ltac:(lia)p230_ax_gate_restore_site eq_refl HQ eq_refl)as[b[d[HR HT]]].
 assert(E1:program230_transfer_state 7 6 start(program230_path_value M(inc_path p230_ax_gate_restore))
 (zeroM M)(addM M(program230_register start 6)c)=
 p230_ax_gate_state M base(program230_path_value M p230_ax_gate_load)(zeroM M)a(zeroM M)top c(zeroM M)).
 {unfold start,p230_ax_gate_state;cbn[program230_transfer_state program230_config_of program230_field program230_register];
  rewrite coding_add_zero;reflexivity. }
 rewrite E1 in HT.
 set(mid:=p230_ax_gate_state M base(program230_path_value M p230_ax_gate_load)(zeroM M)a(zeroM M)top c(zeroM M))in *.
 destruct(p230_transfer_record M p230_ax_gate_load p230_ax_gate_load 4 5 4967 4968 mid a
 ltac:(lia)ltac:(lia)ltac:(lia)p230_ax_gate_load_site eq_refl(ipeq_refl _)eq_refl)as[e[f[HE HF]]].
 assert(E2:program230_transfer_state 4 5 mid(program230_path_value M(inc_path p230_ax_gate_load))
 (zeroM M)(addM M(program230_register mid 5)a)=
 p230_ax_gate_state M base(program230_path_value M(p230_comparison_parent_path_1++[false]))
 (zeroM M)(zeroM M)a top c(zeroM M)).
 {unfold mid,p230_ax_gate_state;cbn[program230_transfer_state program230_config_of program230_field program230_register];
  rewrite coding_add_zero;reflexivity. }
 rewrite E2 in HF.
 destruct(program230_history_join M p230_instruction_formula b d(program230_transfer_time M c)
 e f(program230_transfer_time M a)start mid HR HT HE)as[u[v[HU[HL Hright]]]].
 exists u,v;split;[exact HU|exact(proj1(Hright _ _(coding_lt_succ M _))HF)].
Qed.
Print Assumptions p230_ax_gate_reload.
