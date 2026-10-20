(** The exact blank startup followed by any internal instruction history. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 Program230Configurations Program230Histories Program230InstructionFormula Program230HaltingSentence
 Program230Transition TM230BinaryStep TM230RunArithmetic TM230RunComposition TM230Paths
 TM230ExactPaths TM230MacroProgress TM230BootEncoding TM230SimulationState TM230HistorySimulation
 TM230HistorySimulationSyntax.
From K230 Require Prog230.
From Stdlib Require Import Arith.Arith Lia PArith setoid_ring.Ring.
Unset Implicit Arguments.
Section Seeded.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Add Ring seeded_simulation_ring:(model_semiring M).
Theorem machine230_seeded_instruction_history b c count:
 program230_history M p230_instruction_formula b c count(p230_initial_configuration M)->
 exists final t time slack,
 program230_state_at M b c count final /\machine230_reaches_in M time(machine230_seed M)t /\
 time=N(Pos.to_nat 408419)+count+slack /\
 machine230_simulation_state M(program230_pc final)(program230_register final)t.
Proof.
 intro HH. destruct(machine230_simulation_initial M)as[bb[bc[start[Hboot Hsim]]]].
 assert(Hstart:machine230_simulation_state M(program230_pc(p230_initial_configuration M))
  (program230_register(p230_initial_configuration M))start).
 {apply(proj1(machine230_simulation_registers_ext M(N 1)(machine230_initial_register M)
   (program230_register(p230_initial_configuration M))start
   ltac:(intros j Hj;do 9(destruct j;[reflexivity|]);lia))).
  exact Hsim. }
 destruct(machine230_simulates_internal_history M b c count(p230_initial_configuration M)start HH Hstart)
  as[final[t[time[slack[Hfinal[Hpath[Et Hlast]]]]]]].
 exists final,t,(N(Pos.to_nat 408419)+time),slack;split;[exact Hfinal|].
 split.
 -eapply machine230_reaches_in_join;[exists bb,bc;exact Hboot|exact Hpath].
 -split;[rewrite Et;ring|exact Hlast].
Qed.
Theorem p230_counter_halting_implies_machine230:
 p230_counter_halting M->machine230_arithmetical_halts M.
Proof.
 intros[b[c[count[HH[last[Hlast Hhalt]]]]]].
 destruct(machine230_seeded_instruction_history b c count HH)
  as[final[t[time[slack[Hfinal[Hpath[Et Hsim]]]]]]].
 assert(Efinal:final=last)by(eapply program230_state_at_functional;eassumption). subst final.
 destruct(machine230_simulation_halt M(program230_pc last)(program230_register last)t Hsim Hhalt)
  as[ending[Hend[tb[tc[ticks[Hpositive Htail]]]]]].
 destruct(machine230_reaches_in_join M time ticks(machine230_seed M)t ending Hpath
  (ex_intro _ tb(ex_intro _ tc Htail)))as[fb[fc[Hrun Hstate]]].
 exists fb,fc,(time+ticks);split;[exact Hrun|].
 pose proof(proj1 Hstate)as HB. now rewrite Hend in HB.
Qed.
End Seeded.

Print Assumptions machine230_seeded_instruction_history.
Print Assumptions p230_counter_halting_implies_machine230.
