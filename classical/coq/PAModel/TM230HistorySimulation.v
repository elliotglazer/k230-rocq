(** Genuine PA induction on the internally coded program-history length.
    Positive machine progress at every source step retains time >= index. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 Program230Configurations Program230Histories Program230Transition Program230InstructionFormula
 TM230BinaryStep TM230MacroProgress TM230ExactPaths TM230SimulationState TM230HistorySimulationSyntax.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
Section Uniform.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Infix "+":=(addM M).
Add Ring history_simulation_ring:(model_semiring M).
Theorem machine230_simulates_internal_history b c N first start:
 program230_history M p230_instruction_formula b c N first ->
 machine230_simulation_state M(program230_pc first)(program230_register first)start ->
 machine230_history_simulation_at M b c start N.
Proof.
 intros[H0 Hstep]Hstart.
 assert(Hall:forall idx,machine230_history_progress M b c N start idx).
 {apply(definable_induction M(machine230_history_progress M b c N start)
   (machine230_history_progress_definable M b c N start)).
  -intros Hbound. exists first,start,Z,Z;split;[exact H0|].
   split;[apply machine230_reaches_in_zero|]. split;[now rewrite Arithmetic.add_zero|exact Hstart].
  -intros idx IH Hbound.
   pose proof(proj1(coding_lt_succ_cancel M idx N)Hbound)as Hidx.
   assert(Hold:coding_lt M idx(S N))by(eapply coding_lt_trans;[exact Hidx|apply coding_lt_succ]).
   destruct(IH Hold)as[old[mid[time[slack[HoldState[Hrun[Htime Hsim]]]]]]].
   destruct(program230_state_at_total M b c(S idx))as[next Hnext].
   pose proof(Hstep idx old next Hidx HoldState Hnext)as Hsource.
   apply p230_instruction_formula_correct in Hsource.
   destruct(machine230_simulation_step M(program230_pc old)(program230_register old)
    (program230_register next)(program230_pc next)mid Hsim Hsource)as[last[Hprogress Hlast]].
   destruct Hprogress as[tb[tc[ticks[Hpositive Hpath]]]].
   destruct Hpositive as[k Ek]. rewrite coding_add_zero in Ek.
   exists next,last,(time+ticks),(slack+k);split;[exact Hnext|].
   split.
   +eapply machine230_reaches_in_join;[exact Hrun|exists tb,tc;exact Hpath].
   +split;[|exact Hlast]. rewrite Htime,Ek,(succ_as_add M k),(succ_as_add M idx);ring.
 }
 exact(Hall N(coding_lt_succ M N)).
Qed.
End Uniform.
Print Assumptions machine230_simulates_internal_history.
