(** A genuine history with different endpoint PCs has positive internal length. *)
From PAModel Require Import Model Arithmetic FiniteCoding Program230Configurations Program230Histories Program230TransferProgram.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Lemma program230_program_history_positive M p b c time start final:
 program230_program_history M p b c time start->program230_state_at M b c time final->
 program230_pc start<>program230_pc final->coding_lt M(zeroM M)time.
Proof.
 intros[Hstart Hstep]Hfinal Hneq.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)time)as[H0|[n Hn]].
 -subst time;pose proof(program230_state_at_functional M b c(zeroM M)start final Hstart Hfinal)as E.
  subst final;contradiction.
 -subst time;apply coding_zero_lt_succ.
Qed.
Print Assumptions program230_program_history_positive.
