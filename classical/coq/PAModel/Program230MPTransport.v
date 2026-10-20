(** Actual semantic-history transport for zero-padded MP entries. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230TransferProgram
 Program230InstructionFormula Program230RootHistory Program230TransferEntry Program230StackStates
 Program230ComparisonIteration Program230ComparisonControl.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_positive_history_entry M P Q start last b c time:
 program230_pc start=program230_path_value M P->ipeq P Q->
 program230_program_history M p230 b c time start->program230_state_at M b c time last->
 coding_lt M(zeroM M)time->exists u v,
 program230_program_history M p230 u v time(program230_with_pc start(program230_path_value M Q)) /\
 program230_state_at M u v time last.
Proof.
 intros HP Heq HR HT Hpos.
 apply(proj2(p230_instruction_history_correct M b c time start))in HR.
 assert(Hnz:time<>zeroM M).
 {intro E;rewrite E in Hpos;destruct Hpos as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 destruct(p230_history_ipeq_endpoint M b c time start P Q last HP Heq HR Hnz HT)
 as[u[v[HU[HV _]]]].
 exists u,v;split;[apply p230_instruction_history_correct;exact HU|exact HV].
Qed.
Lemma program230_stack_with_pc {D}(base:program230_configuration D)pc pc' tw ws a b:
 program230_with_pc(program230_stack_state base pc tw ws a b)pc'=
 program230_stack_state base pc' tw ws a b.
Proof. destruct base;reflexivity. Qed.
Lemma p230_mp_comparison_start M base pc tw ws value:
 program230_stack_state base pc tw ws value(zeroM M)=
 program230_comparison_state(program230_stack_state base pc tw ws(zeroM M)(zeroM M))
 pc value(program230_register base 5).
Proof. destruct base;reflexivity. Qed.
Lemma p230_mp_comparison_end M base oldpc pc ws:
 program230_comparison_state(program230_stack_state base oldpc(zeroM M)ws(zeroM M)(zeroM M))pc(zeroM M)(zeroM M)=
 program230_stack_state(program230_comparison_state base pc(zeroM M)(zeroM M))pc(zeroM M)ws(zeroM M)(zeroM M).
Proof. destruct base;reflexivity. Qed.
Print Assumptions p230_positive_history_entry.
Print Assumptions p230_mp_comparison_start.
