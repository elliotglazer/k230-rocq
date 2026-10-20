(** Pair construction accepts the exact padded PC returned by a prior block. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230Histories Program230TransferStates Program230Copy2States
 Program230TransferProgram Program230InstructionFormula Program230RootHistory Program230TransferEntry
 Program230PairConstructorIteration Program230PairShape Program230PairShapeBody.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Unset Implicit Arguments.
Theorem p230_pair_padded_entry M P Q start value:
 program230_pair_shape P->program230_pc start=program230_path_value M Q->ipeq Q P->
 pair_graph M(program230_register start 6)(program230_register start 1)value->
 exists u v time,program230_program_history M p230 u v time start /\
 program230_state_at M u v time
 (program230_pair_state start(program230_path_value M((inc_path P)++(false::nil)))
 (zeroM M)(zeroM M)(addM M(program230_register start 7)value)) /\coding_lt M(zeroM M)time.
Proof.
 intros HS HP Heq Hpair.
 destruct(program230_pair_shape_history M P HS start(program230_register start 6)(program230_register start 1)
 (program230_register start 7)value Hpair)as[u[v[time[HR[HT Hpos]]]]].
 set(canonical:=program230_with_pc start(program230_path_value M P)).
 assert(E:program230_pair_state start(program230_path_value M P)(program230_register start 6)
 (program230_register start 1)(program230_register start 7)=canonical).
 {apply program230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
  change(program230_register(program230_pair_state start(program230_path_value M P)(program230_register start 6)
    (program230_register start 1)(program230_register start 7))j=program230_register canonical j).
  unfold program230_pair_state,canonical;rewrite program230_with_pc_register,program230_copy2_register by lia.
  destruct(Nat.eqb j 6)eqn:H6;[apply Nat.eqb_eq in H6;now subst j|].
  destruct(Nat.eqb j 1)eqn:H1;[apply Nat.eqb_eq in H1;now subst j|].
  destruct(Nat.eqb j 7)eqn:H7;[apply Nat.eqb_eq in H7;now subst j|reflexivity]. }
 rewrite E in HR;apply(proj2(p230_instruction_history_correct M u v time canonical))in HR.
 assert(Hnz:time<>zeroM M).
 {intro Et;rewrite Et in Hpos;destruct Hpos as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 destruct(p230_history_ipeq_endpoint M u v time canonical P Q _ eq_refl(ipeq_sym Q P Heq)HR Hnz HT)
 as[a[b[HA[HB _]]]].
 assert(EC:program230_with_pc canonical(program230_path_value M Q)=start).
 {unfold canonical;rewrite program230_with_pc_twice;now apply program230_with_pc_restore. }
 exists a,b,time;split;[apply p230_instruction_history_correct;now rewrite <-EC|].
 exact(conj HB Hpos).
Qed.
Print Assumptions p230_pair_padded_entry.
