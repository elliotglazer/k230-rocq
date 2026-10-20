(** Exact record endpoints for checked internal register loops. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230TransferStates Program230TransferProgram Program230TransferLoop Program230TransferEntry
 Program230Copy2States Program230Copy2Program Program230Copy2Loop.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Unset Implicit Arguments.

Lemma p230_transfer_record M P Q a b n m start count:
 (a<9)%nat->(b<9)%nat->a<>b->program230_transfer_occurrence p230 P a b n m->
 program230_pc start=program230_path_value M Q->ipeq Q P->program230_register start a=count->
 exists u v,program230_history M p230_instruction_formula u v(program230_transfer_time M count)start /\
 program230_state_at M u v(program230_transfer_time M count)
 (program230_transfer_state a b start(program230_path_value M(inc_path P))(zeroM M)
   (addM M(program230_register start b)count)).
Proof.
 intros Ha Hb Hab HO HP HE HC.
 destruct(p230_transfer_padded_entry M P Q a b n m start count Ha Hb Hab HO HP HE HC)
 as[u[v[final[HR[HT[Hpc[HA[HB HF]]]]]]]].
 assert(E:final=program230_transfer_state a b start(program230_path_value M(inc_path P))
 (zeroM M)(addM M(program230_register start b)count)).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[exact Hpc|].
  change(program230_register final j=program230_register
   (program230_transfer_state a b start(program230_path_value M(inc_path P))(zeroM M)
   (addM M(program230_register start b)count))j).
  rewrite program230_transfer_register by lia.
  destruct(Nat.eqb j a)eqn:EA;[apply Nat.eqb_eq in EA;now subst j|].
  destruct(Nat.eqb j b)eqn:EB;[apply Nat.eqb_eq in EB;now subst j|].
  apply Nat.eqb_neq in EA;apply Nat.eqb_neq in EB;apply HF;lia. }
 exists u,v;split;[apply(proj2(p230_instruction_history_correct M u v _ start));exact HR|now rewrite <-E].
Qed.

Lemma p230_copy2_record M P a b c n m k start count:
 (a<9)%nat->(b<9)%nat->(c<9)%nat->a<>b->a<>c->b<>c->
 program230_copy2_occurrence p230 P a b c n m k->
 program230_pc start=program230_path_value M P->program230_register start a=count->
 exists u v,program230_history M p230_instruction_formula u v(program230_copy2_time M count)start /\
 program230_state_at M u v(program230_copy2_time M count)
 (program230_copy2_state a b c start(program230_path_value M(inc_path P))(zeroM M)
   (addM M(program230_register start b)count)(addM M(program230_register start c)count)).
Proof.
 intros Ha Hb Hc Hab Hac Hbc HO HP HC.
 destruct(program230_copy2_program_history M p230 P a b c n m k start count Ha Hb Hc Hab Hac Hbc HO HP HC)
 as[u[v[final[HR[HT[Hpc[HA[HB[HC' HF]]]]]]]]].
 assert(E:final=program230_copy2_state a b c start(program230_path_value M(inc_path P))(zeroM M)
   (addM M(program230_register start b)count)(addM M(program230_register start c)count)).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[exact Hpc|].
  change(program230_register final j=program230_register
   (program230_copy2_state a b c start(program230_path_value M(inc_path P))(zeroM M)
   (addM M(program230_register start b)count)(addM M(program230_register start c)count))j).
  rewrite program230_copy2_register by lia.
  destruct(Nat.eqb j a)eqn:EA;[apply Nat.eqb_eq in EA;now subst j|].
  destruct(Nat.eqb j b)eqn:EB;[apply Nat.eqb_eq in EB;now subst j|].
  destruct(Nat.eqb j c)eqn:EC;[apply Nat.eqb_eq in EC;now subst j|].
  apply Nat.eqb_neq in EA;apply Nat.eqb_neq in EB;apply Nat.eqb_neq in EC;apply HF;lia. }
 exists u,v;split;[apply(proj2(p230_instruction_history_correct M u v _ start));exact HR|now rewrite <-E].
Qed.
Print Assumptions p230_transfer_record.
Print Assumptions p230_copy2_record.
