(** Fourfold scaling accepts the actual padded PC of a preceding block. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230TransferStates
 Program230TransferLoop Program230TransferProgram Program230Scale4Loop Program230Scale4Program Program230TransferEntry Program230InstructionFormula Program230RootHistory.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Unset Implicit Arguments.
Lemma program230_scale4_time_positive M count:
 coding_lt M(zeroM M)(program230_scale4_time M count).
Proof.
 unfold program230_scale4_time;change(coding_lt M(zeroM M)
  (addM M(mulM M(code_numeral M 6)count)(succM M(zeroM M)))).
 rewrite <-(succ_as_add M(mulM M(code_numeral M 6)count));apply coding_zero_lt_succ.
Qed.
Theorem p230_scale4_padded_entry M P Q a b start count:
 (a<9)%nat->(b<9)%nat->a<>b->program230_scale4_leaves p230 P a b->
 program230_pc start=program230_path_value M Q->ipeq Q P->program230_register start a=count->
 exists u v final,program230_program_history M p230 u v(program230_scale4_time M count)start /\
 program230_state_at M u v(program230_scale4_time M count)final /\
 program230_pc final=program230_path_value M(inc_path P) /\
 program230_register final a=zeroM M /\
 program230_register final b=addM M(program230_register start b)(mulM M(code_numeral M 4)count) /\
 (forall i,(i<9)%nat->i<>a->i<>b->program230_register final i=program230_register start i).
Proof.
 intros Ha Hb Hab Hocc HP Heq Hcount.
 set(canonical:=program230_with_pc start(program230_path_value M P)).
 assert(Hac:program230_register canonical a=count)by(unfold canonical;now rewrite program230_with_pc_register).
 destruct(program230_scale4_program_history M p230 P a b canonical count Ha Hb Hab Hocc eq_refl Hac)
 as[u[v[final[HR[HT[Hpc[HA[HB HO]]]]]]]].
 apply(proj2(p230_instruction_history_correct M u v(program230_scale4_time M count)canonical))in HR.
 assert(Hnz:program230_scale4_time M count<>zeroM M).
 {intro E;pose proof(program230_scale4_time_positive M count)as Hlt;rewrite E in Hlt.
  destruct Hlt as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 destruct(p230_history_ipeq_endpoint M u v(program230_scale4_time M count)canonical P Q final
 eq_refl(ipeq_sym Q P Heq)HR Hnz HT)as[d[e[HD[HE _]]]].
 assert(EC:program230_with_pc canonical(program230_path_value M Q)=start).
 {unfold canonical;rewrite program230_with_pc_twice;now apply program230_with_pc_restore. }
 exists d,e,final;split;[apply p230_instruction_history_correct;now rewrite <-EC|].
 split;[exact HE|]. split;[exact Hpc|]. split;[exact HA|]. split.
 -rewrite HB;unfold canonical;now rewrite program230_with_pc_register.
 -intros i Hi Hia Hib;rewrite(HO i Hi Hia Hib);unfold canonical;apply program230_with_pc_register.
Qed.
Print Assumptions p230_scale4_padded_entry.
