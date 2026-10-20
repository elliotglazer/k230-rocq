(** Exact top-register reset from the ordinary padded entry. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230InstructionFormula Program230PathCode
 Program230TransferStates Program230TransferProgram Program230ResetLoop Program230RootHistory.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_top_state{D}(base:program230_configuration D)pc top:=
 program230_transfer_state 1 1 base pc top top.
Lemma p230_top_reset_padded M P n base top:
 program230_reset_occurrence p230 P 1 n ->
 exists b c,program230_history M p230_instruction_formula b c(program230_reset_time M top)
  (p230_top_state base(program230_path_value M(P++[false]))top) /\
 program230_state_at M b c(program230_reset_time M top)
  (p230_top_state base(program230_path_value M(inc_path P))(zeroM M)).
Proof.
 intro HO;set(start:=p230_top_state base(program230_path_value M P)top).
 assert(HT:program230_register start 1=top)by(unfold start,p230_top_state;apply program230_transfer_source;lia).
 destruct(program230_reset_program_history M p230 P 1 n start top ltac:(lia)HO eq_refl HT)
 as[b[c[final[HR[HE[Hpc[Htop HF]]]]]]].
 assert(EF:final=p230_top_state base(program230_path_value M(inc_path P))(zeroM M)).
 {apply p230_configuration_ext;intros j Hj;destruct j as[|j];[exact Hpc|].
  change(program230_register final j=program230_register
   (p230_top_state base(program230_path_value M(inc_path P))(zeroM M))j).
  unfold p230_top_state;rewrite program230_transfer_register by lia.
  destruct(Nat.eqb j 1)eqn:E;[apply Nat.eqb_eq in E;subst j;exact Htop|].
  apply Nat.eqb_neq in E;rewrite(HF j ltac:(lia)E);unfold start,p230_top_state.
  rewrite program230_transfer_register by lia;now rewrite(proj2(Nat.eqb_neq j 1)E). }
 rewrite EF in HE;apply(proj2(p230_instruction_history_correct M b c _ start))in HR.
 assert(Hnz:program230_reset_time M top<>zeroM M).
 {unfold program230_reset_time;change(addM M(mulM M(code_numeral M 2)top)(succM M(zeroM M))<>zeroM M).
  rewrite <-(succ_as_add M(mulM M(code_numeral M 2)top));intro E.
  exact(zero_ne_succ M(mulM M(code_numeral M 2)top)(eq_sym E)). }
 destruct(p230_history_ipeq_endpoint M b c(program230_reset_time M top)start P(P++[false])
  _ eq_refl(ipeq_sym _ _(ipeq_app_false P))HR Hnz HE)as[d[e[HD[HF' _]]]].
 exists d,e;split;[exact HD|exact HF'].
Qed.
Print Assumptions p230_top_reset_padded.
