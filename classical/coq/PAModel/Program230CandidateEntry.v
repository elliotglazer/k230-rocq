(** Candidate fetch at any bounded zero-padded root-entry PC. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootReady Program230RootHistory Program230TransferStates Program230Copy2States
 Program230RotatedRestore Program230CandidateFetch Program230PathCode.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_fetch_canonical M start:
 program230_register start 6=zeroM M ->
 p230_fetch_cfg M start(code_numeral M 1)(program230_register start 0)(program230_register start 8)=
 program230_with_pc start(code_numeral M 1).
Proof.
 intro H6;apply p230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
 change(program230_register(p230_fetch_cfg M start(code_numeral M 1)
  (program230_register start 0)(program230_register start 8))j=
  program230_register(program230_with_pc start(code_numeral M 1))j).
 rewrite program230_with_pc_register;unfold p230_fetch_cfg;rewrite program230_copy2_register by lia.
 destruct(Nat.eqb j 0)eqn:E0;[apply Nat.eqb_eq in E0;subst j;reflexivity|].
 destruct(Nat.eqb j 8)eqn:E8;[apply Nat.eqb_eq in E8;subst j;reflexivity|].
 destruct(Nat.eqb j 6)eqn:E6;[apply Nat.eqb_eq in E6;subst j;symmetry;exact H6|reflexivity].
Qed.
Lemma p230_fetch_time_nonzero M n:p230_fetch_time M n<>zeroM M.
Proof.
 unfold p230_fetch_time;change(addM M(mulM M(code_numeral M 7)n)(succM M(code_numeral M 3))<>zeroM M).
 rewrite (Arithmetic.add_comm M),(Arithmetic.add_succ M).
 intro E;apply(zero_ne_succ M(addM M(code_numeral M 3)(mulM M(code_numeral M 7)n)));symmetry;exact E.
Qed.
Theorem p230_candidate_fetch_zero_entry M start:
 program230_root_ready M(program230_pc start) ->
 program230_register start 6=zeroM M ->program230_register start 8=zeroM M ->
 exists b c,program230_history M p230_instruction_formula b c
  (p230_fetch_time M(program230_register start 0))start /\
 program230_state_at M b c(p230_fetch_time M(program230_register start 0))
  (p230_fetch_cfg M start(program230_path_value M p230_rotated_exit)
   (succM M(program230_register start 0))(program230_register start 0)).
Proof.
 intros Hready H6 H8.
 destruct(p230_candidate_fetch_zero M start(program230_register start 0))as[b[c[HR HT]]].
 pose proof(p230_fetch_canonical M start H6)as HC;rewrite H8 in HC;rewrite HC in HR.
 destruct(p230_history_root_ready_endpoint M b c(p230_fetch_time M(program230_register start 0))start
  (p230_fetch_cfg M start(program230_path_value M p230_rotated_exit)
   (succM M(program230_register start 0))(program230_register start 0))
  Hready HR(p230_fetch_time_nonzero M(program230_register start 0))HT)as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Theorem p230_candidate_fetch_positive_entry M start q:
 program230_root_ready M(program230_pc start) ->
 program230_register start 6=zeroM M ->program230_register start 8=succM M q ->
 exists b c,program230_history M p230_instruction_formula b c(code_numeral M 2)start /\
 program230_state_at M b c(code_numeral M 2)
  (p230_fetch_cfg M start(program230_path_value M([true]))(program230_register start 0)q).
Proof.
 intros Hready H6 H8.
 destruct(p230_candidate_fetch_positive M start(program230_register start 0)q)as[b[c[HR HT]]].
 pose proof(p230_fetch_canonical M start H6)as HC;rewrite H8 in HC;rewrite HC in HR.
 assert(Hnz:code_numeral M 2<>zeroM M)by(intro E;apply(zero_ne_succ M(code_numeral M 1));symmetry;exact E).
 destruct(p230_history_root_ready_endpoint M b c(code_numeral M 2)start
  (p230_fetch_cfg M start(program230_path_value M([true]))(program230_register start 0)q)
  Hready HR Hnz HT)as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Print Assumptions p230_candidate_fetch_zero_entry.
Print Assumptions p230_candidate_fetch_positive_entry.
