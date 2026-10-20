(** Actual coded histories tolerate the finite zero padding of a root PC.
    Only row zero changes; every positive row keeps its original value. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs CodeExpressions
 Program230Configurations Program230Histories Program230HistoryInitialTransport
 Program230InstructionFormula Program230RootReady Program230PathCode.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Unset Implicit Arguments.

Definition program230_with_pc {D}(s:program230_configuration D)(pc:D):=
 mkProgram230Configuration D pc (program230_r0 s)(program230_r1 s)
  (program230_r2 s)(program230_r3 s)(program230_r4 s)(program230_r5 s)
  (program230_r6 s)(program230_r7 s)(program230_r8 s).
Lemma program230_with_pc_pc {D}(s:program230_configuration D) pc:
 program230_pc(program230_with_pc s pc)=pc.
Proof. reflexivity. Qed.
Lemma program230_with_pc_register {D}(s:program230_configuration D) pc i:
 program230_register(program230_with_pc s pc)i=program230_register s i.
Proof. destruct s;reflexivity. Qed.

Lemma p230_instruction_ipeq_initial M start P Q next:
 program230_pc start=program230_path_value M P -> ipeq P Q ->
 Program230Histories.program230_step M p230_instruction_formula start next ->
 Program230Histories.program230_step M p230_instruction_formula
  (program230_with_pc start(program230_path_value M Q))next.
Proof.
 intros HP E Hstep;apply p230_instruction_formula_correct.
 change(Program230Transition.program230_step M p230(program230_path_value M Q)
  (program230_register start)(program230_register next)(program230_pc next)).
 apply(proj1(program230_step_ipeq_transport M p230 P Q
  (program230_register start)(program230_register next)(program230_pc next)p230_wf E)).
 apply p230_instruction_formula_correct in Hstep;now rewrite <- HP.
Qed.

Theorem p230_history_ipeq_initial M b c N start P Q:
 program230_pc start=program230_path_value M P -> ipeq P Q ->
 program230_history M p230_instruction_formula b c N start ->
 exists f g,program230_history M p230_instruction_formula f g N
  (program230_with_pc start(program230_path_value M Q)) /\
 (forall i state,coding_lt M i(succM M N) -> i<>zeroM M ->
  (program230_state_at M b c i state <->program230_state_at M f g i state)).
Proof.
 intros HP E Hrun;apply(program230_history_change_initial M p230_instruction_formula
  b c N start(program230_with_pc start(program230_path_value M Q))Hrun).
 intros next H;exact(p230_instruction_ipeq_initial M start P Q next HP E H).
Qed.

Corollary p230_history_ipeq_endpoint M b c N start P Q last:
 program230_pc start=program230_path_value M P -> ipeq P Q ->
 program230_history M p230_instruction_formula b c N start -> N<>zeroM M ->
 program230_state_at M b c N last ->
 exists f g,program230_history M p230_instruction_formula f g N
  (program230_with_pc start(program230_path_value M Q)) /\
 program230_state_at M f g N last /\
 (forall i state,coding_lt M i(succM M N) -> i<>zeroM M ->
  (program230_state_at M b c i state <->program230_state_at M f g i state)).
Proof.
 intros HP E Hrun Hnz Hlast.
 apply(program230_history_change_initial_endpoint M p230_instruction_formula
  b c N start(program230_with_pc start(program230_path_value M Q))last Hrun Hnz Hlast).
 intros next H;exact(p230_instruction_ipeq_initial M start P Q next HP E H).
Qed.

Lemma p230_instruction_root_ready_initial M start next:
 program230_root_ready M(program230_pc start) ->
 Program230Histories.program230_step M p230_instruction_formula
  (program230_with_pc start(code_numeral M 1))next ->
 Program230Histories.program230_step M p230_instruction_formula start next.
Proof.
 intros HR Hstep;apply p230_instruction_formula_correct.
 apply(proj2(program230_root_ready_step M(program230_pc start)
  (program230_register start)(program230_register next)(program230_pc next)HR)).
 apply p230_instruction_formula_correct in Hstep;exact Hstep.
Qed.

Theorem p230_history_root_ready M b c N start:
 program230_root_ready M(program230_pc start) ->
 program230_history M p230_instruction_formula b c N
  (program230_with_pc start(code_numeral M 1)) ->
 exists f g,program230_history M p230_instruction_formula f g N start /\
 (forall i state,coding_lt M i(succM M N) -> i<>zeroM M ->
  (program230_state_at M b c i state <->program230_state_at M f g i state)).
Proof.
 intros HR Hrun;apply(program230_history_change_initial M p230_instruction_formula
  b c N(program230_with_pc start(code_numeral M 1))start Hrun).
 intros next H;exact(p230_instruction_root_ready_initial M start next HR H).
Qed.

Corollary p230_history_root_ready_endpoint M b c N start last:
 program230_root_ready M(program230_pc start) ->
 program230_history M p230_instruction_formula b c N
  (program230_with_pc start(code_numeral M 1)) -> N<>zeroM M ->
 program230_state_at M b c N last ->
 exists f g,program230_history M p230_instruction_formula f g N start /\
 program230_state_at M f g N last /\
 (forall i state,coding_lt M i(succM M N) -> i<>zeroM M ->
  (program230_state_at M b c i state <->program230_state_at M f g i state)).
Proof.
 intros HR Hrun Hnz Hlast.
 apply(program230_history_change_initial_endpoint M p230_instruction_formula
  b c N(program230_with_pc start(code_numeral M 1))start last Hrun Hnz Hlast).
 intros next H;exact(p230_instruction_root_ready_initial M start next HR H).
Qed.

Print Assumptions p230_history_ipeq_initial.
Print Assumptions p230_history_ipeq_endpoint.
Print Assumptions p230_history_root_ready.
Print Assumptions p230_history_root_ready_endpoint.
