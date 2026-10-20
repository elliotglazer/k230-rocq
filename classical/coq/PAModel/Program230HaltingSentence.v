(** The complete seeded register-program halting sentence, using the actual
    instruction formula and internally coded ten-field histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathPop Program230Configurations Program230Histories Program230InstructionFormula
 Program230Transition Program230HaltingFormula.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.

Definition p230_initial_configuration M:program230_configuration(carrier M):=
 mkProgram230Configuration(carrier M)
  (code_numeral M 1)(code_numeral M 3)(zeroM M)(zeroM M)(zeroM M)
  (code_numeral M 3)(zeroM M)(zeroM M)(zeroM M)(zeroM M).
Definition p230_initial_terms:program230_configuration term:=
 mkProgram230Configuration term(num 1)(num 3)zero zero zero(num 3)zero zero zero zero.
Lemma p230_initial_terms_correct M rho:
 program230_eval_config M rho p230_initial_terms=p230_initial_configuration M.
Proof. reflexivity. Qed.

Definition p230_counter_halt_at M b c N:=
 exists last,program230_state_at M b c N last /\
  Program230Transition.program230_halt M p230(program230_pc last).
Definition p230_counter_halt_at_formula(b c N:term):form:=
 ∃(beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0 ∧
    p230_program_halt_formula $0).
Theorem p230_counter_halt_at_formula_correct M rho b c N:
 holds M rho(p230_counter_halt_at_formula b c N)<->
 p230_counter_halt_at M(evalM M rho b)(evalM M rho c)(evalM M rho N).
Proof.
 unfold p230_counter_halt_at_formula;rewrite holds_ex.
 assert(Hbody:forall pc,
  holds M(pc.:rho)(beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0 ∧
    p230_program_halt_formula $0)<->
  beta M(evalM M rho b)(evalM M rho c)(program230_field_index M(evalM M rho N)0)pc /\
    Program230Transition.program230_halt M p230 pc).
 {intro pc.
  rewrite(holds_and M(pc.:rho)
   (beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0)
   (p230_program_halt_formula $0)).
  rewrite beta_formula_correct,p230_program_halt_formula_correct,
    program230_field_index_correct,!pathpop_eval_up;reflexivity. }
 setoid_rewrite Hbody. unfold p230_counter_halt_at. split.
 -intros[pc[HB HH]].
  destruct(program230_state_at_total M(evalM M rho b)(evalM M rho c)(evalM M rho N))as[last HS].
  pose proof(HS 0 ltac:(lia))as HP.
  assert(E:pc=program230_pc last).
  {exact(beta_unique M(evalM M rho b)(evalM M rho c)
    (program230_field_index M(evalM M rho N)0)pc(program230_pc last)HB HP). }
  exists last;split;[exact HS|now rewrite <-E].
 -intros[last[HS HH]]. exists(program230_pc last);split;[exact(HS 0 ltac:(lia))|exact HH].
Qed.

Definition p230_counter_halting M:=exists b c N,
 program230_history M p230_instruction_formula b c N(p230_initial_configuration M) /\
 p230_counter_halt_at M b c N.
Definition p230_counter_halting_formula:form:=
 ∃∃∃(program230_history_formula p230_instruction_formula $2 $1 $0 p230_initial_terms ∧
  p230_counter_halt_at_formula $2 $1 $0).
Local Opaque program230_history_formula p230_counter_halt_at_formula.
Theorem p230_counter_halting_formula_correct M rho:
 holds M rho p230_counter_halting_formula<->p230_counter_halting M.
Proof.
 unfold p230_counter_halting_formula,p230_counter_halting.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct.
 setoid_rewrite p230_counter_halt_at_formula_correct.
 setoid_rewrite p230_initial_terms_correct. reflexivity.
Qed.
Definition p230_counter_nonhalting M:=~p230_counter_halting M.
Definition p230_counter_nonhalting_formula:form:=¬p230_counter_halting_formula.
Theorem p230_counter_nonhalting_formula_correct M rho:
 holds M rho p230_counter_nonhalting_formula<->p230_counter_nonhalting M.
Proof.
 unfold p230_counter_nonhalting_formula,p230_counter_nonhalting.
 change((holds M rho p230_counter_halting_formula->False)<->~p230_counter_halting M).
 now rewrite p230_counter_halting_formula_correct.
Qed.

Print Assumptions p230_counter_halt_at_formula_correct.
Print Assumptions p230_counter_halting_formula_correct.
Print Assumptions p230_counter_nonhalting_formula_correct.
