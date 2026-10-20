(** Genuine PA-definable induction constructs arbitrarily long internal
    executions when the actual seeded counterprogram does not halt. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathPop Program230Configurations Program230Histories Program230HistoryConstructors
 Program230InstructionFormula Program230HaltingSentence Program230Transition Program230RegisterExtensional.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Unset Implicit Arguments.

Theorem p230_instruction_progress M s:
 program230_pc s<>zeroM M->
 Program230Transition.program230_halt M p230(program230_pc s) \/
 exists t,Program230Histories.program230_step M p230_instruction_formula s t.
Proof.
 intro Hnz.
 destruct(Program230Transition.program230_p230_progress M(program230_pc s)(program230_register s)Hnz)
  as[HH|[T[pc' HS]]];[now left|].
 right.
 set(t:=mkProgram230Configuration(carrier M) pc'(T 0)(T 1)(T 2)(T 3)(T 4)(T 5)(T 6)(T 7)(T 8)).
 assert(HT:forall i,(i<9)%nat->T i = program230_register t i).
 {intros i Hi;do 9(destruct i;[reflexivity|]);lia. }
 exists t;apply p230_instruction_formula_correct.
 change(Program230Transition.program230_step M p230(program230_pc s)(program230_register s)(program230_register t)pc').
 apply(proj1(program230_step_register_extensional M p230(program230_pc s)
   (program230_register s)T(program230_register s)(program230_register t)pc'
   (fun i Hi=>eq_refl)HT));exact HS.
Qed.

Definition p230_positive_at M b c N:=exists last,
 program230_state_at M b c N last /\program230_pc last<>zeroM M.
Definition p230_positive_at_formula(b c N:term):form:=
 ∃(beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0 ∧¬($0==zero)).
Theorem p230_positive_at_formula_correct M rho b c N:
 holds M rho(p230_positive_at_formula b c N)<->
 p230_positive_at M(evalM M rho b)(evalM M rho c)(evalM M rho N).
Proof.
 unfold p230_positive_at_formula;rewrite holds_ex.
 assert(Hbody:forall pc,
  holds M(pc.:rho)(beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0 ∧¬($0==zero))<->
  beta M(evalM M rho b)(evalM M rho c)(program230_field_index M(evalM M rho N)0)pc /\pc<>zeroM M).
 {intro pc. rewrite holds_and,beta_formula_correct,program230_field_index_correct,!pathpop_eval_up.
  reflexivity. }
 setoid_rewrite Hbody. unfold p230_positive_at. split.
 -intros[pc[HB Hpc]].
  destruct(program230_state_at_total M(evalM M rho b)(evalM M rho c)(evalM M rho N))as[last HS].
  assert(E:pc=program230_pc last).
  {exact(beta_unique M(evalM M rho b)(evalM M rho c)
    (program230_field_index M(evalM M rho N)0)pc(program230_pc last)HB(HS 0 ltac:(lia))). }
  exists last;split;[exact HS|now rewrite <-E].
 -intros[last[HS Hpc]]. exists(program230_pc last);split;[exact(HS 0 ltac:(lia))|exact Hpc].
Qed.

Definition p230_prefix_exists M N:=exists b c,
 program230_history M p230_instruction_formula b c N(p230_initial_configuration M) /\
 p230_positive_at M b c N.
Definition p230_prefix_exists_formula(N:term):form:=
 ∃∃(program230_history_formula p230_instruction_formula $1 $0 N`[↑]`[↑] p230_initial_terms ∧
  p230_positive_at_formula $1 $0 N`[↑]`[↑]).
Local Opaque program230_history_formula p230_positive_at_formula.
Theorem p230_prefix_exists_formula_correct M rho N:
 holds M rho(p230_prefix_exists_formula N)<->p230_prefix_exists M(evalM M rho N).
Proof.
 unfold p230_prefix_exists_formula,p230_prefix_exists.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct.
 setoid_rewrite p230_positive_at_formula_correct.
 setoid_rewrite p230_initial_terms_correct.
 repeat setoid_rewrite pathpop_eval_up. reflexivity.
Qed.
Lemma p230_prefix_exists_definable M:Definable1 M(p230_prefix_exists M).
Proof.
 exists(p230_prefix_exists_formula $0),(fun _=>zeroM M).
 intro N;symmetry;apply p230_prefix_exists_formula_correct.
Qed.

Theorem p230_counter_nonhalting_long_prefixes M:
 p230_counter_nonhalting M->forall N,p230_prefix_exists M N.
Proof.
 intro Hno. apply(definable_induction M(p230_prefix_exists M)(p230_prefix_exists_definable M)).
 -destruct(program230_history_zero M p230_instruction_formula(p230_initial_configuration M))as[b[c[HR HS]]].
  exists b,c;split;[exact HR|exists(p230_initial_configuration M);split;[exact HS|]].
  intro H;apply(zero_ne_succ M(zeroM M));now symmetry.
 -intros N[b[c[HR[last[HS Hpc]]]]].
  destruct(p230_instruction_progress M last Hpc)as[HH|[next Hstep]].
  +exfalso;apply Hno;exists b,c,N;split;[exact HR|exists last;auto].
  +destruct(program230_history_extend M p230_instruction_formula b c N
    (p230_initial_configuration M)last next HR HS Hstep)as[d[e[HT[HSnext HP]]]].
   exists d,e;split;[exact HT|exists next;split;[exact HSnext|]].
   exact(p230_instruction_preserves_positive_PC M last next Hstep).
Qed.

Print Assumptions p230_instruction_progress.
Print Assumptions p230_prefix_exists_formula_correct.
Print Assumptions p230_prefix_exists_definable.
Print Assumptions p230_counter_nonhalting_long_prefixes.
