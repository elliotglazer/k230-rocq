(** The exact public program step in the canonical twenty-field environment
    used by the internally coded counterprogram histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230LeafFormula Program230Transition Program230RegisterExtensional
 Program230Configurations Program230Histories.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Unset Implicit Arguments.

Definition p230_instruction_formula:form:=
 p230_program_step_formula $0(fun i => $(S i))(fun i => $(11+i))$10.

Lemma p230_transition_env_before M s t j:
 (j<10)%nat->
 evalM M(program230_transition_env(zeroM M)s t)($j)=program230_field s j.
Proof.
 intro H;change(program230_transition_env(zeroM M)s t j=program230_field s j).
 unfold program230_transition_env.
 destruct(Nat.ltb j 10)eqn:E;[reflexivity|apply Nat.ltb_ge in E;lia].
Qed.
Lemma p230_transition_env_after M s t j:
 (j<10)%nat->
 evalM M(program230_transition_env(zeroM M)s t)($(10+j))=program230_field t j.
Proof.
 intro H;change(program230_transition_env(zeroM M)s t(10+j)=program230_field t j).
 unfold program230_transition_env.
 destruct(Nat.ltb(10+j)10)eqn:E10;[apply Nat.ltb_lt in E10;lia|].
 destruct(Nat.ltb(10+j)20)eqn:E20;[|apply Nat.ltb_ge in E20;lia].
 replace(10+j-10)%nat with j by lia;reflexivity.
Qed.

Theorem p230_instruction_formula_correct M s t:
 Program230Histories.program230_step M p230_instruction_formula s t <->
 Program230Transition.program230_step M p230(program230_pc s)
  (program230_register s)(program230_register t)(program230_pc t).
Proof.
 unfold Program230Histories.program230_step,p230_instruction_formula.
 rewrite p230_program_step_formula_correct.
 change(Program230Transition.program230_step M p230(program230_pc s)
  (fun i => evalM M(program230_transition_env(zeroM M)s t)($(S i)))
  (fun i => evalM M(program230_transition_env(zeroM M)s t)($(11+i)))
  (program230_pc t)<->
 Program230Transition.program230_step M p230(program230_pc s)
  (program230_register s)(program230_register t)(program230_pc t)).
 apply program230_step_register_extensional.
 -intros i Hi;unfold program230_register;apply p230_transition_env_before;lia.
 -intros i Hi;unfold program230_register.
  replace(11+i)%nat with(10+S i)%nat by lia;apply p230_transition_env_after;lia.
Qed.

Theorem p230_instruction_history_correct M b c N start:
 program230_history M p230_instruction_formula b c N start <->
 program230_state_at M b c(zeroM M)start /\
 forall i s t,coding_lt M i N->program230_state_at M b c i s->
 program230_state_at M b c(succM M i)t->
 Program230Transition.program230_step M p230(program230_pc s)
  (program230_register s)(program230_register t)(program230_pc t).
Proof.
 unfold program230_history. split;intros[H0 H];split;[exact H0| |exact H0|].
 -intros i s t Hi HS HT;apply p230_instruction_formula_correct;exact(H i s t Hi HS HT).
 -intros i s t Hi HS HT;apply p230_instruction_formula_correct;exact(H i s t Hi HS HT).
Qed.

Lemma p230_configuration_ext{D}(s t:program230_configuration D):
 (forall j,(j<10)%nat->program230_field s j=program230_field t j)->s=t.
Proof.
 intro H;destruct s,t;f_equal.
 -exact(H 0 ltac:(lia)).
 -exact(H 1 ltac:(lia)).
 -exact(H 2 ltac:(lia)).
 -exact(H 3 ltac:(lia)).
 -exact(H 4 ltac:(lia)).
 -exact(H 5 ltac:(lia)).
 -exact(H 6 ltac:(lia)).
 -exact(H 7 ltac:(lia)).
 -exact(H 8 ltac:(lia)).
 -exact(H 9 ltac:(lia)).
Qed.
Theorem p230_instruction_deterministic M s t u:
 Program230Histories.program230_step M p230_instruction_formula s t->
 Program230Histories.program230_step M p230_instruction_formula s u->t=u.
Proof.
 rewrite !p230_instruction_formula_correct;intros HT HU.
 destruct(Program230Transition.program230_step_deterministic M p230
  (program230_pc s)(program230_register s)(program230_register t)
  (program230_register u)(program230_pc t)(program230_pc u)HT HU)as[Hpc HR].
 apply p230_configuration_ext;intros j Hj;destruct j as[|j];[exact Hpc|apply HR;lia].
Qed.
Theorem p230_instruction_preserves_positive_PC M s t:
 Program230Histories.program230_step M p230_instruction_formula s t->
 program230_pc t<>zeroM M.
Proof.
 rewrite p230_instruction_formula_correct;apply Program230Transition.program230_step_target_nonzero.
Qed.

Print Assumptions p230_instruction_formula_correct.
Print Assumptions p230_instruction_history_correct.
Print Assumptions p230_instruction_deterministic.
Print Assumptions p230_instruction_preserves_positive_PC.
