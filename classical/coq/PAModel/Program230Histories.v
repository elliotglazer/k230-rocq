(** Generic internal histories for a literal arithmetic step formula. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs Program230Configurations.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Unset Implicit Arguments.
Definition program230_transition_env {D}(z:D)(s t:program230_configuration D)(j:nat):D:=
 if Nat.ltb j 10 then program230_field s j else if Nat.ltb j 20 then program230_field t(j-10)else z.
Definition program230_step M(step:form)(s t:program230_configuration(carrier M)):=
 holds M(program230_transition_env(zeroM M)s t)step.
Definition program230_step_formula(step:form)(s t:program230_configuration term):form:=
 step[program230_transition_env zero s t].
Lemma program230_transition_eval M rho s t j:
 evalM M rho(program230_transition_env zero s t j)=
 program230_transition_env(zeroM M)(program230_eval_config M rho s)(program230_eval_config M rho t)j.
Proof.
 unfold program230_transition_env. destruct(Nat.ltb j 10)eqn:H10.
 -apply Nat.ltb_lt in H10. symmetry;now apply program230_eval_field.
 -destruct(Nat.ltb j 20)eqn:H20;[|reflexivity].
  apply Nat.ltb_ge in H10. apply Nat.ltb_lt in H20. symmetry;apply program230_eval_field;lia.
Qed.
Lemma program230_step_formula_correct M rho step s t:
 holds M rho(program230_step_formula step s t)<->
 program230_step M step(program230_eval_config M rho s)(program230_eval_config M rho t).
Proof.
 unfold program230_step_formula,program230_step,holds. rewrite sat_comp.
 split;intro H; eapply sat_ext;[|exact H| |exact H];intro j;
 first[exact(program230_transition_eval M rho s t j)|symmetry;exact(program230_transition_eval M rho s t j)].
Qed.
Definition program230_history M step b c N start:=
 program230_state_at M b c(zeroM M)start /\
 forall i s t,coding_lt M i N->program230_state_at M b c i s->
 program230_state_at M b c(succM M i)t->program230_step M step s t.
Fixpoint program230_lift n(t:term):term:=match n with 0=>t|S n=>(program230_lift n t)`[↑]end.
Lemma program230_eval_lift21 M rho x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 t:evalM M(x20.:x19.:x18.:x17.:x16.:x15.:x14.:x13.:x12.:x11.:x10.:x9.:x8.:x7.:x6.:x5.:x4.:x3.:x2.:x1.:x0.:rho)(program230_lift 21 t)=evalM M rho t.
Proof. unfold evalM;cbn[program230_lift];now rewrite !eval_up. Qed.
Definition program230_history_before:program230_configuration term:=program230_config_of(fun j=>$ (19-j)).
Definition program230_history_after:program230_configuration term:=program230_config_of(fun j=>$ (9-j)).
Definition program230_history_formula(step:form)(b c N:term)(start:program230_configuration term):form:=
 program230_state_at_formula b c zero start ∧∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀
 (Peano.sless $20(program230_lift 21 N)→
 program230_state_at_formula(program230_lift 21 b)(program230_lift 21 c)$20 program230_history_before→
 program230_state_at_formula(program230_lift 21 b)(program230_lift 21 c)(σ $20)program230_history_after→
 program230_step_formula step program230_history_before program230_history_after).
Local Opaque holds program230_state_at_formula program230_step_formula.
Lemma program230_history_formula_correct M rho step b c N start:
 holds M rho(program230_history_formula step b c N start)<->
 program230_history M step(evalM M rho b)(evalM M rho c)(evalM M rho N)(program230_eval_config M rho start).
Proof.
 unfold program230_history_formula,program230_history.
 rewrite holds_and,program230_state_at_formula_correct.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite program230_state_at_formula_correct. setoid_rewrite program230_step_formula_correct.
 setoid_rewrite less_formula_correct. setoid_rewrite program230_eval_lift21.
 cbn[program230_history_before program230_history_after program230_eval_config program230_config_of program230_field evalM].
 split;intros[H0 H];split;[exact H0| |exact H0|].
 -intros idx [pc a0 a1 a2 a3 a4 a5 a6 a7 a8][qc b0 b1 b2 b3 b4 b5 b6 b7 b8]Hi HS HT. exact(H idx pc a0 a1 a2 a3 a4 a5 a6 a7 a8 qc b0 b1 b2 b3 b4 b5 b6 b7 b8 Hi HS HT).
 -intros idx pc a0 a1 a2 a3 a4 a5 a6 a7 a8 qc b0 b1 b2 b3 b4 b5 b6 b7 b8 Hi HS HT. exact(H idx (mkProgram230Configuration(carrier M) pc a0 a1 a2 a3 a4 a5 a6 a7 a8)(mkProgram230Configuration(carrier M) qc b0 b1 b2 b3 b4 b5 b6 b7 b8)Hi HS HT).
Qed.
Print Assumptions program230_step_formula_correct.
Print Assumptions program230_history_formula_correct.
