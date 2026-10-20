(** The exact halt-leaf predicate as an ordinary arithmetic formula. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs Program230Read Program230Walk
 Program230Transition Program230LeafFormula.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230 Interpreter230Leaves.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition program230_leaf_halt_formula Q e pc:form:=
 match e with EHalt=>program230_path_reached_formula Q pc|_=>⊥end.
Lemma program230_leaf_halt_formula_correct M rho Q e pc:
 holds M rho(program230_leaf_halt_formula Q e pc)<->
 e=EHalt /\exists rest,program230_read M(evalM M rho pc)Q rest.
Proof.
 destruct e;cbn[program230_leaf_halt_formula];try(split;[contradiction|intros[H _];discriminate]).
 rewrite program230_path_reached_formula_correct;tauto.
Qed.
Fixpoint program230_leaves_halt_formula L pc:form:=
 match L with []=>⊥|(Q,e)::L=>program230_leaf_halt_formula Q e pc ∨program230_leaves_halt_formula L pc end.
Lemma program230_leaves_halt_formula_correct M rho L pc:
 holds M rho(program230_leaves_halt_formula L pc)<->
 exists Q rest,In(Q,EHalt)L /\program230_read M(evalM M rho pc)Q rest.
Proof.
 induction L as[|[P e]L IH].
 -split;[contradiction|intros[Q[rest[H _]]];contradiction].
 -cbn[program230_leaves_halt_formula].
  rewrite holds_or,program230_leaf_halt_formula_correct,IH. split.
  +intros[[He[rest HR]]|[Q[rest[HI HR]]]].
   *subst e;exists P,rest;split;[now left|exact HR].
   *exists Q,rest;split;[now right|exact HR].
  +intros[Q[rest[[HI|HI]HR]]].
   *inversion HI;subst;left;split;[reflexivity|eauto].
   *right;exists Q,rest;auto.
Qed.

Definition program230_program_halt_formula p pc:form:=
 program230_leaves_halt_formula(leaves p(nnodes p+1)(root p))pc.
Theorem program230_program_halt_formula_correct M rho p pc:
 wf p->
 (holds M rho(program230_program_halt_formula p pc)<->
  Program230Transition.program230_halt M p(evalM M rho pc)).
Proof.
 intro W;unfold program230_program_halt_formula,Program230Transition.program230_halt.
 rewrite program230_leaves_halt_formula_correct. split.
 -intros[Q[rest[HI HR]]].
  destruct(program230_leaves_sound p(nnodes p+1)(root p)Q EHalt HI)as[HF HL].
  exists Q,rest;split;[exact HR|auto].
 -intros[Q[rest HW]]. exists Q,rest;split.
  +exact(program230_walk_leaf_member M p(evalM M rho pc)EHalt Q rest W HW).
  +exact(proj1 HW).
Qed.
Definition p230_program_halt_formula:=program230_program_halt_formula p230.
Corollary p230_program_halt_formula_correct M rho pc:
 holds M rho(p230_program_halt_formula pc)<->
 Program230Transition.program230_halt M p230(evalM M rho pc).
Proof. apply program230_program_halt_formula_correct;exact p230_wf. Qed.
Print Assumptions program230_leaves_halt_formula_correct.
Print Assumptions program230_program_halt_formula_correct.
Print Assumptions p230_program_halt_formula_correct.
