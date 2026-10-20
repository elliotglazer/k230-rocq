(** Exact field correspondence between the concrete counterprogram and the
    previously verified six-field numerical proof search. This file does not
    assert that a whole program iteration implements a search step. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 SearchStep KernelSafety Program230Configurations Program230InstructionFormula Program230HaltingSentence.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.

Definition p230_search_projection{D}(s:program230_configuration D):search_state D:=
 mkSearchState D(program230_r8 s)(program230_r0 s)(program230_r1 s)
  (program230_r2 s)(program230_r4 s)(program230_r5 s).
Definition p230_search_embedding{D}(z pc:D)(s:search_state D):program230_configuration D:=
 mkProgram230Configuration D pc(search_np s)(search_tw s)(search_ws s)z
  (search_d s)(search_h s)z z(search_pl s).
Definition p230_search_clean{D}(z:D)(s:program230_configuration D):Prop:=
 program230_r3 s=z /\program230_r6 s=z /\program230_r7 s=z.
Lemma p230_search_projection_embedding{D}(z pc:D)s:
 p230_search_projection(p230_search_embedding z pc s)=s.
Proof. destruct s;reflexivity. Qed.
Lemma p230_search_embedding_clean{D}(z pc:D)s:
 p230_search_clean z(p230_search_embedding z pc s).
Proof. repeat split;reflexivity. Qed.
Theorem p230_search_embedding_projection{D}(z:D)s:
 p230_search_clean z s->
 p230_search_embedding z(program230_pc s)(p230_search_projection s)=s.
Proof.
 destruct s;unfold p230_search_clean,p230_search_embedding,p230_search_projection;cbn.
 intros[H3[H6 H7]];rewrite H3,H6,H7;reflexivity.
Qed.
Theorem p230_initial_search_projection M:
 p230_search_projection(p230_initial_configuration M)=seed_state M.
Proof. reflexivity. Qed.
Theorem p230_initial_search_embedding M:
 p230_search_embedding(zeroM M)(code_numeral M 1)(seed_state M)=p230_initial_configuration M.
Proof. reflexivity. Qed.

Definition p230_eval_search M rho(s:search_state term):search_state(carrier M):=
 mkSearchState(carrier M)(evalM M rho(search_pl s))(evalM M rho(search_np s))
  (evalM M rho(search_tw s))(evalM M rho(search_ws s))
  (evalM M rho(search_d s))(evalM M rho(search_h s)).
Lemma p230_search_embedding_eval M rho pc s:
 program230_eval_config M rho(p230_search_embedding zero pc s)=
 p230_search_embedding(zeroM M)(evalM M rho pc)(p230_eval_search M rho s).
Proof. destruct s;reflexivity. Qed.
Definition p230_search_boundary_formula(pc:term)(state:program230_configuration term)(search:search_state term):form:=
 program230_fields_formula 10(fun j =>
  program230_field state j==program230_field(p230_search_embedding zero pc search)j).
Theorem p230_search_boundary_formula_correct M rho pc state search:
 holds M rho(p230_search_boundary_formula pc state search)<->
 program230_eval_config M rho state=
 p230_search_embedding(zeroM M)(evalM M rho pc)(p230_eval_search M rho search).
Proof.
 unfold p230_search_boundary_formula;rewrite program230_fields_formula_correct.
 rewrite <-p230_search_embedding_eval. split.
 -intro H;apply p230_configuration_ext;intros j Hj.
  rewrite !program230_eval_field by exact Hj. exact(H j Hj).
 -intros H j Hj.
  change(evalM M rho(program230_field state j)=
    evalM M rho(program230_field(p230_search_embedding zero pc search)j)).
  rewrite <-(program230_eval_field M rho state j Hj),
    <-(program230_eval_field M rho(p230_search_embedding zero pc search)j Hj).
  now rewrite H.
Qed.

Print Assumptions p230_search_embedding_projection.
Print Assumptions p230_initial_search_projection.
Print Assumptions p230_initial_search_embedding.
Print Assumptions p230_search_boundary_formula_correct.
