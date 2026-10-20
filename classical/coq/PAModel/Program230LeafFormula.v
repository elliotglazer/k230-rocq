(** A complete PA step formula from the actual finite program's leaf paths.
    The arithmetic read is valid on arbitrary PA-model inputs. The finite
    source enumeration selects control only, not a natural-number execution. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 NumericalProofs Program230PathCode Program230PathPop Program230Read
 Program230Walk Program230Edges Program230Transition.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230 Interpreter230Leaves.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma program230_subl_sound p f:
 (forall n Q e,In(Q,e)(leaves p f n)->fol p(ENode n)Q=Some e /\is_node e=false)->
 forall b a Q e,In(Q,e)(subl(fun n=>leaves p f n)b a)->
 exists T,Q=b::T /\fol p a T=Some e /\is_node e=false.
Proof.
 intros IH b a Q e H. destruct a as[n|r|r|k|k|];cbn[subl]in H.
 -apply in_map_iff in H as[[T out][HE HI]].
  destruct(IH n T out HI)as[HF HL]. cbn[fst snd]in HE.
  inversion HE;subst;exists T;auto.
 -destruct H as[HE|[]];inversion HE;subst;exists[];repeat split;reflexivity.
 -destruct H as[HE|[]];inversion HE;subst;exists[];repeat split;reflexivity.
 -destruct H as[HE|[]];inversion HE;subst;exists[];repeat split;reflexivity.
 -destruct H as[HE|[]];inversion HE;subst;exists[];repeat split;reflexivity.
 -destruct H as[HE|[]];inversion HE;subst;exists[];repeat split;reflexivity.
Qed.
Theorem program230_leaves_sound p f n Q e:
 In(Q,e)(leaves p f n)->fol p(ENode n)Q=Some e /\is_node e=false.
Proof.
 induction f as[|f IH]in n,Q,e|-*;intro H;[contradiction|].
 cbn[leaves]in H. apply in_app_or in H. destruct H as[H|H].
 -destruct(program230_subl_sound p f IH false(fst(nodes p n))Q e H)
   as[T[-> [HF HL]]]. split;[exact HF|exact HL].
 -destruct(program230_subl_sound p f IH true(snd(nodes p n))Q e H)
   as[T[-> [HF HL]]]. split;[exact HF|exact HL].
Qed.
Theorem program230_walk_leaf_member M p pc e Q rest:
 wf p->program230_walk M p pc e Q rest->
 In(Q,e)(leaves p(nnodes p+1)(root p)).
Proof.
 intros W[HR[HF HL]].
 pose proof(walk_leaf p W Q e Q HF HL(fun i => eq_refl))as HW.
 pose proof(leaves_root p Q e(length Q)HW)as HI.
 now rewrite(pad_eq Q Q(fun i => eq_refl))in HI.
Qed.

Definition program230_path_reached_formula Q pc:form:=
 ∃program230_read_formula pc`[↑] Q $0.
Lemma program230_path_reached_formula_correct M rho Q pc:
 holds M rho(program230_path_reached_formula Q pc)<->
 exists rest,program230_read M(evalM M rho pc)Q rest.
Proof.
 unfold program230_path_reached_formula;rewrite holds_ex.
 split;intros[x H];exists x.
 -apply program230_read_formula_correct in H;now rewrite pathpop_eval_up in H.
 -apply program230_read_formula_correct;now rewrite pathpop_eval_up.
Qed.
Definition program230_leaf_step_formula Q e pc before after pc':form:=
 program230_path_reached_formula Q pc ∧program230_edge_formula Q e before after pc'.
Lemma program230_leaf_step_formula_correct M rho Q e pc before after pc':
 holds M rho(program230_leaf_step_formula Q e pc before after pc')<->
 exists rest,program230_read M(evalM M rho pc)Q rest /\
  program230_edge_step M Q e(fun i => evalM M rho(before i))
    (fun i => evalM M rho(after i))(evalM M rho pc').
Proof.
 unfold program230_leaf_step_formula.
 rewrite holds_and,program230_path_reached_formula_correct,program230_edge_formula_correct.
 firstorder.
Qed.

Fixpoint program230_leaves_step_formula L pc before after pc':form:=
 match L with
 |[]=>⊥
 |(Q,e)::L=>program230_leaf_step_formula Q e pc before after pc' ∨
   program230_leaves_step_formula L pc before after pc'
 end.
Theorem program230_leaves_step_formula_correct M rho L pc before after pc':
 holds M rho(program230_leaves_step_formula L pc before after pc')<->
 exists Q e rest,In(Q,e)L /\program230_read M(evalM M rho pc)Q rest /\
  program230_edge_step M Q e(fun i => evalM M rho(before i))
    (fun i => evalM M rho(after i))(evalM M rho pc').
Proof.
 induction L as[|[P edge]L IH].
 -split;[contradiction|intros[Q[e[rest[H _]]]];contradiction].
 -cbn[program230_leaves_step_formula]. rewrite holds_or,program230_leaf_step_formula_correct,IH.
  split.
  +intros[[rest[HR HE]]|[Q[e[rest[HI[HR HE]]]]]].
   *exists P,edge,rest;split;[now left|auto].
   *exists Q,e,rest;split;[now right|auto].
  +intros[Q[e[rest[[HI|HI][HR HE]]]]].
   *inversion HI;subst;left;exists rest;auto.
   *right;exists Q,e,rest;auto.
Qed.

Definition program230_program_step_formula p pc before after pc':form:=
 program230_leaves_step_formula(leaves p(nnodes p+1)(root p))pc before after pc'.
Theorem program230_program_step_formula_correct M rho p pc before after pc':
 wf p->
 (holds M rho(program230_program_step_formula p pc before after pc')<->
  Program230Transition.program230_step M p(evalM M rho pc)
   (fun i => evalM M rho(before i))(fun i => evalM M rho(after i))(evalM M rho pc')).
Proof.
 intro W;unfold program230_program_step_formula,Program230Transition.program230_step.
 rewrite program230_leaves_step_formula_correct. split.
 -intros[Q[e[rest[HI[HR HE]]]]].
  destruct(program230_leaves_sound p(nnodes p+1)(root p)Q e HI)as[HF HL].
  exists e,Q,rest;split;[split;[exact HR|auto]|exact HE].
 -intros[e[Q[rest[HW HE]]]]. exists Q,e,rest.
  split;[exact(program230_walk_leaf_member M p(evalM M rho pc)e Q rest W HW)|].
  split;[exact(proj1 HW)|exact HE].
Qed.

Definition p230_program_step_formula:=program230_program_step_formula p230.
Corollary p230_program_step_formula_correct M rho pc before after pc':
 holds M rho(p230_program_step_formula pc before after pc')<->
 Program230Transition.program230_step M p230(evalM M rho pc)
  (fun i => evalM M rho(before i))(fun i => evalM M rho(after i))(evalM M rho pc').
Proof. apply program230_program_step_formula_correct;exact p230_wf. Qed.

Print Assumptions program230_leaves_sound.
Print Assumptions program230_walk_leaf_member.
Print Assumptions program230_leaves_step_formula_correct.
Print Assumptions program230_program_step_formula_correct.
Print Assumptions p230_program_step_formula_correct.
