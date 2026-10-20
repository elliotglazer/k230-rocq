(** Root-entry codes retain the finite number of zero path bits.
    Read/step transport uses ipeq; no normalization of the stored PC is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs CodeExpressions
 SentenceBounds Program230FormulaBounds Program230PathCode Program230Read Program230Walk
 Program230Walk40 Program230Height Program230Edges Program230Transition.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma program230_repeat_false_ipeq n:ipeq(repeat false n) (@nil bool) .
Proof.
 unfold ipeq,bit. assert(Hnil:forall i,nth i(@nil bool)false=false)by(intros[|i];reflexivity).
 intro i;rewrite Hnil;revert i;induction n as[|n IH];intros[|i];cbn;auto.
Qed.
Lemma program230_ipeq_nil_path P:ipeq P  (@nil bool) ->P=repeat false(length P).
Proof.
 induction P as[|b P IH];intro E;[reflexivity|].
 assert(Hb:b=false)by(exact(E 0));subst b;cbn[length repeat];f_equal.
 apply IH;intro i;specialize(E(S i));rewrite !bit_nil in E |- *;exact E.
Qed.
Lemma program230_take_zeros_ipeq n P Q:ipeq P Q->
 program230_take_zeros n P=program230_take_zeros n Q.
Proof.
 intro E;rewrite !program230_take_zeros_source_prefix,!pad_bits.
 apply map_ext;intro i;exact(E i).
Qed.

Definition program230_root_ready_upto M n pc:Prop:=
 exists j,(j<=n)%nat /\ pc=program230_path_value M(repeat false j).
Definition program230_root_ready M pc:=program230_root_ready_upto M 40 pc.
Fixpoint program230_root_ready_upto_formula n(pc:term):form:=
 match n with
 |0=>pc==program230_path_term  (@nil bool) 
 |S n=>(pc==program230_path_term(repeat false(S n))) ∨program230_root_ready_upto_formula n pc
 end.
Definition program230_root_ready_formula:=program230_root_ready_upto_formula 40.
Lemma program230_root_ready_upto_formula_correct M rho n pc:
 holds M rho(program230_root_ready_upto_formula n pc)<->
 program230_root_ready_upto M n(evalM M rho pc).
Proof.
 induction n as[|n IH].
 -change(evalM M rho pc=program230_path_value M (@nil bool) <->exists j,(j<=0)%nat /\evalM M rho pc=program230_path_value M(repeat false j)).
  split;[intro H;exists 0;auto|intros[j[Hj H]];assert(j=0)by lia;subst j;exact H].
 -cbn [program230_root_ready_upto_formula].
  rewrite holds_or,program230_holds_equal,program230_path_term_correct,IH.
  unfold program230_root_ready_upto;split.
  +intros[H|[j[Hj H]]];[exists(S n)|exists j];split;auto;lia.
  +intros[j[Hj H]];destruct(Nat.eq_dec j(S n))as[->|Hne];[now left|right;exists j;split;auto;lia].
Qed.
Theorem program230_root_ready_formula_correct M rho pc:
 holds M rho(program230_root_ready_formula pc)<->program230_root_ready M(evalM M rho pc).
Proof. apply program230_root_ready_upto_formula_correct. Qed.
Theorem program230_root_ready_boundb k pc:term_boundb k pc = true ->
 formula_boundb k(program230_root_ready_formula pc) = true.
Proof.
 intro H;unfold program230_root_ready_formula;generalize 40;intro n;induction n as[|n IH].
 -apply program230_equal_boundb;[exact H|apply program230_path_term_boundb].
 -apply program230_or_boundb;[apply program230_equal_boundb;[exact H|apply program230_path_term_boundb]|exact IH].
Qed.
Theorem program230_root_ready_definable M:Definable1 M(program230_root_ready M).
Proof.
 exists(program230_root_ready_formula $0),(fun _ => zeroM M).
 intro pc;symmetry;apply program230_root_ready_formula_correct.
Qed.
Theorem program230_root_ready_initial M:program230_root_ready M(code_numeral M 1).
Proof. exists 0;split;[lia|reflexivity]. Qed.
Theorem program230_root_ready_nonzero M pc:program230_root_ready M pc->pc<>zeroM M.
Proof. intros[j[Hj ->]];apply program230_path_nonzero. Qed.
Theorem program230_root_ready_of_zero_path M P:
 (length P<=40)%nat->ipeq P  (@nil bool) ->program230_root_ready M(program230_path_value M P).
Proof. intros HL E;exists(length P);split;[exact HL|exact(f_equal(program230_path_value M)(program230_ipeq_nil_path P E))]. Qed.

Lemma program230_walk_ipeq_transport M p P P' e Q rest:
 wf p->ipeq P P'->program230_walk M p(program230_path_value M P)e Q rest->
 exists rest',program230_walk M p(program230_path_value M P')e Q rest'.
Proof.
 intros W E H.
 destruct(program230_walk_source_exact M p P e Q rest W H)as[HW[HQ HR]].
 rewrite(walk_ipeq p(nnodes p+1)(root p)P P' 0 E)in HW.
 pose proof(program230_walk_source M p(nnodes p+1)P' e(length Q)HW)as H'.
 exists(program230_path_value M(skipn(length Q)P')).
 assert(EQ:Q=program230_take_zeros(length Q)P').
 {rewrite <- (program230_take_zeros_ipeq(length Q)P P' E),program230_take_zeros_source_prefix;exact HQ. }
 rewrite <- EQ in H';exact H'.
Qed.
Theorem program230_step_ipeq_transport M p P P' R T pc':
 wf p->ipeq P P'->
 (Program230Transition.program230_step M p(program230_path_value M P)R T pc'<->
  Program230Transition.program230_step M p(program230_path_value M P')R T pc').
Proof.
 intros W E;split;intros[e[Q[rest[HW HE]]]].
 -destruct(program230_walk_ipeq_transport M p P P' e Q rest W E HW)as[rest' H']. exists e,Q,rest';auto.
 -destruct(program230_walk_ipeq_transport M p P' P e Q rest W(ipeq_sym P P' E)HW)as[rest' H']. exists e,Q,rest';auto.
Qed.
Theorem program230_halt_ipeq_transport M p P P':
 wf p->ipeq P P'->
 (Program230Transition.program230_halt M p(program230_path_value M P)<->
  Program230Transition.program230_halt M p(program230_path_value M P')).
Proof.
 intros W E;split;intros[Q[rest HW]].
 -destruct(program230_walk_ipeq_transport M p P P' EHalt Q rest W E HW)as[rest' H'];exists Q,rest';exact H'.
 -destruct(program230_walk_ipeq_transport M p P' P EHalt Q rest W(ipeq_sym P P' E)HW)as[rest' H'];exists Q,rest';exact H'.
Qed.
Theorem program230_root_ready_step M pc R T pc':program230_root_ready M pc->
 (Program230Transition.program230_step M p230 pc R T pc'<->
  Program230Transition.program230_step M p230(code_numeral M 1)R T pc').
Proof.
 intros[n[Hn ->]]. apply(program230_step_ipeq_transport M p230(repeat false n) (@nil bool) R T pc' p230_wf).
 apply program230_repeat_false_ipeq.
Qed.
Theorem program230_root_ready_halt M pc:program230_root_ready M pc->
 (Program230Transition.program230_halt M p230 pc<->
  Program230Transition.program230_halt M p230(code_numeral M 1)).
Proof.
 intros[n[Hn ->]]. apply(program230_halt_ipeq_transport M p230(repeat false n) (@nil bool) p230_wf).
 apply program230_repeat_false_ipeq.
Qed.
Theorem program230_root_ready_first_leaf M pc:program230_root_ready M pc->
 exists rest,program230_walk M p230 pc(EDecnz 8)(repeat false 3)rest.
Proof.
 intros[n[Hn ->]].
 assert(HW:walk p230 40(root p230) (@nil bool) 0=Some(EDecnz 8,3))by reflexivity.
 pose proof(program230_numeric_walk_40_source M (@nil bool) (EDecnz 8)3 HW)as H.
 change(program230_walk M p230(program230_path_value M (@nil bool) )(EDecnz 8)(repeat false 3)(program230_path_value M (@nil bool) ))in H.
 eapply program230_walk_ipeq_transport;[exact p230_wf|apply ipeq_sym;apply program230_repeat_false_ipeq|exact H].
Qed.

Print Assumptions program230_root_ready_formula_correct.
Print Assumptions program230_root_ready_definable.
Print Assumptions program230_root_ready_of_zero_path.
Print Assumptions program230_root_ready_step.
Print Assumptions program230_root_ready_halt.
Print Assumptions program230_root_ready_first_leaf.
