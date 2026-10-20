(** The actual register program's uniform one-step relation. The PC and all
    register values range over an arbitrary PA model. Internal iteration is
    handled separately by a PA-definable history, not by external induction. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 NumericalProofs TM230LiteralActions TM230BitArithmetic Program230PathCode
 Program230PathPop Program230Read Program230Walk Program230Edges Program230Bounds Program230Clean.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition program230_step M p pc(R T:nat->carrier M)pc':Prop:=
 exists e Q rest,program230_walk M p pc e Q rest /\
  program230_edge_step M Q e R T pc'.
Definition program230_halt M p pc:Prop:=
 exists Q rest,program230_walk M p pc EHalt Q rest.
Definition program230_updated M(R:nat->carrier M)r value:nat->carrier M:=
 fun i => if Nat.eqb i r then value else R i.
Lemma program230_updated_correct M R r value:
 program230_register_update M r value R(program230_updated M R r value).
Proof. intros i Hi;reflexivity. Qed.
Lemma program230_same_refl M R:program230_register_same M R R.
Proof. intros i Hi;reflexivity. Qed.

Lemma program230_edge_progress M Q e R:
 program230_edge_register_supported e->is_node e=false->
 e=EHalt \/exists T pc',program230_edge_step M Q e R T pc'.
Proof.
 destruct e as[n|r|r|k|k|];cbn[program230_edge_register_supported is_node];intros HS HL.
 -discriminate.
 -right;exists(program230_updated M R r(succM M(R r))),
   (program230_path_value M(inc_path Q)).
  split;[exact HS|split;[reflexivity|apply program230_updated_correct]].
 -right. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)(R r))as[H0|[v Hv]].
  +exists R,(program230_path_value M(brk 1 Q)).
   split;[exact HS|left;split;[exact H0|split;[reflexivity|apply program230_same_refl]]].
  +exists(program230_updated M R r v),(program230_path_value M(inc_path Q)).
   split;[exact HS|right;exists v;split;[exact Hv|split;[reflexivity|apply program230_updated_correct]]].
 -right;exists R,(program230_path_value M(brk k Q));split;[reflexivity|apply program230_same_refl].
 -right;exists R,(program230_path_value M(cont k Q));split;[reflexivity|apply program230_same_refl].
 -left;reflexivity.
Qed.

Theorem program230_step_deterministic M p pc R T U pc' pc'':
 program230_step M p pc R T pc'->program230_step M p pc R U pc''->
 pc'=pc'' /\forall i,(i<9)%nat->T i = U i.
Proof.
 intros[e[Q[rest[HW HE]]]][e'[Q'[rest'[KW KE]]]].
 destruct(program230_walk_deterministic M p pc e Q rest e' Q' rest' HW KW)as[HQ[He Hr]].
 subst e' Q' rest'. exact(program230_edge_deterministic M Q e R T U pc' pc'' HE KE).
Qed.
Theorem program230_step_target_nonzero M p pc R T pc':
 program230_step M p pc R T pc'->pc'<>zeroM M.
Proof.
 intros[e[Q[rest[HW HE]]]]. destruct e;cbn[program230_edge_step]in HE;try contradiction.
 -destruct HE as[Hr[-> HT]];apply program230_path_nonzero.
 -destruct HE as[Hr[[H0[-> HT]]|[v[Hv[-> HT]]]]];apply program230_path_nonzero.
 -destruct HE as[-> HT];apply program230_path_nonzero.
 -destruct HE as[-> HT];apply program230_path_nonzero.
Qed.
Theorem program230_halt_excludes_step M p pc R T pc':
 program230_halt M p pc->~program230_step M p pc R T pc'.
Proof.
 intros[Q[rest HW]][e[Q'[rest'[KW KE]]]].
 destruct(program230_walk_deterministic M p pc EHalt Q rest e Q' rest' HW KW)as[_[He _]].
 subst e;exact KE.
Qed.

Theorem program230_p230_progress M pc R:
 pc<>zeroM M->program230_halt M p230 pc \/
  exists T pc',program230_step M p230 pc R T pc'.
Proof.
 intro Hnz. destruct(program230_walk_total M p230 pc p230_wf Hnz)as[e[Q[rest[HW HL]]]].
 pose proof(program230_walk_p230_register_supported M pc e Q rest HW)as HS.
 destruct(program230_edge_progress M Q e R HS(proj2(proj2 HW)))as[He|[T[pc' HE]]].
 -left;subst e;exists Q,rest;exact HW.
 -right;exists T,pc',e,Q,rest;auto.
Qed.

Theorem program230_step_clean_target M p P R T pc':
 wf p->program230_step M p(program230_path_value M P)R T pc'->
 exists P',pc'=program230_path_value M P' /\clean p P' /\
  exists e Q rest,program230_walk M p(program230_path_value M P)e Q rest /\
    (length P'<=length Q)%nat.
Proof.
 intros W[e[Q[rest[HW HE]]]].
 destruct(program230_walk_source_exact M p P e Q rest W HW)as[HWs[HQ Hrest]].
 destruct(program230_edge_control_clean M p P Q e(length Q)R T pc' HWs HQ HE)
  as[P'[Hpc[HC HL]]].
 exists P';split;[exact Hpc|split;[exact HC|exists e,Q,rest;auto]].
Qed.

Print Assumptions program230_step_deterministic.
Print Assumptions program230_step_target_nonzero.
Print Assumptions program230_halt_excludes_step.
Print Assumptions program230_p230_progress.
Print Assumptions program230_step_clean_target.
