(** The exact three-leaf transfer cycle used by increment-only while loops. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Configurations Program230Histories.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_edge_step_ext (M:Model) Q e (R T R' T':nat->carrier M) pc:
 (forall i,(i<9)%nat->R i =R' i)->(forall i,(i<9)%nat->T i =T' i)->
 (program230_edge_step M Q e R T pc<->program230_edge_step M Q e R' T' pc).
Proof.
 intros HR HT. assert(U:forall r value,program230_register_update M r value R T<->program230_register_update M r value R' T').
 {intros r value;unfold program230_register_update;split;intros H i Hi;specialize(H i Hi).
  -rewrite <-(HT i Hi),<-(HR i Hi);exact H.
  -rewrite (HT i Hi),(HR i Hi);exact H. }
 assert(V:program230_register_same M R T<->program230_register_same M R' T').
 {unfold program230_register_same;split;intros H i Hi;specialize(H i Hi).
  -rewrite <-(HT i Hi),<-(HR i Hi);exact H.
  -rewrite (HT i Hi),(HR i Hi);exact H. }
 destruct e as[n|r|r|k|k|];cbn[program230_edge_step];try tauto.
 -split;intros[Hreg[Hp HU]];split;[exact Hreg| |exact Hreg|];split;[exact Hp| |exact Hp|].
  +rewrite <-(HR r Hreg). apply(proj1(U r(succM M(R r))));exact HU.
  +apply(proj2(U r(succM M(R r)))). rewrite(HR r Hreg);exact HU.
 -split;intros[Hreg H];split;[exact Hreg| |exact Hreg|].
  +destruct H as[[HZ[HP HS]]|[v[HV[HP HS]]]].
   *left. split;[rewrite <-(HR r Hreg);exact HZ|]. split;[exact HP|now apply V].
   *right;exists v. split;[rewrite <-(HR r Hreg);exact HV|]. split;[exact HP|now apply U].
  +destruct H as[[HZ[HP HS]]|[v[HV[HP HS]]]].
   *left. split;[rewrite(HR r Hreg);exact HZ|]. split;[exact HP|now apply V].
   *right;exists v. split;[rewrite(HR r Hreg);exact HV|]. split;[exact HP|now apply U].
Qed.
Definition program230_transfer_cycle (M:Model) P a b (s t:program230_configuration(carrier M)):=
 (program230_pc s=program230_path_value M P /\
  program230_edge_step M(P++[false])(EDecnz a)(program230_register s)(program230_register t)(program230_pc t)) \/
 (program230_pc s=program230_path_value M(P++[true]) /\
  program230_edge_step M(P++[true;false])(EInc b)(program230_register s)(program230_register t)(program230_pc t)) \/
 (program230_pc s=program230_path_value M(P++[true;true]) /\
  program230_edge_step M(P++[true;true])(EContinue 2)(program230_register s)(program230_register t)(program230_pc t)).
Definition program230_transfer_formula P a b:form:=
 ($0==program230_path_term P ∧program230_edge_formula(P++[false])(EDecnz a)
    (fun i =>$ (S i))(fun i =>$ (11+i))$10) ∨
 (($0==program230_path_term(P++[true]) ∧program230_edge_formula(P++[true;false])(EInc b)
    (fun i =>$ (S i))(fun i =>$ (11+i))$10) ∨
 ($0==program230_path_term(P++[true;true]) ∧program230_edge_formula(P++[true;true])(EContinue 2)
    (fun i =>$ (S i))(fun i =>$ (11+i))$10)).
Lemma program230_transition_register_before M s t i:(i<9)%nat->
 program230_transition_env(zeroM M)s t(S i)=program230_register s i.
Proof. intro Hi;unfold program230_transition_env,program230_register.
 assert(H:(S i<?10)%nat=true)by(apply Nat.ltb_lt;lia). now rewrite H. Qed.
Lemma program230_transition_register_after M s t i:(i<9)%nat->
 program230_transition_env(zeroM M)s t(11+i)=program230_register t i.
Proof. intro Hi;unfold program230_transition_env,program230_register.
 assert(H:(11+i<?10)%nat=false)by(apply Nat.ltb_ge;lia).
 assert(K:(11+i<?20)%nat=true)by(apply Nat.ltb_lt;lia).
 rewrite H,K. replace(11+i-10)%nat with(S i)by lia. reflexivity. Qed.
Lemma program230_transfer_formula_correct M P a b s t:
 program230_step M(program230_transfer_formula P a b)s t<->program230_transfer_cycle M P a b s t.
Proof.
 assert(HE:forall Q e,
  program230_edge_step M Q e
   (fun i =>program230_transition_env(zeroM M)s t(S i))
   (fun i =>program230_transition_env(zeroM M)s t(11+i))(program230_pc t)<->
  program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)).
 {intros Q e. apply program230_edge_step_ext.
  -intros i Hi;apply program230_transition_register_before;exact Hi.
  -intros i Hi;apply program230_transition_register_after;exact Hi. }
 unfold program230_step,program230_transfer_formula,program230_transfer_cycle.
 rewrite !holds_or,!holds_and,!program230_holds_equal,!program230_path_term_correct,
 !program230_edge_formula_correct. cbn[evalM].
 change(((program230_pc s=program230_path_value M P /\
 program230_edge_step M(P++[false])(EDecnz a)
 (fun i =>program230_transition_env(zeroM M)s t(S i))
 (fun i =>program230_transition_env(zeroM M)s t(11+i))(program230_pc t)) \/
 ((program230_pc s=program230_path_value M(P++[true]) /\
 program230_edge_step M(P++[true;false])(EInc b)
 (fun i =>program230_transition_env(zeroM M)s t(S i))
 (fun i =>program230_transition_env(zeroM M)s t(11+i))(program230_pc t)) \/
 (program230_pc s=program230_path_value M(P++[true;true]) /\
 program230_edge_step M(P++[true;true])(EContinue 2)
 (fun i =>program230_transition_env(zeroM M)s t(S i))
 (fun i =>program230_transition_env(zeroM M)s t(11+i))(program230_pc t))))<->program230_transfer_cycle M P a b s t).
 rewrite !HE;reflexivity.
Qed.
Print Assumptions program230_transfer_formula_correct.