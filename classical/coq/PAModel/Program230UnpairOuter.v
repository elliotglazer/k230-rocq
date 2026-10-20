(** Clean-input consequence of the actual outer unpair induction.
    The only pending hypothesis is the separately implemented concrete body certificate. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230Configurations
 Program230Histories Program230PathCode Program230Copy2States Program230TransferProgram
 Program230InstructionFormula Program230PairIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem program230_unpair_clean M P a start count:
 (a<9)%nat->a<>6->a<>7->
 fol p230(ENode(root p230))(P++[false]) = Some(EDecnz a)->
 program230_unpair_body M P a->
 program230_pc start = program230_path_value M P->program230_register start a = count->
 program230_register start 6 = zeroM M->program230_register start 7 = zeroM M->
 exists u v N final,program230_program_history M p230 u v N start /\
 program230_state_at M u v N final /\
 program230_pc final = program230_path_value M(inc_path P) /\
 program230_register final a = zeroM M /\
 pair_graph M(program230_register final 6)(program230_register final 7)count /\
 (forall i,(i<9)%nat->i<>a->i<>6->i<>7->program230_register final i = program230_register start i).
Proof.
 intros Ha Ha6 Ha7 HF HB HP HI H6 H7.
 destruct(program230_unpair_iteration M P a Ha HF HB start count
 (zeroM M)(zeroM M)(zeroM M)(pair_zero M))as[u[v[N[x[y[HR[HT Hpair]]]]]]].
 rewrite(program230_copy2_restore a 6 7 start(program230_path_value M P)count(zeroM M)(zeroM M)HP HI H6 H7)in HR.
 set(final:=program230_copy2_state a 6 7 start(program230_path_value M(inc_path P))(zeroM M)x y).
 assert(Ha':program230_register final a = zeroM M).
 {unfold final;rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl. }
 assert(H6':program230_register final 6 = x).
 {unfold final;rewrite program230_copy2_register by lia.
  now rewrite(proj2(Nat.eqb_neq 6 a)ltac:(congruence)),Nat.eqb_refl. }
 assert(H7':program230_register final 7 = y).
 {unfold final;rewrite program230_copy2_register by lia.
  now rewrite(proj2(Nat.eqb_neq 7 a)ltac:(congruence)),(proj2(Nat.eqb_neq 7 6)ltac:(lia)),Nat.eqb_refl. }
 exists u,v,N,final;split;[apply p230_instruction_history_correct;exact HR|].
 split;[exact HT|]. split;[reflexivity|]. split;[exact Ha'|]. split.
 -rewrite H6',H7'. now rewrite coding_add_zero in Hpair.
 -intros i Hi Hia Hi6 Hi7;unfold final;rewrite program230_copy2_register by exact Hi.
  now rewrite(proj2(Nat.eqb_neq i a)Hia),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7).
Qed.
Definition p230_unpair_input_path:list bool:=[true;false;false;false].
Lemma p230_unpair_input_leaf:
 fol p230(ENode(root p230))(p230_unpair_input_path++[false]) = Some(EDecnz 8).
Proof. vm_compute;reflexivity. Qed.
Corollary p230_unpair_from_body M start count:
 program230_unpair_body M p230_unpair_input_path 8->
 program230_pc start = program230_path_value M p230_unpair_input_path->program230_register start 8 = count->
 program230_register start 6 = zeroM M->program230_register start 7 = zeroM M->
 exists u v N final,program230_program_history M p230 u v N start /\
 program230_state_at M u v N final /\
 program230_pc final = program230_path_value M(inc_path p230_unpair_input_path) /\
 program230_register final 8 = zeroM M /\
 pair_graph M(program230_register final 6)(program230_register final 7)count /\
 (forall i,(i<9)%nat->i<>8->i<>6->i<>7->program230_register final i = program230_register start i).
Proof.
 intro HB;apply(program230_unpair_clean M p230_unpair_input_path 8 start count);try lia;
 [exact p230_unpair_input_leaf|exact HB].
Qed.
Print Assumptions program230_unpair_clean.
Print Assumptions p230_unpair_from_body.
