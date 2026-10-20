(** Exact read/pop sites of the public p230 program. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230Histories Program230TransferProgram Program230UnpairSites Program230ReadComposition.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_read174_path:list bool:=[true;false].
Definition p230_read175_path:list bool:=[true;true;false].
Definition p230_read176_path:list bool:=[true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;false].
Definition p230_read_top_path:list bool:=[true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;true;false].
Definition p230_pop170_path:list bool:=[true;true;true;false;true;false;false;true;false;true;true;true].
Inductive p230_read_site:list bool->nat->nat->Prop:=
| p230_read174_site:p230_read_site p230_read174_path 8 3
| p230_read175_site:p230_read_site p230_read175_path 8 4
| p230_read176_site:p230_read_site p230_read176_path 8 5
| p230_read_top_site:p230_read_site p230_read_top_path 8 1
| p230_pop170_site:p230_read_site p230_pop170_path 2 5.

Definition p230_read_effect M P a r start x y:=
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path P++[false]) /\
 program230_register final a=y /\program230_register final r=addM M(program230_register start r)x /\
 program230_register final 6=zeroM M /\program230_register final 7=zeroM M /\
 (forall i,(i<9)%nat->i<>a->i<>r->i<>6->i<>7->program230_register final i=program230_register start i).
Theorem p230_read_site_history M P a r start x y:
 p230_read_site P a r->program230_pc start=program230_path_value M P->
 pair_graph M x y(program230_register start a)->program230_register start 6=zeroM M->
 program230_register start 7=zeroM M->p230_read_effect M P a r start x y.
Proof.
 intros HS HP Hpair H6 H7;destruct HS;unfold p230_read_effect.
 -eapply(p230_read_composition M p230_read174_path 8 3 12 19 20 21 22 start x y).
  +unfold p230_unpair_sites;do 0 right;left;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +lia.
  +lia.
  +lia.
  +lia.
  +exact HP.
  +exact Hpair.
  +exact H6.
  +exact H7.
 -eapply(p230_read_composition M p230_read175_path 8 4 26 33 34 35 36 start x y).
  +unfold p230_unpair_sites;do 1 right;left;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +lia.
  +lia.
  +lia.
  +lia.
  +exact HP.
  +exact Hpair.
  +exact H6.
  +exact H7.
 -eapply(p230_read_composition M p230_read176_path 8 5 132 139 140 141 142 start x y).
  +unfold p230_unpair_sites;do 3 right;left;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +lia.
  +lia.
  +lia.
  +lia.
  +exact HP.
  +exact Hpair.
  +exact H6.
  +exact H7.
 -eapply(p230_read_composition M p230_read_top_path 8 1 192 199 200 201 202 start x y).
  +unfold p230_unpair_sites;do 4 right;left;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +lia.
  +lia.
  +lia.
  +lia.
  +exact HP.
  +exact Hpair.
  +exact H6.
  +exact H7.
 -eapply(p230_read_composition M p230_pop170_path 2 5 4996 5003 5004 5005 5006 start x y).
  +unfold p230_unpair_sites;do 92 right;left;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +vm_compute;repeat split;reflexivity.
  +lia.
  +lia.
  +lia.
  +lia.
  +exact HP.
  +exact Hpair.
  +exact H6.
  +exact H7.
Qed.
Print Assumptions p230_read_site_history.
