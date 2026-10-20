(** Literal last two equality gates of AX in the public p230 tree. *)
From PAModel Require Import Program230ComparisonGuards Program230ComparisonSites
 Program230Copy2Program Program230TransferProgram Program230ResetLoop Program230Selector.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_gate_path:list bool:=[true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;true].
Definition p230_ax_gate_copy:list bool:=[true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;true].
Definition p230_ax_gate_reset0:=p230_ax_gate_path++[false;false;true].
Definition p230_ax_gate_restore:=p230_ax_gate_path++[false;true;false].
Definition p230_ax_gate_load:=p230_ax_gate_path++[false;true;true].
Definition p230_ax_gate_reset1:=p230_ax_gate_path++[true;true].
Lemma p230_ax_gate_copy_site:program230_copy2_occurrence p230 p230_ax_gate_copy 3 7 6 4947 4948 4949.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma p230_ax_gate_restore_site:program230_transfer_occurrence p230 p230_ax_gate_restore 7 6 4965 4966.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma p230_ax_gate_load_site:program230_transfer_occurrence p230 p230_ax_gate_load 4 5 4967 4968.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma p230_ax_gate_reset0_site:program230_reset_occurrence p230 p230_ax_gate_reset0 1 4963.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma p230_ax_gate_reset1_site:program230_reset_occurrence p230 p230_ax_gate_reset1 1 4980.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma p230_ax_gate_paths:
 p230_comparison_parent_path_0=p230_ax_gate_path++[false;false;false] /\
 p230_comparison_parent_path_1=p230_ax_gate_path++[true;false] /\
 inc_path p230_ax_gate_copy=p230_comparison_parent_path_0++[false] /\
 inc_path p230_comparison_parent_path_0=p230_ax_gate_reset0 /\
 brk 1 p230_comparison_parent_path_0=p230_ax_gate_path++[false;true] /\
 inc_path p230_ax_gate_reset0=p230_ax_gate_restore /\
 inc_path p230_ax_gate_restore=p230_ax_gate_load /\
 inc_path p230_ax_gate_load=p230_comparison_parent_path_1++[false] /\
 inc_path p230_comparison_parent_path_1=p230_ax_gate_reset1 /\
 brk 1 p230_comparison_parent_path_1=inc_path(p230_ax_gate_path++[true]) /\
 ipeq(inc_path p230_ax_gate_reset1)(inc_path p230_selector_ax).
Proof.
 repeat split;try reflexivity.
 all: try (vm_compute;reflexivity).
 intros i;unfold p230_ax_gate_reset1,p230_ax_gate_path,p230_selector_ax;
 do 32(destruct i;[reflexivity|]);reflexivity.
Qed.
Print Assumptions p230_ax_gate_copy_site.
Print Assumptions p230_ax_gate_paths.
