(** Exact outer guard/reset skeleton for the four comparison occurrences. *)
From K230 Require Import RM RMEquiv Prog230.
From PAModel Require Import Program230ComparisonSites.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_comparison_guard_occurrence p P parent loop guard wrapper reset :=
 fol p(ENode(root p))P=Some(ENode parent) /\
 nodes p parent=(ENode loop,ENode guard) /\
 nodes p guard=(EDecnz 5,ENode wrapper) /\
 nodes p wrapper=(ENode reset,EBreak 1) /\
 nodes p reset=(EDecnz 5,EContinue 1).
Definition p230_comparison_parent_path_0:list bool := [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;true;false;false;false].
Lemma p230_comparison_guard_site_0:p230_comparison_guard_occurrence p230 p230_comparison_parent_path_0 4953 4954 4960 4961 4962.
Proof. unfold p230_comparison_guard_occurrence,p230_comparison_parent_path_0;vm_compute;repeat split;reflexivity. Qed.
Lemma p230_comparison_parent_loop_0:p230_comparison_parent_path_0++[false]=p230_comparison_path_0.
Proof. reflexivity. Qed.
Definition p230_comparison_parent_path_1:list bool := [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;true;true;false].
Lemma p230_comparison_guard_site_1:p230_comparison_guard_occurrence p230 p230_comparison_parent_path_1 4970 4971 4977 4978 4979.
Proof. unfold p230_comparison_guard_occurrence,p230_comparison_parent_path_1;vm_compute;repeat split;reflexivity. Qed.
Lemma p230_comparison_parent_loop_1:p230_comparison_parent_path_1++[false]=p230_comparison_path_1.
Proof. reflexivity. Qed.
Definition p230_comparison_parent_path_2:list bool := [true;true;true;false;true;false;false;true;false;true;true;false;false].
Lemma p230_comparison_guard_site_2:p230_comparison_guard_occurrence p230 p230_comparison_parent_path_2 4984 4985 4991 4992 4993.
Proof. unfold p230_comparison_guard_occurrence,p230_comparison_parent_path_2;vm_compute;repeat split;reflexivity. Qed.
Lemma p230_comparison_parent_loop_2:p230_comparison_parent_path_2++[false]=p230_comparison_path_2.
Proof. reflexivity. Qed.
Definition p230_comparison_parent_path_3:list bool := [true;true;true;true;true;false].
Lemma p230_comparison_guard_site_3:p230_comparison_guard_occurrence p230 p230_comparison_parent_path_3 5089 5090 5096 5097 5098.
Proof. unfold p230_comparison_guard_occurrence,p230_comparison_parent_path_3;vm_compute;repeat split;reflexivity. Qed.
Lemma p230_comparison_parent_loop_3:p230_comparison_parent_path_3++[false]=p230_comparison_path_3.
Proof. reflexivity. Qed.

Lemma p230_comparison_guard_equal_exit P:
 brk 1(P++[true;false])=inc_path P++[false].
Proof.
 replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite brk_car1,inc_path_app_true;reflexivity.
Qed.
Lemma p230_comparison_guard_reset_exit P:
 inc_path(P++[true;true;false])=P++[true;true;true].
Proof.
 replace(P++[true;true;false])with((P++[true;true])++[false])by(rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false,<-app_assoc;reflexivity.
Qed.
Lemma p230_comparison_guard_unequal_exit P:
 brk 1(P++[true;true;true])=brk 1 P.
Proof.
 replace(P++[true;true;true])with(((P++[true])++[true])++[true])by(rewrite <-!app_assoc;reflexivity).
 rewrite !brk_cdr;reflexivity.
Qed.
Lemma p230_comparison_outer_equal_exit P:
 brk 1((P++[false])++[true;false])=P++[true;false].
Proof. rewrite p230_comparison_guard_equal_exit,inc_path_app_false,<-app_assoc;reflexivity. Qed.
Lemma p230_comparison_outer_unequal_exit P:
 brk 1((P++[false])++[true;true;true])=inc_path P.
Proof. rewrite p230_comparison_guard_unequal_exit,brk_car1;reflexivity. Qed.
Print Assumptions p230_comparison_guard_site_0.
Print Assumptions p230_comparison_guard_site_1.
Print Assumptions p230_comparison_guard_site_2.
Print Assumptions p230_comparison_guard_site_3.
Print Assumptions p230_comparison_outer_equal_exit.
Print Assumptions p230_comparison_outer_unequal_exit.
