(** Literal comparison-loop occurrences. DAG node numbers are not reused. *)
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_comparison_occurrence p P n a b c d e :=
 fol p(ENode(root p))P=Some(ENode n) /\
 nodes p n=(EDecnz 6,ENode a) /\
 nodes p a=(ENode b,ENode c) /\
 nodes p b=(EDecnz 5,EContinue 2) /\
 nodes p c=(ENode d,EInc 5) /\
 nodes p d=(EDecnz 6,ENode e) /\
 nodes p e=(EInc 5,EContinue 2).
Definition p230_comparison_path_0:list bool := [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;true;false;false;false;false].
Lemma p230_comparison_site_0:p230_comparison_occurrence p230 p230_comparison_path_0 4954 4955 4956 4957 4958 4959.
Proof. unfold p230_comparison_occurrence,p230_comparison_path_0;vm_compute;repeat split;reflexivity. Qed.
Definition p230_comparison_path_1:list bool := [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;true;true;false;false].
Lemma p230_comparison_site_1:p230_comparison_occurrence p230 p230_comparison_path_1 4971 4972 4973 4974 4975 4976.
Proof. unfold p230_comparison_occurrence,p230_comparison_path_1;vm_compute;repeat split;reflexivity. Qed.
Definition p230_comparison_path_2:list bool := [true;true;true;false;true;false;false;true;false;true;true;false;false;false].
Lemma p230_comparison_site_2:p230_comparison_occurrence p230 p230_comparison_path_2 4985 4986 4987 4988 4989 4990.
Proof. unfold p230_comparison_occurrence,p230_comparison_path_2;vm_compute;repeat split;reflexivity. Qed.
Definition p230_comparison_path_3:list bool := [true;true;true;true;true;false;false].
Lemma p230_comparison_site_3:p230_comparison_occurrence p230 p230_comparison_path_3 5090 5091 5092 5093 5094 5095.
Proof. unfold p230_comparison_occurrence,p230_comparison_path_3;vm_compute;repeat split;reflexivity. Qed.

Lemma p230_comparison_left_exit P:
 brk 1(P++[false])=inc_path P.
Proof. apply brk_car1. Qed.
Lemma p230_comparison_right_exit P:
 inc_path(P++[true;true;true])=inc_path P++[false;false;false].
Proof.
 replace(P++[true;true;true])with(((P++[true])++[true])++[true])
  by(rewrite <-!app_assoc;reflexivity).
 rewrite !inc_path_app_true,<-!app_assoc;reflexivity.
Qed.
Lemma p230_comparison_cycle_return P:
 cont 2(P++[true;false;true])=P.
Proof.
 replace(P++[true;false;true])with(((P++[true])++[false])++[true])
  by(rewrite <-!app_assoc;reflexivity).
 rewrite cont_cdrS,cont_car,cont_cdr1;reflexivity.
Qed.
Lemma p230_comparison_exit_ipeq P:
 ipeq(inc_path P++[false;false;false])(inc_path P).
Proof.
 replace(inc_path P++[false;false;false])with(((inc_path P++[false])++[false])++[false])
  by(rewrite <-!app_assoc;reflexivity).
 eapply ipeq_trans;[apply ipeq_app_false|].
 eapply ipeq_trans;[apply ipeq_app_false|apply ipeq_app_false].
Qed.
Print Assumptions p230_comparison_site_0.
Print Assumptions p230_comparison_site_1.
Print Assumptions p230_comparison_site_2.
Print Assumptions p230_comparison_site_3.
Print Assumptions p230_comparison_right_exit.
