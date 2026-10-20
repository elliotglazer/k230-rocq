(** Unique literal NIP halt site and its padded equality exit. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Selector Program230PathCode Program230Read Program230Walk Program230Transition.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_nip_test_outer:list bool:=p230_selector_nip++[true;false].
Definition p230_nip_test_parent:list bool:=p230_nip_test_outer++[false].
Definition p230_nip_halt_path:list bool:=p230_nip_test_outer++[true].
Definition p230_nip_equal_exit:list bool:=inc_path p230_nip_test_parent++[false].
Definition p230_nip_unequal_exit:list bool:=brk 1 p230_nip_test_parent.
Lemma p230_nip_outer_equations:
 nodes p230 4981=(EInc 6,ENode 4982) /\
 nodes p230 4982=(ENode 4983,ENode 4994) /\
 nodes p230 4983=(ENode 4984,EHalt).
Proof. repeat split;reflexivity. Qed.
Lemma p230_nip_test_actual:
 fol p230(ENode(root p230))p230_nip_test_parent=Some(ENode 4984).
Proof. reflexivity. Qed.
Lemma p230_nip_halt_actual:
 fol p230(ENode(root p230))p230_nip_halt_path=Some EHalt.
Proof. reflexivity. Qed.
Lemma p230_nip_equal_exit_exact:p230_nip_equal_exit=p230_nip_halt_path++[false].
Proof. reflexivity. Qed.
Lemma p230_nip_unequal_exit_exact:p230_nip_unequal_exit=p230_selector_nip++[true;true].
Proof. reflexivity. Qed.
Lemma p230_nip_skip_actual:
 fol p230(ENode(root p230))p230_nip_unequal_exit=Some(ENode 4994).
Proof. reflexivity. Qed.
Lemma p230_nip_equal_read M:
 program230_read M(program230_path_value M p230_nip_equal_exit)
  p230_nip_halt_path(program230_path_value M([false])).
Proof. exact(program230_read_path M 13 p230_nip_equal_exit). Qed.
Theorem p230_nip_equal_halts M:
 Program230Transition.program230_halt M p230(program230_path_value M p230_nip_equal_exit).
Proof.
 exists p230_nip_halt_path,(program230_path_value M([false]));split;[apply p230_nip_equal_read|].
 split;[apply p230_nip_halt_actual|reflexivity].
Qed.
Print Assumptions p230_nip_outer_equations.
Print Assumptions p230_nip_equal_halts.
Print Assumptions p230_nip_skip_actual.
