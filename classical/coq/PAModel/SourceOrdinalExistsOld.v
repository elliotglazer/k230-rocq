(** A fixed empty ordinal supplies the negative Cond branch. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_ordinal_exists :form :=∃ Ord0 $0.
Theorem old_ordinal_exists_proof :old_L_background ⊢C old_ordinal_exists.
Proof.
 unfold old_ordinal_exists. pose proof(emp0_ex old_hierarchy_base)as HE.
 apply(ExE_named HE). intro e. fexists e.
 apply ord_emp_g. replace(Emp0 e)with((Emp0 $0)[e..])by(simp;reflexivity).
 apply Ctx. now left.
Qed.
Print Assumptions old_ordinal_exists_proof.
