(** A genuinely fixed old proof. The varying-matrix extension is separate. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase Std_setrec Std_setinf.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_recursion_bottom_base_law:form:=SNz phSig $0 $2 →
 ∃(Att phSig ⊥ $1 $2 $3 $0 ∧App $0 $1 $2).
Theorem old_recursion_bottom_base_proof:old_L_background ⊢C old_recursion_bottom_base_law.
Proof.
 unfold old_recursion_bottom_base_law. apply II.
 refine(att_base _ phSig ⊥ $2 $0 $1 _).
 - intros f HF. right. exact(old_hierarchy_base f HF).
 - apply Ctx. now left.
Qed.
Print Assumptions old_recursion_bottom_base_proof.
