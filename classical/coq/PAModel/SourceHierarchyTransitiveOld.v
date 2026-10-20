(** A hierarchy level contains all members of each of its elements. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_hierarchy_element_subset_law :form :=Ord0 $0 →LL $0 $1 →$2 ∈' $1 →Sub0 $2 $1.

Theorem old_hierarchy_element_subset_proof :old_L_background ⊢C old_hierarchy_element_subset_law.
Proof.
  unfold old_hierarchy_element_subset_law. apply II,II,II.
  assert(HT:(($2 ∈' $1)::LL $0 $1::Ord0 $0::old_L_background) ⊢C Trans0 $1).
  { eapply LL_trans_g with(a:=$0).
    - intros a HA. do 3 right. exact(old_hierarchy_base a HA).
    - do 3 right. exact old_hierarchy_reg.
    - do 3 right. exact old_hierarchy_omega.
    - intros a HA. do 3 right. exact(old_hierarchy_axioms a HA).
    - apply Ctx. right;right;now left.
    - apply Ctx. right;now left. }
  unfold Trans0 in HT. finst HT $2. eapply IE;[exact HT|apply Ctx;now left].
Qed.

Print Assumptions old_hierarchy_element_subset_proof.
