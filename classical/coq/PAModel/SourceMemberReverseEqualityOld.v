(** The fixed reversed membership guard used when equal carriers are
    substituted in the antecedent of an assignment quantifier. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_member_reverse_equality_law :form := $1 ≡' $2 →$0 ∈' $2 →$0 ∈' $1.
Theorem old_member_reverse_equality_proof :old_L_background ⊢C old_member_reverse_equality_law.
Proof.
  unfold old_member_reverse_equality_law. apply II,II.
  eapply elem_r with(x:=$0)(y:=$2)(y':=$1).
  - intros a HA. do 2 right. exact(old_hierarchy_base a HA).
  - eapply eq_sym' with(x:=$1)(y:=$2).
    + intros a HA. do 2 right. exact(old_hierarchy_base a HA).
    + apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.
Print Assumptions old_member_reverse_equality_proof.
