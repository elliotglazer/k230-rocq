(** The fixed set-membership transport used by the hierarchy witness
    branch.  Only the pinned finite background is used. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From PAModel Require Import SourceLFixed.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_member_right_equality_law :form :=
  $1 ≡' $2 →$0 ∈' $1 →$0 ∈' $2.

Theorem old_member_right_equality_proof :
  old_L_background ⊢C old_member_right_equality_law.
Proof.
  unfold old_member_right_equality_law. apply II,II.
  eapply elem_r with(x:=$0)(y:=$1)(y':=$2).
  - intros a HA. do 2 right. unfold old_L_background.
    right;right. apply in_app_iff. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Print Assumptions old_member_right_equality_proof.
