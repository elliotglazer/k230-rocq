(** Fixed hierarchy existence and monotonicity deductions, independent of
    the varying reflection predicate. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_L.
From PAModel Require Import SourceLFixed.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_hierarchy_exists_law :form :=Ord0 $0 → ∃ LL $1 $0.
Definition old_hierarchy_subset_law :form :=
  Ord0 $0 →Ord0 $1 →Sub0 $0 $1 →LL $0 $2 →LL $1 $3 →Sub0 $2 $3.

Lemma old_hierarchy_base :incl ZF0base old_L_background.
Proof. intros a HA. right;right. apply in_app_iff. now left. Qed.
Lemma old_hierarchy_reg :In ax_reg' old_L_background.
Proof. now left. Qed.
Lemma old_hierarchy_omega :In ax_om' old_L_background.
Proof. right;now left. Qed.
Lemma old_hierarchy_axioms :incl Ax_L old_L_background.
Proof. intros a HA. right;right. apply in_app_iff. now right. Qed.

Theorem old_hierarchy_exists_proof :old_L_background ⊢C old_hierarchy_exists_law.
Proof.
  unfold old_hierarchy_exists_law. apply II.
  eapply LL_ex_g with (a:=$0).
  - intros a HA. right. exact(old_hierarchy_base a HA).
  - right. exact old_hierarchy_reg.
  - right. exact old_hierarchy_omega.
  - intros a HA. right. exact(old_hierarchy_axioms a HA).
  - apply Ctx. now left.
Qed.

Theorem old_hierarchy_subset_proof :old_L_background ⊢C old_hierarchy_subset_law.
Proof.
  unfold old_hierarchy_subset_law. apply II,II,II,II,II.
  eapply LL_sub_g with (a:=$1)(b:=$0)(Ya:=$3)(Yb:=$2).
  - intros a HA. do 5 right. exact(old_hierarchy_base a HA).
  - do 5 right. exact old_hierarchy_reg.
  - do 5 right. exact old_hierarchy_omega.
  - intros a HA. do 5 right. exact(old_hierarchy_axioms a HA).
  - apply Ctx. do 3 right. now left.
  - apply Ctx. do 4 right. now left.
  - apply Ctx. do 2 right. now left.
  - apply Ctx. now left.
  - apply Ctx. right. now left.
Qed.

Print Assumptions old_hierarchy_exists_proof.
Print Assumptions old_hierarchy_subset_proof.
