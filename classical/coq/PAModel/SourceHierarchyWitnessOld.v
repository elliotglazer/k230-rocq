(** Further fixed hierarchy laws used by the reflection witness bound. *)
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

Definition old_hierarchy_unique_law :form :=Ord0 $0 →LL $0 $1 →LL $0 $2 →$1 ≡' $2.
Definition old_hierarchy_above_law :form :=InL $0 →Ord0 $1 →
  ∃(∃(Ord0 $1 ∧Sub0 $3 $1 ∧LL $1 $0 ∧$2 ∈' $0)).

Theorem old_hierarchy_unique_proof :old_L_background ⊢C old_hierarchy_unique_law.
Proof.
  unfold old_hierarchy_unique_law. apply II,II,II.
  eapply LL_unique_g with(a:=$0)(Y:=$1)(Y':=$2).
  - intros a HA. do 3 right. exact(old_hierarchy_base a HA).
  - do 3 right. exact old_hierarchy_reg.
  - do 3 right. exact old_hierarchy_omega.
  - intros a HA. do 3 right. exact(old_hierarchy_axioms a HA).
  - apply Ctx. do 2 right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem old_hierarchy_above_proof :old_L_background ⊢C old_hierarchy_above_law.
Proof.
  unfold old_hierarchy_above_law. apply II,II.
  eapply L_above_g with(x:=$0)(a:=$1).
  - intros a HA. do 2 right. exact(old_hierarchy_base a HA).
  - do 2 right. exact old_hierarchy_reg.
  - do 2 right. exact old_hierarchy_omega.
  - intros a HA. do 2 right. exact(old_hierarchy_axioms a HA).
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Print Assumptions old_hierarchy_unique_proof.
Print Assumptions old_hierarchy_above_proof.
