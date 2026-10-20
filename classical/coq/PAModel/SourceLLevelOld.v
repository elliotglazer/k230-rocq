(** The fixed hierarchy level itself is constructible. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_L_level_law:form:=Ord0 $0 →LL $0 $1 →InL $1.
Theorem old_L_level_proof:old_L_background ⊢C old_L_level_law.
Proof.
 unfold old_L_level_law. apply II,II.
 eapply L_LL_g with(a:=$0)(Y:=$1).
 - intros a HA. do 2 right. exact(old_hierarchy_base a HA).
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros a HA. do 2 right. exact(old_hierarchy_axioms a HA).
 - apply Ctx. right;now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_L_level_proof.
