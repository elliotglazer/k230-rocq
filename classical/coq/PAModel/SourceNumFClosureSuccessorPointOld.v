(** The closure-successor law with its witness name already specialized. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_numf_closure_successor_point :form :=Succ0 $1 $2 →Cl $2 $3 →$0 ∈' $3 →
 ∃(Succ0 $1 $0 ∧$0 ∈' $4).
Theorem old_numf_closure_successor_point_proof :old_L_background ⊢C old_numf_closure_successor_point.
Proof.
 unfold old_numf_closure_successor_point. apply II,II,II.
 eapply old_closure_successor_step with(A:=$1)(S0:=$2)(C:=$3)(x:=$0).
 - intros a HA. do 3 right. exact(old_hierarchy_base a HA).
 - do 3 right. exact old_hierarchy_reg.
 - do 3 right. exact old_hierarchy_omega.
 - intros a HA. do 3 right. exact(old_closure_axioms a HA).
 - apply Ctx. right;right;now left.
 - apply Ctx. right;now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_numf_closure_successor_point_proof.
