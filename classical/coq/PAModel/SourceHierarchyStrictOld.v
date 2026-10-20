(** Strict hierarchy monotonicity retains both membership and inclusion. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_hierarchy_strict_law:form:=
 Ord0 $0 →Ord0 $1 →$0 ∈' $1 →LL $0 $2 →LL $1 $3 →($2 ∈' $3 ∧Sub0 $2 $3).
Theorem old_hierarchy_strict_proof:old_L_background ⊢C old_hierarchy_strict_law.
Proof.
 unfold old_hierarchy_strict_law. apply II,II,II,II,II.
 eapply LL_mono_g with(a:=$1)(b:=$0)(Ya:=$3)(Yb:=$2).
 - intros a HA. do 5 right. exact(old_hierarchy_base a HA).
 - do 5 right. exact old_hierarchy_reg.
 - do 5 right. exact old_hierarchy_omega.
 - intros a HA. do 5 right. exact(old_hierarchy_axioms a HA).
 - apply Ctx. do 3 right. now left.
 - apply Ctx. do 2 right. now left.
 - apply Ctx. now left.
 - apply Ctx. right. now left.
Qed.
Print Assumptions old_hierarchy_strict_proof.
