(** Literal three-independent-input closure law for the pinned operations. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_atomic_closure_ternary_law k:form:=Succ0 $0 $1→Cl $1 $2→$3∈'$2→$4∈'$2→$5∈'$2→
 ∃($0∈'$3∧Op k $4 $5 $6 $0).
Theorem old_atomic_closure_ternary_proof k:(k<8)%nat->old_L_background⊢C old_atomic_closure_ternary_law k.
Proof.
 intro HK. unfold old_atomic_closure_ternary_law. do 5 apply II.
 eapply cl_op_g with(k:=k)(B:=$1)(C:=$2)(a:=$3)(b:=$4)(c:=$5).
 - intros a HA. do 5 right. exact(old_hierarchy_base a HA).
 - do 5 right. exact old_hierarchy_reg.
 - do 5 right. exact old_hierarchy_omega.
 - intros a HA. do 5 right. exact(old_closure_axioms a HA).
 - exact HK.
 - apply Ctx. right;right;right;now left.
 - apply Ctx. right;right;now left.
 - apply Ctx. right;now left.
 - apply Ctx. now left.
Qed.
Print Assumptions old_atomic_closure_ternary_proof.
