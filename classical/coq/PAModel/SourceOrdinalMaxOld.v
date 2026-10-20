(** The pinned ordinary ordinal maximum deduction with its finite background discharged. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_ordinal_max_law :form :=Ord0 $0 →Ord0 $1 →
  ∃((Ord0 $0 ∧Sub0 $1 $0)∧Sub0 $2 $0).

Theorem old_ordinal_max_proof :old_L_background ⊢C old_ordinal_max_law.
Proof.
  unfold old_ordinal_max_law. apply II,II.
  eapply ord_max_g with (a:=$0)(b:=$1).
  - intros a HA. right;right. exact(old_hierarchy_base a HA).
  - apply Ctx. right;now left.
  - apply Ctx. now left.
Qed.

Print Assumptions old_ordinal_max_proof.
