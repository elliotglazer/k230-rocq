(** Pinned finite union existence certificate for the reflection carrier. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd.
From OldZFC Require Import Z_base Z_prim.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
#[local] Existing Instance sig_empty|0.
#[local] Existing Instance ZF_pred_sig|0.
Unset Implicit Arguments.
Definition old_reflection_union_exists:form:=∃ Union0 $1 $0.
Theorem old_reflection_union_exists_proof:old_L_background ⊢C old_reflection_union_exists.
Proof. exact(union0_ex old_hierarchy_base ltac:(intros a H;contradiction) $0). Qed.
Print Assumptions old_reflection_union_exists_proof.
