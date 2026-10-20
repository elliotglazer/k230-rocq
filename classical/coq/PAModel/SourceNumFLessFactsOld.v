(** Fixed comparison facts after exposing a successor's predecessor. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord Z_cl.
From PAModel Require Import SourceLFixed SourceHierarchyOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_numf_less_fact(equal:bool):form :=
 (if equal then $1 ≡' $0 else $1 ∈' $0) →Succ0 $0 $2 →$1 ∈' $2.
Theorem old_numf_less_fact_proof(equal:bool):old_L_background ⊢C old_numf_less_fact equal.
Proof.
 unfold old_numf_less_fact. destruct equal.
 - apply II,II.
   assert(HG:incl ZF0base(Succ0 $0 $2::$1 ≡' $0::old_L_background))by(intros a HA;do 2 right;exact(old_hierarchy_base a HA)).
   assert(E:(Succ0 $0 $2::$1 ≡' $0::old_L_background) ⊢C $1 ≡' $0)by(apply Ctx;right;now left).
   assert(S:(Succ0 $0 $2::$1 ≡' $0::old_L_background) ⊢C Succ0 $0 $2)by(apply Ctx;now left).
   pose proof(succ0_self HG $0 $2 S)as H. frew E ($0 ∈' $2`[↑]). exact H.
 - apply II,II. eapply sub0_use.
   + intros a HA. do 2 right. exact(old_hierarchy_base a HA).
   + eapply succ0_sub.
     * intros a HA. do 2 right. exact(old_hierarchy_base a HA).
     * apply Ctx. now left.
   + apply Ctx. right;now left.
Qed.
Print Assumptions old_numf_less_fact_proof.
