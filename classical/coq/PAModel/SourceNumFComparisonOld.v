(** Fixed set-theoretic facts for uniform NumF comparison. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord Z_cl Z_L.
From PAModel Require Import SourceLFixed SourceHierarchyOld SourceClosureNumeralsOld.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_numf_empty_unique :form :=Emp0 $0 →Emp0 $1 →$0 ≡' $1.
Definition old_numf_successor_square :form :=$0 ≡' $1 →Succ0 $1 $2 →Succ0 $0 $3 →$2 ≡' $3.
Definition old_numf_successor_member :form :=Succ0 $0 $1 →$0 ∈' $1.
Definition old_numf_successor_upper :form :=$0 ∈' $1 →Succ0 $1 $2 →$0 ∈' $2.
Definition old_numf_member_unequal :form :=$0 ∈' $1 →$0 ≡' $1 →⊥.
Theorem old_numf_empty_unique_proof :old_L_background ⊢C old_numf_empty_unique.
Proof.
 unfold old_numf_empty_unique. apply II,II.
 eapply u_emp0_unique.
 - intros a HA. do 2 right. exact(old_hierarchy_base a HA).
 - do 2 right. exact old_hierarchy_reg.
 - do 2 right. exact old_hierarchy_omega.
 - intros a HA. do 2 right. exact(old_closure_axioms a HA).
 - apply Ctx. right;now left.
 - apply Ctx. now left.
Qed.
Theorem old_numf_successor_square_proof :old_L_background ⊢C old_numf_successor_square.
Proof.
 unfold old_numf_successor_square. apply II,II,II.
 assert(E:(Succ0 $0 $3::Succ0 $1 $2::$0 ≡' $1::old_L_background) ⊢C $0 ≡' $1)by(apply Ctx;right;right;now left).
 assert(S:(Succ0 $0 $3::Succ0 $1 $2::$0 ≡' $1::old_L_background) ⊢C Succ0 $0 $3)by(apply Ctx;now left).
 assert(HG:incl ZF0base(Succ0 $0 $3::Succ0 $1 $2::$0 ≡' $1::old_L_background))by(intros a HA;do 3 right;exact(old_hierarchy_base a HA)).
 frew_in E (Succ0 $0 $3`[↑]) S.
 eapply u_succ0_unique.
 - intros a HA. do 3 right. exact(old_hierarchy_base a HA).
 - do 3 right. exact old_hierarchy_reg.
 - do 3 right. exact old_hierarchy_omega.
 - intros a HA. do 3 right. exact(old_closure_axioms a HA).
 - apply Ctx. right;now left.
 - exact S.
Qed.
Theorem old_numf_successor_member_proof :old_L_background ⊢C old_numf_successor_member.
Proof.
 unfold old_numf_successor_member. apply II. eapply succ0_self.
 - intros a HA. right. exact(old_hierarchy_base a HA).
 - apply Ctx. now left.
Qed.
Theorem old_numf_successor_upper_proof :old_L_background ⊢C old_numf_successor_upper.
Proof.
 unfold old_numf_successor_upper. apply II,II.
 eapply sub0_use.
 - intros a HA. do 2 right. exact(old_hierarchy_base a HA).
 - eapply succ0_sub.
   + intros a HA. do 2 right. exact(old_hierarchy_base a HA).
   + apply Ctx. now left.
 - apply Ctx. right;now left.
Qed.
Theorem old_numf_member_unequal_proof :old_L_background ⊢C old_numf_member_unequal.
Proof.
 unfold old_numf_member_unequal. apply II,II.
 assert(E:($0 ≡' $1::$0 ∈' $1::old_L_background) ⊢C $0 ≡' $1)by(apply Ctx;now left).
 assert(H:($0 ≡' $1::$0 ∈' $1::old_L_background) ⊢C $0 ∈' $1)by(apply Ctx;right;now left).
 assert(HG:incl ZF0base($0 ≡' $1::$0 ∈' $1::old_L_background))by(intros a HA;do 2 right;exact(old_hierarchy_base a HA)).
 frew_in E ($0 ∈' $1`[↑]) H.
 exact(u_no_self HG ltac:(do 2 right;exact old_hierarchy_reg)
  ltac:(do 2 right;exact old_hierarchy_omega)
  ltac:(intros a HA;do 2 right;exact(old_closure_axioms a HA)) $1 H).
Qed.
Print Assumptions old_numf_empty_unique_proof.
Print Assumptions old_numf_successor_square_proof.
Print Assumptions old_numf_successor_member_proof.
Print Assumptions old_numf_successor_upper_proof.
Print Assumptions old_numf_member_unequal_proof.
