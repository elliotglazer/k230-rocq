(** The fixed pinned theorem that every raw set has an L-level
    containing all of its constructible elements. Its extra axiom list is finite. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord Z_L Z_axL.
From PAModel Require Import SourceLFixed SourceLFixedImages.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition old_L_bound_background:list form:=old_L_background++powL_insts.
Definition old_L_bound_law:form:=
 ∃ (∃ (Ord0 $1 ∧ LL $1 $0 ∧ ∀ ($0 ∈' $3 →InL $0 →$0 ∈' $1))).
Theorem old_L_bound_background_valid a:In a old_L_bound_background ->ZFR a.
Proof.
 apply(old_L_extended_background_valid powL_insts).
 intros q HQ. exact(oc_insts_ok 0 Qpow q fb_Qpow HQ).
Qed.
Theorem old_L_bound_proof:old_L_bound_background ⊢C old_L_bound_law.
Proof.
 unfold old_L_bound_background,old_L_bound_law.
 exact(L_bound(old_L_background_base powL_insts)(old_L_background_reg powL_insts)
  (old_L_background_omega powL_insts)(old_L_background_hierarchy powL_insts)$0
  ltac:(intros a HA;apply in_app_iff;now right)).
Qed.
Print Assumptions old_L_bound_background_valid.
Print Assumptions old_L_bound_proof.
