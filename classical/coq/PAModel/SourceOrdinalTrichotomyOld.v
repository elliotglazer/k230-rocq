(** A fixed pinned ZFR deduction of ordinal trichotomy. No varying
    predicate is present in this finite certificate. *)
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_trichotomy_background : list form := ax_reg'::(ZF0base++Ax_ord).
Definition old_ordinal_trichotomy_law : form := Ord0 $0 → Ord0 $1 → Tri $0 $1.

Lemma old_trichotomy_background_valid a : In a old_trichotomy_background -> ZFR a.
Proof.
  intros [<-|HA];[apply ZFR_reg|].
  apply in_app_iff in HA as [HA|HA];[apply ZFR_base,HA|apply Ax_ord_ok,HA].
Qed.

Theorem old_ordinal_trichotomy_law_proof : old_trichotomy_background ⊢C old_ordinal_trichotomy_law.
Proof.
  assert (HG:incl ZF0base old_trichotomy_background).
  { intros a HA. right. apply in_app_iff. now left. }
  assert (HO:incl Ax_ord old_trichotomy_background).
  { intros a HA. right. apply in_app_iff. now right. }
  assert (HR:In ax_reg' old_trichotomy_background) by now left.
  unfold old_ordinal_trichotomy_law. fintro HA. fintro HB.
  exact (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) $0 $1 HA HB).
Qed.
Print Assumptions old_ordinal_trichotomy_law_proof.
