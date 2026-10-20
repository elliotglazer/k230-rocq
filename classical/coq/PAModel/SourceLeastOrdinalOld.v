(** Fixed finite ordinal and Foundation consequences, proved with the
    pinned original natural-deduction library. No predicate-schema hole
    occurs in these lemmas. *)
From Stdlib Require Import Lists.List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldRegCon Require Import MinZF.
From OldZFC Require Import Z_base Z_prim Z_ord.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_least_background : list form := ax_reg'::ZF0base.
Lemma old_least_background_base : incl ZF0base old_least_background.
Proof. intros a HA. now right. Qed.
Lemma old_least_background_zfr a : In a old_least_background -> ZFR a.
Proof. intros [<-|HA];[apply ZFR_reg|apply ZFR_base,HA]. Qed.

Definition old_ordinal_member_law : form :=
  Ord0 $0 → ∀ ($0 ∈' $1 → Ord0 $0 ∧ Sub0 $0 $1).

Theorem old_ordinal_member_law_proof : [] ⊢C old_ordinal_member_law.
Proof.
  unfold old_ordinal_member_law. fintro HO. fall m. fintro HM. fsplit.
  - exact (ord_el_g $0 m HO HM).
  - exact (ord_el_sub_g m $0 HO HM).
Qed.

Definition old_regular_minimum_law : form :=
  $1 ∈' $0 → ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $1 → ¬ ($0 ∈' $2))).

Theorem old_regular_minimum_law_proof : old_least_background ⊢C old_regular_minimum_law.
Proof.
  assert (HG:incl ZF0base old_least_background) by exact old_least_background_base.
  assert (HR:In ax_reg' old_least_background) by now left.
  unfold old_regular_minimum_law. fintro HM.
  apply (reg_use HG HR $0 $1 HM).
Qed.

Definition old_ordinal_successor_container : form :=
  Ord0 $0 → ∃ (Ord0 $0 ∧ $1 ∈' $0).

Theorem old_ordinal_successor_container_proof :
  old_least_background ⊢C old_ordinal_successor_container.
Proof.
  assert (HG:incl ZF0base old_least_background) by exact old_least_background_base.
  unfold old_ordinal_successor_container. fintro HO.
  fobtain (succ_ex HG $0) as s HS. fexists s. fsplit.
  - exact (ord_succ_g HG $0 s HO (succ0_of HG $0 s HS)).
  - exact (succ_self HG $0 s HS).
Qed.

Print Assumptions old_ordinal_member_law_proof.
Print Assumptions old_regular_minimum_law_proof.
Print Assumptions old_ordinal_successor_container_proof.

