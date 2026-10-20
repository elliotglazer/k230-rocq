(** The fixed set-theoretic fact needed after collecting least ordinals.
    It contains no arbitrary predicate or schematic proof parameter. *)
From Stdlib Require Import Lists.List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_iface Std_setnd Std_setbase.
From OldZFC Require Import Z_base Z_prim Z_ord.
From PAModel Require Import SourceLeastOrdinalOld.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition old_ordinal_range_upper :form :=
  (∀ ($0 ∈' $1 → Ord0 $0)) →
  ∃ (Ord0 $0 ∧ ∀ ($0 ∈' $2 → Sub0 $0 $1)).

Theorem old_ordinal_range_upper_proof :old_least_background ⊢C old_ordinal_range_upper.
Proof.
  assert (HG:incl ZF0base old_least_background) by exact old_least_background_base.
  unfold old_ordinal_range_upper. fintro HOrdinals.
  fobtain (union_ex HG $0) as upper HUpper.
  fexists upper. fsplit.
  - exact (ord_union_g HG $0 upper HOrdinals (union0_of HG $0 upper HUpper)).
  - fall ordinal. fintro HMember. unfold Sub0. fall element. fintro HElement.
    exact (union_in HG $0 upper ordinal element HUpper HMember HElement).
Qed.

Print Assumptions old_ordinal_range_upper_proof.
