(** The ordinal comparison proof of uniqueness of a minimal witness.
    Arbitrary predicate formulas appear as opaque propositional slots. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition ordinal_unique_tri := SPTOr (SPTOr (SPTSlot 0) (SPTSlot 1)) (SPTSlot 2).
Definition ordinal_unique_left_exclusion := SPTImpl (SPTSlot 0) (SPTImpl (SPTSlot 3) SPTFalse).
Definition ordinal_unique_right_exclusion := SPTImpl (SPTSlot 2) (SPTImpl (SPTSlot 4) SPTFalse).
Definition ordinal_unique_premises :=
  [ordinal_unique_tri;SPTSlot 3;SPTSlot 4;ordinal_unique_left_exclusion;ordinal_unique_right_exclusion].

Theorem ordinal_unique_program : source_prop_program ordinal_unique_premises (SPTSlot 1).
Proof.
  unfold ordinal_unique_tri in *.
  apply (SPTDE ordinal_unique_premises (SPTOr (SPTSlot 0) (SPTSlot 1)) (SPTSlot 2) (SPTSlot 1)).
  - apply SPTCtx. unfold ordinal_unique_premises,ordinal_unique_tri;cbn;tauto.
  - apply (SPTDE _ (SPTSlot 0) (SPTSlot 1) (SPTSlot 1)).
    + apply SPTCtx. now left.
    + apply SPTExp. apply (SPTIE _ (SPTSlot 3) SPTFalse).
      * apply (SPTIE _ (SPTSlot 0) (SPTImpl (SPTSlot 3) SPTFalse)).
        -- apply SPTCtx. unfold ordinal_unique_premises,ordinal_unique_left_exclusion;cbn;tauto.
        -- apply SPTCtx. now left.
      * apply SPTCtx. unfold ordinal_unique_premises;cbn;tauto.
    + apply SPTCtx. now left.
  - apply SPTExp. apply (SPTIE _ (SPTSlot 4) SPTFalse).
    + apply (SPTIE _ (SPTSlot 2) (SPTImpl (SPTSlot 4) SPTFalse)).
      * apply SPTCtx. unfold ordinal_unique_premises,ordinal_unique_right_exclusion;cbn;tauto.
      * apply SPTCtx. now left.
    + apply SPTCtx. unfold ordinal_unique_premises;cbn;tauto.
Qed.
Print Assumptions ordinal_unique_program.
