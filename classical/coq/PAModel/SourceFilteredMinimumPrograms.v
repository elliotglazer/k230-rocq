(** The finite propositional deductions in the filtered-set minimum proof.
    Slot0 is x in S, slot1 x in A, slot2 psi(x), slot3 x in m. *)
From PAModel Require Import SourcePropositionalTemplates SourceSeparationPropositional.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition filtered_minimum_profile :=
  SPTIff (SPTSlot 0) (SPTAnd (SPTSlot 1) (SPTSlot 2)).
Definition filtered_minimum_inclusion := SPTImpl (SPTSlot 3) (SPTSlot 1).
Definition filtered_minimum_exclusion :=
  SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 0) SPTFalse).
Definition filtered_predicate_exclusion :=
  SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 2) SPTFalse).

Theorem filtered_minimum_exclusion_program : source_prop_program
  [filtered_minimum_profile;filtered_minimum_inclusion;filtered_minimum_exclusion]
  filtered_predicate_exclusion.
Proof.
  unfold filtered_predicate_exclusion. apply SPTII,SPTII.
  set (A:=[SPTSlot 2;SPTSlot 3;filtered_minimum_profile;
    filtered_minimum_inclusion;filtered_minimum_exclusion]).
  change (source_prop_program A SPTFalse).
  assert (HP:source_prop_program A filtered_minimum_profile)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (HI:source_prop_program A filtered_minimum_inclusion)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (HE:source_prop_program A filtered_minimum_exclusion)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (HX:source_prop_program A (SPTSlot 3))
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (HQ:source_prop_program A (SPTSlot 2))
    by (apply SPTCtx;unfold A;cbn;tauto).
  eapply SPTIE.
  - exact (SPTIE A _ _ HE HX).
  - eapply SPTIE.
    + exact (SPTCE2 A _ _ HP).
    + apply SPTCI;[exact (SPTIE A _ _ HI HX)|exact HQ].
Qed.

Theorem filtered_minimum_predicate_program : source_prop_program
  [filtered_minimum_profile;SPTSlot 0] (SPTSlot 2).
Proof.
  eapply SPTCE2. eapply SPTIE.
  - eapply SPTCE1. apply SPTCtx. now left.
  - apply SPTCtx. right;now left.
Qed.

Theorem filtered_minimum_container_program : source_prop_program
  [filtered_minimum_profile;SPTSlot 0] (SPTSlot 1).
Proof.
  eapply SPTCE1. eapply SPTIE.
  - eapply SPTCE1. apply SPTCtx. now left.
  - apply SPTCtx. right;now left.
Qed.

Print Assumptions filtered_minimum_exclusion_program.
Print Assumptions filtered_minimum_predicate_program.
Print Assumptions filtered_minimum_container_program.

