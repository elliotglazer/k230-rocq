(** The final witness-bound case split is an object-calculus derivation
    from Peirce, with no meta-level excluded-middle axiom. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition witness_bound_cases_positive :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition witness_bound_cases_negative :=SPTImpl(SPTImpl(SPTSlot 0)SPTFalse)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition witness_bound_cases_result :=SPTImpl(SPTSlot 1)(SPTSlot 2).

Theorem source_witness_bound_cases_program :source_prop_program
  [witness_bound_cases_positive;witness_bound_cases_negative]witness_bound_cases_result.
Proof.
  unfold witness_bound_cases_positive,witness_bound_cases_negative,witness_bound_cases_result.
  apply SPTII. eapply SPTIE;[exact(SPTPc _ (SPTSlot 2)SPTFalse)|].
  apply SPTII. eapply(SPTIE _ (SPTSlot 1)(SPTSlot 2)).
  - eapply SPTIE.
    + apply SPTCtx. right;right;right;now left.
    + apply SPTII. eapply SPTIE.
      * apply SPTCtx. right;now left.
      * eapply(SPTIE _ (SPTSlot 1)(SPTSlot 2)).
        -- eapply SPTIE.
           ++ apply SPTCtx. right;right;right;now left.
           ++ apply SPTCtx. now left.
        -- apply SPTCtx. right;right;now left.
  - apply SPTCtx. right;now left.
Qed.

Print Assumptions source_witness_bound_cases_program.
