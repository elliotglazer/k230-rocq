(** Fixed propositional programs for the hierarchy witness shells. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_witness_six_environment {A}(o s l m p g:A)i :=
  match i with 0=>o|1=>s|2=>l|3=>m|4=>p|_=>g end.
Definition source_witness_five_environment {A}(l o ex p g:A)i :=
  match i with 0=>l|1=>o|2=>ex|3=>p|_=>g end.

Definition witness_positive_input :=SPTImpl
  (SPTAnd(SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTSlot 3))(SPTSlot 4))(SPTSlot 5).
Definition witness_positive_body :=SPTAnd(SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 2))(SPTSlot 3).
Definition witness_positive_output :=SPTImpl witness_positive_body(SPTImpl(SPTSlot 4)(SPTSlot 5)).

Theorem source_witness_positive_rearrangement :source_prop_program[witness_positive_input]witness_positive_output.
Proof.
  unfold witness_positive_input,witness_positive_output,witness_positive_body.
  apply SPTII,SPTII. eapply SPTIE.
  - apply SPTCtx. right;right;now left.
  - apply SPTCI.
    + apply SPTCI.
      * apply SPTCI.
        -- eapply SPTCE1,SPTCE1,SPTCE1,SPTCtx. right;now left.
        -- eapply SPTCE2,SPTCE1,SPTCtx. right;now left.
      * eapply SPTCE2,SPTCtx. right;now left.
    + apply SPTCtx. now left.
Qed.

Definition witness_above_input :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition witness_existential_input :=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 4)).
Definition witness_above_output :=SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 3))
  (SPTImpl(SPTSlot 1)(SPTSlot 4)).

Theorem source_witness_above_application :source_prop_program
  [witness_above_input;witness_existential_input]witness_above_output.
Proof.
  unfold witness_above_input,witness_existential_input,witness_above_output.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;right;now left.
    + eapply SPTIE.
      * eapply SPTIE.
        -- apply SPTCtx. right;right;now left.
        -- eapply SPTCE1,SPTCtx. right;now left.
      * apply SPTCtx. now left.
  - eapply SPTCE2,SPTCtx. right;now left.
Qed.

Print Assumptions source_witness_positive_rearrangement.
Print Assumptions source_witness_above_application.
