(** Finite source-calculus programs for the three PCf-bound ExE shells. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition pcf_curry_input := SPTImpl(SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 2))(SPTSlot 3).
Definition pcf_curry_output := SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))).
Theorem source_pcf_curry_program : source_prop_program[pcf_curry_input]pcf_curry_output.
Proof.
  unfold pcf_curry_input,pcf_curry_output. apply SPTII,SPTII,SPTII.
  eapply SPTIE.
  - apply SPTCtx. right;right;right;now left.
  - apply SPTCI.
    + apply SPTCI;apply SPTCtx;[right;now left|now left].
    + apply SPTCtx. right;right;now left.
Qed.

Definition pcf_successor_A := SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 2))(SPTSlot 3).
Definition pcf_successor_B := SPTAnd(SPTSlot 1)(SPTSlot 4).
Definition pcf_successor_exists := SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 5)).
Definition pcf_successor_use := SPTImpl(SPTSlot 5)(SPTImpl pcf_successor_A(SPTImpl pcf_successor_B(SPTSlot 6))).
Definition pcf_successor_output := SPTImpl pcf_successor_A(SPTImpl pcf_successor_B(SPTSlot 6)).
Theorem source_pcf_successor_shell_program :
  source_prop_program[pcf_successor_exists;pcf_successor_use]pcf_successor_output.
Proof.
  unfold pcf_successor_exists,pcf_successor_use,pcf_successor_output,pcf_successor_A,pcf_successor_B.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + eapply SPTIE.
      * apply SPTCtx. right;right;right;now left.
      * eapply SPTIE.
        -- eapply SPTIE.
           ++ apply SPTCtx. right;right;now left.
           ++ eapply SPTCE1,SPTCE1. apply SPTCtx. right;now left.
        -- eapply SPTCE1. apply SPTCtx. now left.
    + apply SPTCtx. right;now left.
  - apply SPTCtx. now left.
Qed.

Definition pcf_previous_exists := SPTImpl(SPTSlot 0)(SPTSlot 4).
Definition pcf_previous_use := SPTImpl(SPTSlot 4)(SPTImpl pcf_successor_A(SPTSlot 5)).
Definition pcf_previous_output := SPTImpl pcf_successor_A(SPTSlot 5).
Theorem source_pcf_previous_shell_program :
  source_prop_program[pcf_previous_exists;pcf_previous_use]pcf_previous_output.
Proof.
  unfold pcf_previous_exists,pcf_previous_use,pcf_previous_output,pcf_successor_A.
  apply SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;now left.
    + eapply SPTIE.
      * apply SPTCtx. right;now left.
      * eapply SPTCE1,SPTCE1. apply SPTCtx. now left.
  - apply SPTCtx. now left.
Qed.

Print Assumptions source_pcf_curry_program.
Print Assumptions source_pcf_successor_shell_program.
Print Assumptions source_pcf_previous_shell_program.
