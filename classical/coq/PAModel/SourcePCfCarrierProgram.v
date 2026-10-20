(** Fixed propositional combination for a carrier-equality induction. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition pcf_carrier_previous:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition pcf_carrier_piece:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 3)(SPTSlot 4)).
Definition pcf_carrier_conjunction:=SPTImpl(SPTSlot 0)
  (SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTAnd(SPTSlot 2)(SPTSlot 4))).
Theorem source_pcf_carrier_conjunction_program:
  source_prop_program[pcf_carrier_previous;pcf_carrier_piece]pcf_carrier_conjunction.
Proof.
  unfold pcf_carrier_previous,pcf_carrier_piece,pcf_carrier_conjunction.
  apply SPTII,SPTII,SPTCI.
  - eapply SPTIE.
    + eapply SPTIE.
      * apply SPTCtx. right;right;now left.
      * apply SPTCtx. right;now left.
    + eapply SPTCE1. apply SPTCtx. now left.
  - eapply SPTIE.
    + eapply SPTIE.
      * apply SPTCtx. right;right;right;now left.
      * apply SPTCtx. right;now left.
    + eapply SPTCE2. apply SPTCtx. now left.
Qed.
Print Assumptions source_pcf_carrier_conjunction_program.
