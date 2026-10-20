(** Finite implication proof with different assignment-carrier guards. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition carrier_body_map:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition carrier_guard_map:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 4)(SPTSlot 3)).
Definition carrier_point_map:=SPTImpl(SPTSlot 0)
  (SPTImpl(SPTImpl(SPTSlot 3)(SPTSlot 1))(SPTImpl(SPTSlot 4)(SPTSlot 2))).
Theorem source_carrier_guard_program :
  source_prop_program[carrier_body_map;carrier_guard_map]carrier_point_map.
Proof.
  unfold carrier_body_map,carrier_guard_map,carrier_point_map.
  apply SPTII,SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;right;now left.
    + apply SPTCtx. right;right;now left.
  - eapply SPTIE.
    + apply SPTCtx. right;now left.
    + eapply SPTIE.
      * eapply SPTIE.
        -- apply SPTCtx. right;right;right;right;now left.
        -- apply SPTCtx. right;right;now left.
      * apply SPTCtx. now left.
Qed.
Print Assumptions source_carrier_guard_program.
