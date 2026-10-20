(** Fixed source proof of the predecessor-comparison branch. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition nl_old :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition nl_fact :=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 4)).
Definition nl_point :=SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTImpl(SPTSlot 0)(SPTSlot 4)).
Theorem source_numf_less_point_program :source_prop_program[nl_old;nl_fact]nl_point.
Proof.
 unfold nl_old,nl_fact,nl_point. apply SPTII,SPTII. eapply SPTIE.
 - eapply SPTIE.
   + apply SPTCtx. right;right;right;now left.
   + eapply SPTIE.
     * eapply SPTIE;apply SPTCtx;[right;right;now left|now left].
     * eapply SPTCE1. apply SPTCtx. right;now left.
 - eapply SPTCE2. apply SPTCtx. right;now left.
Qed.
Print Assumptions source_numf_less_point_program.
