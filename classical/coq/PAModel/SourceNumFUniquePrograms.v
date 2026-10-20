(** Finite proof program for comparing the two predecessor witnesses. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition nu_old :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition nu_fixed :=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))).
Definition nu_result :=SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 4))(SPTImpl(SPTAnd(SPTSlot 1)(SPTSlot 3))(SPTSlot 5)).
Theorem source_numf_unique_point_program :source_prop_program[nu_old;nu_fixed]nu_result.
Proof.
 unfold nu_old,nu_fixed,nu_result. apply SPTII,SPTII.
 eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * apply SPTCtx. right;right;right;now left.
     * eapply SPTIE.
       -- eapply SPTIE.
          ++ apply SPTCtx. right;right;now left.
          ++ eapply SPTCE1. apply SPTCtx. right;now left.
       -- eapply SPTCE1. apply SPTCtx. now left.
   + eapply SPTCE2. apply SPTCtx. now left.
 - eapply SPTCE2. apply SPTCtx. right;now left.
Qed.
Print Assumptions source_numf_unique_point_program.
