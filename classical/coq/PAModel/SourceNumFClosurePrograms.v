(** Finite logical programs for the NumF membership-preserving successor. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition nc_point_pair :=SPTAnd(SPTSlot 0)(SPTSlot 1).
Definition nc_point_body :=SPTAnd(SPTSlot 1)(SPTSlot 2).
Definition nc_point_target :=SPTAnd(SPTSlot 3)(SPTSlot 2).
Theorem source_numf_closure_point_program :source_prop_program
 [SPTImpl nc_point_pair(SPTSlot 3);SPTImpl nc_point_target(SPTSlot 4)]
 (SPTImpl nc_point_body(SPTImpl(SPTSlot 0)(SPTSlot 4))).
Proof.
 unfold nc_point_pair,nc_point_body,nc_point_target. apply SPTII,SPTII.
 eapply SPTIE.
 - apply SPTCtx. right;right;right;now left.
 - apply SPTCI.
   + eapply SPTIE.
     * apply SPTCtx. right;right;now left.
     * apply SPTCI.
       -- apply SPTCtx. now left.
       -- eapply SPTCE1. apply SPTCtx. right;now left.
   + eapply SPTCE2. apply SPTCtx. right;now left.
Qed.
Theorem source_numf_closure_reverse_point_program :source_prop_program
 [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))]
 (SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2))).
Proof.
 apply SPTII,SPTII. eapply SPTIE.
 - eapply SPTIE;apply SPTCtx;[right;right;now left|now left].
 - apply SPTCtx. right;now left.
Qed.
Definition nc_step_law :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 3))).
Definition nc_step_use :=SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5)).
Definition nc_step_body :=SPTAnd(SPTSlot 4)(SPTSlot 2).
Definition nc_step_result :=SPTImpl nc_step_body(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 5))).
Theorem source_numf_closure_step_program :source_prop_program[nc_step_law;nc_step_use]nc_step_result.
Proof.
 unfold nc_step_law,nc_step_use,nc_step_body,nc_step_result. apply SPTII,SPTII,SPTII.
 eapply SPTIE.
 - eapply SPTIE.
   + apply SPTCtx. right;right;right;right;now left.
   + eapply SPTIE.
     * eapply SPTIE.
       -- eapply SPTIE;apply SPTCtx;[right;right;right;now left|right;now left].
       -- apply SPTCtx. now left.
     * eapply SPTCE2. apply SPTCtx. right;right;now left.
 - eapply SPTCE1. apply SPTCtx. right;right;now left.
Qed.
Theorem source_numf_closure_induction_program :source_prop_program
 [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2));
  SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)))]
 (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))).
Proof.
 apply SPTII,SPTII. eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * apply SPTCtx. right;right;right;now left.
     * eapply SPTIE.
       -- eapply SPTIE;apply SPTCtx;[right;right;now left|right;now left].
       -- apply SPTCtx. now left.
   + apply SPTCtx. right;now left.
 - apply SPTCtx. now left.
Qed.
Print Assumptions source_numf_closure_point_program.
Print Assumptions source_numf_closure_reverse_point_program.
Print Assumptions source_numf_closure_step_program.
Print Assumptions source_numf_closure_induction_program.
