(** Fixed logical program connecting actual lookup to an atomic profile. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition atom_lookup_left:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3)).
Definition atom_lookup_right:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 4)).
Definition atom_operation_profile:=SPTImpl(SPTSlot 5)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 7)))).
Definition atom_point_condition:=SPTAnd(SPTSlot 5)(SPTAnd(SPTSlot 1)(SPTSlot 2)).
Definition atom_point_result:=SPTImpl atom_point_condition(SPTImpl(SPTImpl(SPTSlot 0)(SPTSlot 6))(SPTImpl(SPTSlot 0)(SPTSlot 7))).
Local Ltac cx:=apply SPTCtx;cbn;tauto.
Theorem source_atomic_point_program:source_prop_program[atom_lookup_left;atom_lookup_right;atom_operation_profile]atom_point_result.
Proof.
 unfold atom_lookup_left,atom_lookup_right,atom_operation_profile,atom_point_result,atom_point_condition.
 do 3 apply SPTII.
 eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * eapply SPTIE;[cx|eapply SPTCE1;cx].
     * eapply SPTIE;[cx|cx].
   + eapply SPTIE;[eapply SPTIE;[cx|cx]|eapply SPTCE1,SPTCE2;cx].
 - eapply SPTIE;[eapply SPTIE;[cx|cx]|eapply SPTCE2,SPTCE2;cx].
Qed.
Print Assumptions source_atomic_point_program.
