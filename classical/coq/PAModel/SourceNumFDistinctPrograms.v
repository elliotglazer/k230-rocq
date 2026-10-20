(** Actual finite propositional programs, including reversal of premise order. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition nd_member(reverse:bool):=if reverse then SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2))
 else SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition nd_fact:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)SPTFalse).
Definition nd_law:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)SPTFalse)).
Theorem source_numf_distinct_program reverse:source_prop_program[nd_member reverse;nd_fact]nd_law.
Proof.
 destruct reverse;unfold nd_member,nd_fact,nd_law;apply SPTII,SPTII,SPTII.
 - eapply SPTIE.
   + eapply SPTIE.
     * apply SPTCtx. right;right;right;right;now left.
     * eapply SPTIE.
       -- eapply SPTIE.
          ++ apply SPTCtx. right;right;right;now left.
          ++ apply SPTCtx. right;now left.
       -- apply SPTCtx. right;right;now left.
   + apply SPTCtx. now left.
 - eapply SPTIE.
   + eapply SPTIE.
     * apply SPTCtx. right;right;right;right;now left.
     * eapply SPTIE.
       -- eapply SPTIE.
          ++ apply SPTCtx. right;right;right;now left.
          ++ apply SPTCtx. right;right;now left.
       -- apply SPTCtx. right;now left.
   + apply SPTCtx. now left.
Qed.
Print Assumptions source_numf_distinct_program.
