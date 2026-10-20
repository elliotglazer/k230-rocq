(** Finite logical assembly for the two actual existential witnesses. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition ew_ih_template:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition ew_fixed_template:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 5))).
Definition ew_num_body:=SPTAnd(SPTSlot 1)(SPTSlot 3).
Definition ew_env_body:=SPTAnd(SPTSlot 0)(SPTSlot 4).
Definition ew_point_template:=SPTImpl ew_num_body(SPTImpl ew_env_body(SPTSlot 5)).
Theorem source_envf_domain_witness_point_program:source_prop_program[ew_ih_template;ew_fixed_template]ew_point_template.
Proof.
 unfold ew_ih_template,ew_fixed_template,ew_num_body,ew_env_body,ew_point_template.
 apply SPTII,SPTII. eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * apply SPTCtx. right;right;right;now left.
     * eapply SPTIE.
       -- eapply SPTIE.
          ++ apply SPTCtx. right;right;now left.
          ++ eapply SPTCE1. apply SPTCtx. now left.
       -- eapply SPTCE1. apply SPTCtx. right;now left.
   + eapply SPTCE2. apply SPTCtx. right;now left.
 - eapply SPTCE2. apply SPTCtx. now left.
Qed.
Theorem source_envf_domain_witness_reverse_program:source_prop_program
 [SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))]
 (SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2))).
Proof.
 apply SPTII,SPTII. eapply SPTIE.
 - eapply SPTIE;apply SPTCtx;[right;right;now left|now left].
 - apply SPTCtx. right;now left.
Qed.
Print Assumptions source_envf_domain_witness_point_program.
Print Assumptions source_envf_domain_witness_reverse_program.
