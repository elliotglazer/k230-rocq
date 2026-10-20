(** Fixed propositional programs for the literal two-witness lookup step. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition el_domain:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition el_unique:=SPTImpl(SPTSlot 4)(SPTImpl(SPTSlot 1)(SPTSlot 5)).
Definition el_distinct:=SPTImpl(SPTSlot 4)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 5)SPTFalse)).
Definition el_old:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 4)(SPTSlot 7)).
Definition el_head:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 5)(SPTSlot 6))).
Definition el_tail:=SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTImpl(SPTSlot 5)SPTFalse)(SPTImpl(SPTSlot 7)(SPTSlot 6)))).
Definition el_point:=SPTImpl(SPTSlot 1)(SPTImpl(SPTAnd(SPTSlot 0)(SPTSlot 3))(SPTImpl(SPTSlot 4)(SPTSlot 6))).
Local Ltac cx:=apply SPTCtx;cbn;tauto.
Theorem source_env_lookup_head_program:source_prop_program[el_domain;el_unique;el_head]el_point.
Proof.
 unfold el_domain,el_unique,el_head,el_point. do 3 apply SPTII.
 eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * cx.
     * eapply SPTIE;[eapply SPTIE;[cx|eapply SPTCE1;cx]|cx].
   + eapply SPTCE2;cx.
 - eapply SPTIE;[eapply SPTIE;[cx|cx]|cx].
Qed.
Theorem source_env_lookup_tail_program:source_prop_program[el_domain;el_distinct;el_old;el_tail]el_point.
Proof.
 unfold el_domain,el_distinct,el_old,el_tail,el_point. do 3 apply SPTII.
 eapply SPTIE.
 - eapply SPTIE.
   + eapply SPTIE.
     * eapply SPTIE.
       -- cx.
       -- eapply SPTIE;[eapply SPTIE;[cx|eapply SPTCE1;cx]|cx].
     * eapply SPTCE2;cx.
   + eapply SPTIE;[eapply SPTIE;[cx|cx]|cx].
 - eapply SPTIE;[eapply SPTIE;[cx|eapply SPTCE1;cx]|cx].
Qed.
Print Assumptions source_env_lookup_head_program.
Print Assumptions source_env_lookup_tail_program.
