(** Fixed propositional derivations used by the actual Cond proof. *)
From PAModel Require Import SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_reflection_joint:=SPTAnd(SPTAnd(SPTSlot 0)(SPTSlot 1))(SPTSlot 2).
Definition source_reflection_unique_template:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)(SPTSlot 4))).
Definition source_reflection_carrier_template:=SPTImpl(SPTSlot 4)(SPTImpl(SPTSlot 2)(SPTSlot 5)).
Definition source_reflection_point_template:=SPTImpl source_reflection_joint(SPTImpl(SPTSlot 3)(SPTSlot 5)).
Theorem source_reflection_point_program:source_prop_program
  [source_reflection_unique_template;source_reflection_carrier_template]source_reflection_point_template.
Proof.
  unfold source_reflection_unique_template,source_reflection_carrier_template,source_reflection_point_template,source_reflection_joint.
  apply SPTII,SPTII. eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;right;right;now left.
    + eapply SPTIE.
      * eapply SPTIE.
        -- eapply SPTIE;[apply SPTCtx;right;right;now left|].
           eapply SPTCE1,SPTCE1. apply SPTCtx. right;now left.
        -- eapply SPTCE2,SPTCE1. apply SPTCtx. right;now left.
      * apply SPTCtx. now left.
  - eapply SPTCE2. apply SPTCtx. right;now left.
Qed.

Definition source_reflection_all_input:=SPTImpl source_reflection_joint(SPTSlot 4).
Definition source_reflection_condition_output:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
  (SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 0)(SPTAnd(SPTSlot 3)(SPTSlot 4)))))).
Theorem source_reflection_condition_program:source_prop_program[source_reflection_all_input]source_reflection_condition_output.
Proof.
  unfold source_reflection_all_input,source_reflection_condition_output,source_reflection_joint.
  apply SPTII,SPTII,SPTII,SPTII,SPTII,SPTCI.
  - apply SPTCtx. right;right;now left.
  - eapply SPTIE;[apply SPTCtx;right;right;right;right;right;now left|]. apply SPTCI.
    + apply SPTCI;apply SPTCtx;[now left|right;right;right;now left].
    + apply SPTCtx. right;now left.
Qed.

Print Assumptions source_reflection_point_program.
Print Assumptions source_reflection_condition_program.
