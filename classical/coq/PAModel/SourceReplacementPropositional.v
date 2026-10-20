(** The pointwise functionality step for Replacement with a guarded
    matrix. Every slot is an arbitrary internal source formula code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition replacement_guarded_point :=
  SPTImpl (SPTSlot 0) (SPTImpl (SPTSlot 1) (SPTImpl (SPTSlot 2)
    (SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 4) (SPTSlot 5))))).
Definition replacement_guarded_left := SPTAnd (SPTAnd (SPTSlot 0) (SPTSlot 1)) (SPTSlot 3).
Definition replacement_guarded_right := SPTAnd (SPTAnd (SPTSlot 0) (SPTSlot 2)) (SPTSlot 4).
Definition replacement_unguarded_point :=
  SPTImpl replacement_guarded_left (SPTImpl replacement_guarded_right (SPTSlot 5)).
Definition replacement_functionality_cleanup :=
  SPTImpl replacement_guarded_point replacement_unguarded_point.

Definition replacement_gathered_point :=
  SPTImpl (SPTAnd (SPTSlot 0) (SPTSlot 1))
    (SPTImpl (SPTSlot 2) (SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 4) (SPTSlot 5)))).
Definition replacement_gathered_cleanup :=
  SPTImpl replacement_gathered_point replacement_unguarded_point.
Definition source_curry_point := SPTImpl (SPTSlot 0) (SPTImpl (SPTSlot 1) (SPTSlot 2)).
Definition source_joined_point := SPTImpl (SPTAnd (SPTSlot 0) (SPTSlot 1)) (SPTSlot 2).

Lemma source_joined_point_program :
  source_prop_program [] (SPTImpl source_curry_point source_joined_point).
Proof.
  unfold source_curry_point,source_joined_point. apply SPTII,SPTII.
  eapply SPTIE.
  - eapply SPTIE.
    + apply SPTCtx. right;now left.
    + eapply SPTCE1. apply SPTCtx. now left.
  - eapply SPTCE2. apply SPTCtx. now left.
Qed.

Lemma replacement_functionality_cleanup_program :
  source_prop_program [] replacement_functionality_cleanup.
Proof.
  unfold replacement_functionality_cleanup,replacement_unguarded_point.
  apply SPTII,SPTII,SPTII.
  set (A:=[replacement_guarded_right;replacement_guarded_left;replacement_guarded_point]).
  change (source_prop_program A (SPTSlot 5)).
  assert (PG:source_prop_program A replacement_guarded_point)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (PL:source_prop_program A replacement_guarded_left)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (PR:source_prop_program A replacement_guarded_right)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (P0:source_prop_program A (SPTSlot 0)) by
    (eapply SPTCE1;eapply SPTCE1;exact PL).
  assert (P1:source_prop_program A (SPTSlot 1)) by
    (eapply SPTCE2;eapply SPTCE1;exact PL).
  assert (P2:source_prop_program A (SPTSlot 2)) by
    (eapply SPTCE2;eapply SPTCE1;exact PR).
  assert (P3:source_prop_program A (SPTSlot 3)) by (eapply SPTCE2;exact PL).
  assert (P4:source_prop_program A (SPTSlot 4)) by (eapply SPTCE2;exact PR).
  eapply SPTIE;[|exact P4]. eapply SPTIE;[|exact P3].
  eapply SPTIE;[|exact P2]. eapply SPTIE;[|exact P1].
  eapply SPTIE;[exact PG|exact P0].
Qed.

Lemma replacement_gathered_cleanup_program :
  source_prop_program [] replacement_gathered_cleanup.
Proof.
  unfold replacement_gathered_cleanup,replacement_unguarded_point.
  apply SPTII,SPTII,SPTII.
  set (A:=[replacement_guarded_right;replacement_guarded_left;replacement_gathered_point]).
  change (source_prop_program A (SPTSlot 5)).
  assert (PG:source_prop_program A replacement_gathered_point)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (PL:source_prop_program A replacement_guarded_left)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (PR:source_prop_program A replacement_guarded_right)
    by (apply SPTCtx;unfold A;cbn;tauto).
  assert (P01:source_prop_program A (SPTAnd (SPTSlot 0) (SPTSlot 1))) by
    (eapply SPTCE1;exact PL).
  assert (P2:source_prop_program A (SPTSlot 2)) by
    (eapply SPTCE2;eapply SPTCE1;exact PR).
  assert (P3:source_prop_program A (SPTSlot 3)) by (eapply SPTCE2;exact PL).
  assert (P4:source_prop_program A (SPTSlot 4)) by (eapply SPTCE2;exact PR).
  eapply SPTIE;[|exact P4]. eapply SPTIE;[|exact P3].
  eapply SPTIE;[|exact P2]. eapply SPTIE;[exact PG|exact P01].
Qed.

Theorem numerical_source_replacement_functionality_cleanup M rho k b c n imp :
  (forall i,source_bounded M (rho i) k) -> context_bounded M b c n k ->
  code_relation M rho (source_prop_expression replacement_functionality_cleanup) imp ->
  source_full_prv M b c n imp.
Proof.
  intros HB HC HI.
  apply (source_prop_program_sound M [] replacement_functionality_cleanup
    replacement_functionality_cleanup_program rho k b c n imp HB HC);[|exact HI].
  intros a HA. destruct HA.
Qed.

Print Assumptions replacement_functionality_cleanup_program.
Print Assumptions numerical_source_replacement_functionality_cleanup.
Print Assumptions source_joined_point_program.
Print Assumptions replacement_gathered_cleanup_program.
