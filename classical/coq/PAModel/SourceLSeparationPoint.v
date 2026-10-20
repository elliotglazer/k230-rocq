(** The finite logical core of Z_axL.axL_sep': replace the set-level
    predicate by the reflected class predicate, retaining the same witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition lsep_iff a b := SPTAnd (SPTImpl a b) (SPTImpl b a).
(* Slots: z in X, z in Y, z in A, phi^L(z), phi^Y(z). *)
Definition lsep_definition_point :=
  lsep_iff (SPTSlot 0) (SPTAnd (SPTSlot 1) (SPTAnd (SPTSlot 2) (SPTSlot 4))).
Definition lsep_reflection_point := SPTImpl (SPTSlot 1) (lsep_iff (SPTSlot 3) (SPTSlot 4)).
Definition lsep_transitive_point := SPTImpl (SPTSlot 2) (SPTSlot 1).
Definition lsep_result_point := lsep_iff (SPTSlot 0) (SPTAnd (SPTSlot 2) (SPTSlot 3)).
Definition lsep_point_assumptions := [lsep_definition_point;lsep_reflection_point;lsep_transitive_point].

Lemma lsep_point_program : source_prop_program lsep_point_assumptions lsep_result_point.
Proof.
  unfold lsep_result_point,lsep_iff. apply SPTCI.
  - apply SPTII.
    set (A:=SPTSlot 0::lsep_point_assumptions).
    assert (PD:source_prop_program A lsep_definition_point) by
      (apply SPTCtx;unfold A,lsep_point_assumptions;cbn;tauto).
    assert (PR:source_prop_program A lsep_reflection_point) by
      (apply SPTCtx;unfold A,lsep_point_assumptions;cbn;tauto).
    assert (PX:source_prop_program A (SPTSlot 0)) by (apply SPTCtx;unfold A;now left).
    assert (PYAS:source_prop_program A (SPTAnd (SPTSlot 1)(SPTAnd (SPTSlot 2)(SPTSlot 4)))).
    { eapply SPTIE;[eapply SPTCE1;exact PD|exact PX]. }
    assert (PY:source_prop_program A (SPTSlot 1)) by (eapply SPTCE1;exact PYAS).
    assert (PAS:source_prop_program A (SPTAnd (SPTSlot 2)(SPTSlot 4))) by (eapply SPTCE2;exact PYAS).
    assert (PIff:source_prop_program A (lsep_iff (SPTSlot 3)(SPTSlot 4))) by (eapply SPTIE;[exact PR|exact PY]).
    apply SPTCI;[eapply SPTCE1;exact PAS|].
    eapply SPTIE;[eapply SPTCE2;exact PIff|eapply SPTCE2;exact PAS].
  - apply SPTII.
    set (A:=SPTAnd (SPTSlot 2)(SPTSlot 3)::lsep_point_assumptions).
    assert (PD:source_prop_program A lsep_definition_point) by
      (apply SPTCtx;unfold A,lsep_point_assumptions;cbn;tauto).
    assert (PR:source_prop_program A lsep_reflection_point) by
      (apply SPTCtx;unfold A,lsep_point_assumptions;cbn;tauto).
    assert (PT:source_prop_program A lsep_transitive_point) by
      (apply SPTCtx;unfold A,lsep_point_assumptions;cbn;tauto).
    assert (PAL:source_prop_program A (SPTAnd (SPTSlot 2)(SPTSlot 3))) by
      (apply SPTCtx;unfold A;now left).
    assert (PA:source_prop_program A (SPTSlot 2)) by (eapply SPTCE1;exact PAL).
    assert (PY:source_prop_program A (SPTSlot 1)) by (eapply SPTIE;[exact PT|exact PA]).
    assert (PIff:source_prop_program A (lsep_iff (SPTSlot 3)(SPTSlot 4))) by (eapply SPTIE;[exact PR|exact PY]).
    eapply SPTIE;[eapply SPTCE2;exact PD|].
    apply SPTCI;[exact PY|]. apply SPTCI;[exact PA|].
    eapply SPTIE;[eapply SPTCE1;exact PIff|eapply SPTCE2;exact PAL].
Qed.

Theorem source_full_L_separation_point M rho k b c n definition reflection transitive result :
  (forall i,source_bounded M (rho i) k) ->context_bounded M b c n k ->
  code_relation M rho (source_prop_expression lsep_definition_point) definition ->
  code_relation M rho (source_prop_expression lsep_reflection_point) reflection ->
  code_relation M rho (source_prop_expression lsep_transitive_point) transitive ->
  code_relation M rho (source_prop_expression lsep_result_point) result ->
  source_full_prv M b c n definition ->source_full_prv M b c n reflection ->
  source_full_prv M b c n transitive ->source_full_prv M b c n result.
Proof.
  intros HB HC HD HR HT HG PD PR PT.
  apply (source_prop_program_sound M lsep_point_assumptions lsep_result_point lsep_point_program rho k b c n result HB HC);[|exact HG].
  intros a HA f HF. unfold lsep_point_assumptions in HA.
  destruct HA as [<-|[<-|[<-|[]]]].
  - pose proof (code_relation_functional M _ rho f definition HF HD) as E. now subst f.
  - pose proof (code_relation_functional M _ rho f reflection HF HR) as E. now subst f.
  - pose proof (code_relation_functional M _ rho f transitive HF HT) as E. now subst f.
Qed.

Print Assumptions lsep_point_program.
Print Assumptions source_full_L_separation_point.
