(** Literal source-name vacuity and named generalization. The context
    premise compares actual renaming graphs; it is never arbitrary
    contextual generalization. Closing a name with a quantifier proves
    this vacuity at that name even when the matrix has nested binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded NumericalContexts NumericalContextRenaming
  NumericalRenamingMaps NumericalRenaming RawBinderRenaming SourceRenamingDiamond
  SourceQuantifierRules SourceShiftSpecialization SourceImplicationAllShift SourceNamedSelfSpecialization
  SourceSequents SourceTraceBounds NumericalSourceFull SourceProofRenaming SourceProofWeakening.
Unset Implicit Arguments.

Definition source_named_vacuous M x f :=forall rb rc g shifted,
  raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) g ->
  source_formula_shift M f shifted ->g=shifted.
Definition source_named_context_vacuous M b c n x :=forall f,
  context_member M b c n f ->source_named_vacuous M x f.

Theorem source_named_quantifier_vacuous M (universal:bool) f x rb rc body quantified k :
  source_bounded M f k ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  sf_relation M (if universal then SFAll else SFEx) body (zeroM M) quantified ->
  source_named_vacuous M x quantified.
Proof.
  intros HF HM HR HQ ub uc result shifted HU HResult HShift.
  apply (proj1 (numerical_renaming_quantifier M universal body quantified ub uc
    (succM M x)(succM M (zeroM M)) result HQ)) in HResult.
  destruct HResult as (ud&ue&un&closed&HLU&HRC&HOut).
  apply (proj1 (numerical_renaming_quantifier M universal body quantified
    (zeroM M)(zeroM M)(zeroM M)(succM M (zeroM M)) shifted HQ)) in HShift.
  destruct HShift as (sd&se&sn&shiftbody&HLS&HRS&HShiftOut).
  assert (HCloseShift:numerical_renaming M body ud ue un (succM M (zeroM M)) shiftbody).
  { apply (numerical_source_renaming_diamond M f k
      rb rc (succM M x)(succM M (zeroM M))
      rb rc (succM M x)(succM M (zeroM M))
      sd se sn (succM M (zeroM M)) ud ue un (succM M (zeroM M))
      body body shiftbody HF HR HR HRS).
    intros i j l m HI HJ HJM HL.
    assert (EL:l=j) by (exact (renaming_lookup_functional M rb rc _ _ i l j HL HJ)).
    subst l. apply (proj1 (HM i j)) in HJ.
    destruct HJ as [[-> ->]|[HIX ->]].
    - apply (proj1 (renaming_lift_head M _ _ _ _ sd se sn m HLS)) in HJM. subst m.
      exact (proj2 (renaming_lift_head M _ _ _ _ ud ue un (zeroM M) HLU) eq_refl).
    - destruct (renaming_lift_tail_inv M _ _ _ _ sd se sn i m HLS HJM) as (v&HV&EM).
      apply context_shift_lookup in HV. subst v m.
      apply (proj2 (renaming_lift_tail M _ _ _ _ ud ue un i (succM M i) HLU)).
      apply (proj2 (HU i (succM M i))). right;auto. }
  rewrite (numerical_renaming_functional M body ud ue un (succM M (zeroM M))
    closed shiftbody HRC HCloseShift) in HOut.
  exact (sf_relation_functional M (if universal then SFAll else SFEx) shiftbody
    (zeroM M) result shifted HOut HShiftOut).
Qed.

Theorem source_full_named_close_proof M b c n f x rb rc body u v :
  source_named_context_vacuous M b c n x ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  context_shift M b c n u v ->source_full_prv M b c n f ->
  source_full_prv M u v n body.
Proof.
  intros HCtx HM HR HShift HP.
  destruct (context_renaming_total M b c n rb rc (succM M x)(succM M (zeroM M))) as (d&e&HD).
  pose proof (source_full_prv_renaming M b c n f rb rc (succM M x)(succM M (zeroM M))
    d e body HP HD HR) as PBody.
  destruct (source_full_prv_wellformed M b c n f HP) as (k&_&HC).
  apply (source_full_prv_weaken_bounded M d e n u v n body (succM M k) PBody);[|].
  - intros g HG. apply (proj1 (context_renaming_member_iff M b c n rb rc
      (succM M x)(succM M (zeroM M)) d e g HD)) in HG.
    destruct HG as (old&HO&HRename).
    destruct (context_renaming_member_forward M b c n (zeroM M)(zeroM M)(zeroM M)
      (succM M (zeroM M)) u v old HShift HO) as (shifted&HSMember&HS).
    rewrite (HCtx old HO rb rc g shifted HM HRename HS). exact HSMember.
  - exact (context_shift_preserves_bound M b c n u v k HShift HC).
Qed.

Theorem source_full_named_all_intro M b c n f x rb rc body allf :
  source_named_context_vacuous M b c n x ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  sf_relation M SFAll body (zeroM M) allf ->source_full_prv M b c n f ->
  source_full_prv M b c n allf.
Proof.
  intros HCtx HM HR HA HP.
  destruct (source_full_prv_wellformed M b c n f HP) as (k&HF&HC).
  destruct (context_shift_total M b c n) as (u&v&HShift).
  apply (full_source_AllI M b c n body allf u v).
  - exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFAll body allf k (or_introl eq_refl) HA)).
    exact (source_named_closure_bounded M f x rb rc body k HF HM HR).
  - exact (source_full_named_close_proof M b c n f x rb rc body u v HCtx HM HR HShift HP).
  - exact HShift.
  - exact HA.
Qed.

Print Assumptions source_named_quantifier_vacuous.
Print Assumptions source_full_named_all_intro.
