(** Actual quantified proof macros: shifted universal elimination, and
    lifting an arbitrary internal pointwise implication under forall. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalRenaming
  SourceQuantifierRules SourceShiftSpecialization SourceProofRenaming
  SourceSequents NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_all_shift M b c n a all u v :
  sf_relation M SFAll a (zeroM M) all -> source_full_prv M b c n all ->
  context_shift M b c n u v -> source_full_prv M u v n a.
Proof.
  intros HAll HP HCtx.
  destruct (source_full_prv_wellformed M b c n all HP) as [k [HBound HCtxBound]].
  pose proof (proj1 (source_bounded_accept_unary M SFAll a all k (or_introl eq_refl) HAll)
    HBound) as HABound.
  destruct (numerical_renaming_total M all (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shifted HShift].
  pose proof (source_full_prv_renaming M b c n all (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) u v shifted HP HCtx HShift) as PShifted.
  destruct (source_shifted_all_specialization M a all shifted (succM M k)
    HABound HAll HShift) as [ar [HShifted HInst]].
  apply (full_source_AllE M u v n ar shifted (zeroM M) a).
  - exists (succM M k). split;[exact HABound|].
    exact (context_shift_preserves_bound M b c n u v k HCtx HCtxBound).
  - exact PShifted.
  - exact HShifted.
  - exact HInst.
Qed.

Theorem source_full_universal_map M b c n a d alla alld imp u v :
  source_sequent_wf M b c n alld ->
  sf_relation M SFAll a (zeroM M) alla -> sf_relation M SFAll d (zeroM M) alld ->
  sf_relation M SFImpl a d imp -> context_shift M b c n u v ->
  source_full_prv M b c n alla -> source_full_prv M u v n imp ->
  source_full_prv M b c n alld.
Proof.
  intros HWF HA HD HI HC PA PI.
  apply (full_source_AllI M b c n d alld u v HWF);[|exact HC|exact HD].
  apply (full_source_IE M u v n a d imp).
  - destruct HWF as [k [HBound HCtx]]. exists (succM M k). split.
    + exact (proj1 (source_bounded_accept_unary M SFAll d alld k (or_introl eq_refl) HD) HBound).
    + exact (context_shift_preserves_bound M b c n u v k HC HCtx).
  - exact PI.
  - exact (source_full_all_shift M b c n a alla u v HA PA HC).
  - exact HI.
Qed.

Print Assumptions source_full_all_shift.
Print Assumptions source_full_universal_map.
