(** Bounds for the translated rows in the internal proof invariant. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalContexts
  SourceBounded SourceBoundMonotone SourceSequents SourceTraceBounds
  SupportedQuotationContext SourceRelativization SourceRelativizationBounds
  SourceRelativeContexts SourceRelativizedWellformedness.
Unset Implicit Arguments.

Lemma source_relative_row_sequent_wf M domain bound r b c n f k u v l g :
  source_bounded M domain (succM M (zeroM M)) ->
  source_row_at_bound M r bound -> source_sequent M b c n f r ->
  coding_lt M bound (succM M k) ->
  source_relative_context M domain b c n k u v l ->
  source_relativization M domain f g -> source_sequent_wf M u v l g.
Proof.
  intros HD HB HR HK HC HG.
  destruct (source_row_bound_sequent M r bound b c n f HB HR) as [HF HCtx].
  apply (source_relativized_bounded_sequent M domain f g k u v l HD).
  - exact (source_bounded_monotone M f bound k HF HK).
  - exact HG.
  - apply (source_relative_context_bounded M domain b c n k u v l HD).
    + exact (context_bounded_monotone M b c n bound k HCtx HK).
    + exact HC.
Qed.

Lemma source_relative_row_branches_wf M domain bound r b c n a d f k u v l ra rd rf :
  source_bounded M domain (succM M (zeroM M)) ->
  source_row_at_bound M r bound -> source_branches M b c n a d f r ->
  coding_lt M bound (succM M k) ->
  source_relative_context M domain b c n k u v l ->
  source_relativization M domain a ra -> source_relativization M domain d rd ->
  source_relativization M domain f rf -> source_branches_wf M u v l ra rd rf.
Proof.
  intros HD HB HR HK HC HA HD' HF.
  destruct (source_row_bound_branches M r bound b c n a d f HB HR)
    as [HBA [HBD [HBF HCtx]]].
  exists k. repeat split.
  - apply (source_relativization_preserves_bound M a domain k ra HD);[|exact HA].
    exact (source_bounded_monotone M a bound k HBA HK).
  - apply (source_relativization_preserves_bound M d domain k rd HD);[|exact HD'].
    exact (source_bounded_monotone M d bound k HBD HK).
  - apply (source_relativization_preserves_bound M f domain k rf HD);[|exact HF].
    exact (source_bounded_monotone M f bound k HBF HK).
  - apply (source_relative_context_bounded M domain b c n k u v l HD).
    + exact (context_bounded_monotone M b c n bound k HCtx HK).
    + exact HC.
Qed.

Print Assumptions source_relative_row_sequent_wf.
Print Assumptions source_relative_row_branches_wf.
