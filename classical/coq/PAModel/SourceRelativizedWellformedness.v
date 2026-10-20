(** Relativized formulas can be used in any bounded target context,
    including a mapped context extended with domain assumptions. *)
From PAModel Require Import Model NumericalContexts SourceBounded SourceSequents
  SourceRelativization SourceRelativizationBounds.
Unset Implicit Arguments.

Theorem source_relativized_bounded_sequent M dom f g k b c n :
  source_bounded M dom (succM M (zeroM M)) -> source_bounded M f k ->
  source_relativization M dom f g -> context_bounded M b c n k ->
  source_sequent_wf M b c n g.
Proof.
  intros HD HF HR HC. exists k;split;[|exact HC].
  exact (source_relativization_preserves_bound M f dom k g HD HF HR).
Qed.

Print Assumptions source_relativized_bounded_sequent.
