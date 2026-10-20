(** Actual internal source proof weakening, obtained by PA-definable
    induction on the complete source proof trace. No completeness is used. *)
From PAModel Require Import Model NumericalContexts SourceSequents NumericalSourceFull
  SourceContextTransport SourceWeakeningInvariant SourceWeakeningUnary SourceWeakeningQuantifiers.
Unset Implicit Arguments.

Theorem source_full_row_weakening M r :
  source_full_row M r -> source_weakening_invariant M r.
Proof.
  apply (source_full_row_induction M (source_weakening_invariant M)).
  - exact (source_weakening_invariant_definable M).
  - exact (source_weakening_base M).
  - exact (source_weakening_full_unary M).
  - exact (source_weakening_full_binary M).
Qed.

Theorem source_full_prv_weaken M b c n u v l f :
  source_full_prv M b c n f -> context_included M b c n u v l ->
  source_context_finite_bound M u v l -> source_full_prv M u v l f.
Proof.
  intros [r [HS HR]] HI HC.
  exact (proj1 (proj2 (source_full_row_weakening M r HR)) b c n f u v l HS HI HC).
Qed.

Theorem source_full_prv_weaken_bounded M b c n u v l f k :
  source_full_prv M b c n f -> context_included M b c n u v l ->
  context_bounded M u v l k -> source_full_prv M u v l f.
Proof.
  intros HP HI HC. apply (source_full_prv_weaken M b c n u v l f HP HI).
  now exists k.
Qed.

Theorem source_full_branches_weaken M b c n u v l a d f :
  source_full_branches M b c n a d f -> context_included M b c n u v l ->
  source_context_finite_bound M u v l -> source_full_branches M u v l a d f.
Proof.
  intros [r [HS HR]] HI HC.
  exact (proj2 (proj2 (source_full_row_weakening M r HR)) b c n a d f u v l HS HI HC).
Qed.

Print Assumptions source_full_row_weakening.
Print Assumptions source_full_prv_weaken.
Print Assumptions source_full_prv_weaken_bounded.
Print Assumptions source_full_branches_weaken.
