(** Whole-proof source relativization in an arbitrary PA model.
    The proof predicate, syntax transform, common bound, and row invariant
    are arithmetic, so the proof length need not be standard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalTraces
  NumericalSourceFull SourceSequents SourceQuantifierRules SourceTraceBounds
  SourceRuleBounds SourceBoundedInduction SourceBounded SourceRelativization
  SourceRelativeContexts SourceRelativeInvariant SourceRelativePropositionalRows
  SourceRelativeBinaryRows SourceRelativeQuantifierRows SourceRelativeExERow.
Unset Implicit Arguments.

Section Translation.
Variable M : Model.
Variable domain : carrier M.
Hypothesis HD : source_bounded M domain (code_numeral M 1).

Lemma source_relative_full_unary bound r p :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_unary_at M r p bound -> source_relative_good M domain bound r.
Proof.
  intros HB HP [HProp|[_ HQuant]].
  - exact (source_relative_prop_unary_row M domain bound HD r p HB HP HProp).
  - exact (source_relative_quantifier_unary M domain bound r p HD HB HP HQuant).
Qed.

Lemma source_relative_full_binary bound r p q :
  source_row_at_bound M r bound -> source_relative_good M domain bound p ->
  source_relative_good M domain bound q -> source_full_binary M r p q ->
  source_relative_good M domain bound r.
Proof.
  intros HB HP HQ [HProp|[_ HEx]].
  - exact (source_relative_prop_binary_row M domain bound HD r p q HB HP HQ HProp).
  - exact (source_relative_ExE_row M domain bound r p q HD HB HP HQ HEx).
Qed.

Theorem source_full_relativized_trace b c n :
  trace_sequence M source_full_rules b c (succM M n) ->
  exists bound,forall i r,coding_lt M i (succM M n) -> beta M b c i r ->
    source_relative_good M domain bound r.
Proof.
  intro HS.
  destruct (source_trace_uniform_bound M b c (succM M n) HS) as [bound HB].
  exists bound. apply (source_bounded_trace_induction M (source_relative_good M domain bound)
    b c n bound).
  - exact (source_relative_good_definable M domain bound).
  - exact (source_relative_base_row M domain bound HD).
  - exact (source_relative_full_unary bound).
  - exact (source_relative_full_binary bound).
  - exact HB.
Qed.

Theorem source_full_relativized_rows r :
  source_full_row M r -> exists bound,source_relative_good M domain bound r.
Proof.
  intros [b [c [n [HS HR]]]].
  destruct (source_full_relativized_trace b c n HS) as [bound HB].
  exists bound. exact (HB n r (coding_lt_succ M n) HR).
Qed.

Theorem source_full_relativized_proof b c n f :
  source_full_prv M b c n f ->
  exists bound,forall k u v l g,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain f g -> source_full_prv M u v l g.
Proof.
  intros [r [HR HP]].
  destruct (source_full_relativized_rows r HP) as [bound HB].
  exists bound. exact (proj1 (proj2 HB) b c n f HR).
Qed.

Theorem source_full_relativized_branches b c n a d f :
  source_full_branches M b c n a d f ->
  exists bound,forall k u v l ra rd rf,coding_lt M bound (succM M k) ->
    source_relative_context M domain b c n k u v l ->
    source_relativization M domain a ra -> source_relativization M domain d rd ->
    source_relativization M domain f rf -> source_full_branches M u v l ra rd rf.
Proof.
  intros [r [HR HP]].
  destruct (source_full_relativized_rows r HP) as [bound HB].
  exists bound. exact (proj2 (proj2 HB) b c n a d f HR).
Qed.
End Translation.

Print Assumptions source_full_relativized_trace.
Print Assumptions source_full_relativized_rows.
Print Assumptions source_full_relativized_proof.
Print Assumptions source_full_relativized_branches.
