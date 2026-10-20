(** Induction on a fixed source trace with one common bound. The predicate
    and trace parameters are PA-definable, including nonstandard lengths. *)
From PAModel Require Import Model FiniteCoding FiniteCRT NumericalTraces
  TheoryProofInduction CourseOfValues SourcePropositionalRules SourceQuantifierRules
  SourceTraceBounds SourceRuleBounds.
Unset Implicit Arguments.

Theorem source_bounded_trace_induction M P b c n bound :
  Definable1 M P ->
  (forall r,source_row_at_bound M r bound -> source_prop_base M r -> P r) ->
  (forall r p,source_row_at_bound M r bound -> P p -> source_unary_at M r p bound -> P r) ->
  (forall r p q,source_row_at_bound M r bound -> P p -> P q -> source_full_binary M r p q -> P r) ->
  (forall i r,coding_lt M i (succM M n) -> beta M b c i r ->
    source_row_at_bound M r bound /\ source_justified_at M b c i r bound) ->
  forall i r,coding_lt M i (succM M n) -> beta M b c i r -> P r.
Proof.
  intros HD HB HU HBinary HT.
  enough (H : forall i,coding_lt M i (succM M n) ->
    forall r,beta M b c i r -> P r).
  { intros i r Hi Hr. exact (H i Hi r Hr). }
  apply (definable_strong_induction M _ (proof_line_property_definable M P b c n HD)).
  intros i IH Hi r HR.
  destruct (HT i r Hi HR) as [HBound [HBase|[HUnary|HBin]]].
  - apply HB;[exact HBound|]. exact (proj1 (source_full_trace_base M r) HBase).
  - destruct HUnary as [j [p [Hj [HP HRule]]]].
    apply (HU r p HBound);[|exact HRule].
    exact (IH j Hj (coding_lt_trans M j i (succM M n) Hj Hi) p HP).
  - destruct HBin as [j [k [p [q [Hj [Hk [HP [HQ HRule]]]]]]]].
    apply (HBinary r p q HBound).
    + exact (IH j Hj (coding_lt_trans M j i (succM M n) Hj Hi) p HP).
    + exact (IH k Hk (coding_lt_trans M k i (succM M n) Hk Hi) q HQ).
    + exact (proj1 (source_full_trace_binary M r p q) HRule).
Qed.

Print Assumptions source_bounded_trace_induction.
