(** The zero-parameter collection case is the completed actual ZFR
    witness-bound theorem, with its container slot inserted. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
  SourceFiniteCutoffShift SourceHierarchySyntax SourceLFixed SourceOrdinalPredicate SourceCBGoal SourceCBD0Canonical
  SourceWitnessBoundZFR SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_zfr_cb_zero M level phi g ordinal goal implication n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_bounded M phi(succM M n) ->
  coding_lt M g(succM M n) ->numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_cb_goal M(source_L_domain_code M)level(source_ordinal_predicate_code M)(zeroM M)phi goal ->
  sf_relation M SFImpl ordinal goal implication ->source_zfr_provable M implication.
Proof.
  intros HL HB HG HOrd HGoal HImp.
  destruct(source_cutoff_shift_total M 1 phi) as(p1&HC1).
  pose proof(source_cutoff_shift_bounded M 1 phi p1 n HB HC1) as HB1.
  apply(source_zfr_witness_bound M p1 g ordinal goal implication(succM M n)HB1 HG HOrd);[|exact HImp].
  exact(proj1(source_cb_goal_zero_witness M(source_L_domain_code M)level phi p1 goal HL HC1)HGoal).
Qed.

Print Assumptions source_zfr_cb_zero.
