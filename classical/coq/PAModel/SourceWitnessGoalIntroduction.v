(** Choose an actual ordinal witness for the existential bound statement. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts
  NumericalInstantiation NumericalSourceFull SourceInstantiationConstructors SourceConjunctionRules
  SourceOrdinalPredicate SourceD0At SourceD0Instances SourceWitnessBoundGoal SourceOrdinalCollectorShell.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_witness_goal_introduction M b c n domain phi d ordinal request goal k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->source_d0_at M domain phi d request ->
  source_witness_bound_goal M domain phi goal ->source_full_prv M b c n ordinal ->
  source_full_prv M b c n request ->source_full_prv M b c n goal.
Proof.
  intros HD HB HOrd HRequest HGoal POrd PRequest.
  pose proof(source_witness_bound_goal_bounded M domain phi goal k HD HB HGoal) as HGoalBound.
  destruct HGoal as(shifted&d0&body&HC&HD0&HBody&HEx).
  pose proof(source_d0_at_witness_instantiation M domain phi shifted d0 request d(succM M k)
    HD HB HC HD0 HRequest) as HInstD0.
  destruct(sf_relation_total M SFAnd ordinal request) as(witness&HW).
  pose proof(source_instantiation_binary M SFAnd(source_ordinal_predicate_code M)d0 body d ordinal request witness
    (or_introl eq_refl)HBody HOrd HInstD0 HW) as HInst.
  assert(PWitness:source_full_prv M b c n witness).
  { exact(full_source_CI M b c n ordinal request witness
      (source_wf_binary M b c n SFAnd ordinal request witness(or_introl eq_refl)HW
        (source_full_prv_wellformed M b c n ordinal POrd)(source_full_prv_wellformed M b c n request PRequest))
      POrd PRequest HW). }
  destruct(source_full_prv_wellformed M b c n ordinal POrd) as(bound&HOB&HCtx).
  exact(full_source_ExI M b c n body goal d witness
    (source_oc_sequent_two_bounds M b c n goal k bound HGoalBound HCtx)PWitness HEx HInst).
Qed.

Print Assumptions source_full_witness_goal_introduction.
