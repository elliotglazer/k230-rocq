(** Actual negative branch of the witness-bound theorem, including the
    choice of its ordinal and its existential source proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceSequents
  NumericalContexts NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceConjunctionRules
  SourceInstantiationConstructors SourceOrdinalPredicate SourceD0At SourceD0Instances SourceD0Recipe
  SourceWitnessBoundGoal SourceWitnessNegative SourceRelativizationRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_negative_witness_bound M b c n domain phi test neg g og goal k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  context_bounded M b c n k ->coding_lt M g k ->
  sr_quantifier M false domain phi test ->sf_relation M SFImpl test(zeroM M)neg ->
  numerical_instantiation M(source_ordinal_predicate_code M)g og ->
  source_witness_bound_goal M domain phi goal ->
  source_full_prv M b c n og ->source_full_prv M b c n neg ->source_full_prv M b c n goal.
Proof.
  intros HD HB HCtx HG HT HN HOrd HGoal POrd PNeg.
  destruct HGoal as(shifted&d0&body&HC&HD0&HBody&HEx).
  destruct(source_d0_at_total M domain phi g) as(request&HRequest).
  pose proof(source_d0_at_bounded M domain phi g request k HD HB HG HRequest) as HRequestBound.
  destruct HRequest as(s&level&ew&point&HShift&HLevel&HEw&HPoint&HAll).
  assert(PRequest:source_full_prv M b c n request).
  { exact(source_full_no_witness_request M b c n domain phi s test neg level ew point request
      HD HShift HT HN HEw HPoint HAll(ex_intro _ k(conj HRequestBound HCtx))PNeg). }
  assert(HRequest:source_d0_at M domain phi g request).
  { exists s,level,ew,point. repeat split;assumption. }
  pose proof(source_d0_at_witness_instantiation M domain phi shifted d0 request g(succM M k)
    HD HB HC HD0 HRequest) as HInstD0.
  destruct(sf_relation_total M SFAnd og request) as(witness&HW).
  pose proof(source_instantiation_binary M SFAnd(source_ordinal_predicate_code M)d0 body g og request witness
    (or_introl eq_refl)HBody HOrd HInstD0 HW) as HInst.
  assert(PWitness:source_full_prv M b c n witness).
  { exact(full_source_CI M b c n og request witness
      (source_wf_binary M b c n SFAnd og request witness(or_introl eq_refl)HW
        (source_full_prv_wellformed M b c n og POrd)(source_full_prv_wellformed M b c n request PRequest))
      POrd PRequest HW). }
  apply(full_source_ExI M b c n body goal g witness);try assumption.
  exists k. split;[|exact HCtx].
  apply(source_witness_bound_goal_bounded M domain phi goal k HD HB).
  exists shifted,d0,body. repeat split;assumption.
Qed.

Print Assumptions source_full_negative_witness_bound.
