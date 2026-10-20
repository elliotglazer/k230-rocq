(** The no-witness implication is already derivable in empty source logic;
    its ordinal and negative-existence assumptions are discharged here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts
  NumericalEnvironments NumericalInstantiation NumericalSourceFull SourceInstantiationConstructors SourceOrdinalPredicate
  SourceD0Recipe SourceWitnessBoundGoal SourceWitnessBoundNegative SourceRelativizationRules SourceRelativizationBounds
  SourceDomainInstances SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_witness_bound_negative M domain phi g ordinal test neg goal target result k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->coding_lt M g k ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  sr_quantifier M false domain phi test ->sf_relation M SFImpl test(zeroM M)neg ->
  source_witness_bound_goal M domain phi goal ->sf_relation M SFImpl ordinal goal target ->
  sf_relation M SFImpl neg target result ->source_zfr_provable M result.
Proof.
  intros HD HB HG HOrd HTest HNeg HGoal HTarget HResult.
  pose proof(source_guarded_exists_bounded M domain phi test k(sr_domain_bound_succ M domain k HD)HB HTest) as HTestB.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal k
    (source_ordinal_predicate_bounded M)HG HOrd) as HOrdinalB.
  pose proof(source_witness_bound_goal_bounded M domain phi goal k HD HB HGoal) as HGoalB.
  assert(HNegB:source_bounded M neg k).
  { exact(proj2(source_bounded_accept_binary M SFImpl test(zeroM M)neg k
      (or_intror(or_intror eq_refl))HNeg)(conj HTestB(source_bounded_accept_falsity M k))). }
  assert(HTargetB:source_bounded M target k).
  { exact(proj2(source_bounded_accept_binary M SFImpl ordinal goal target k
      (or_intror(or_intror eq_refl))HTarget)(conj HOrdinalB HGoalB)). }
  assert(HResultB:source_bounded M result k).
  { exact(proj2(source_bounded_accept_binary M SFImpl neg target result k
      (or_intror(or_intror eq_refl))HResult)(conj HNegB HTargetB)). }
  destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)neg) as(b&c&n&HConsNeg).
  assert(HNegCtx:context_bounded M b c n k).
  { exact(proj2(context_bounded_cons M(zeroM M)(zeroM M)(zeroM M)neg b c n k HConsNeg)
      (conj HNegB(context_bounded_empty M(zeroM M)(zeroM M)k))). }
  destruct(environment_cons_total M b c n ordinal) as(ub&uc&un&HConsOrdinal).
  assert(HBranch:context_bounded M ub uc un k).
  { exact(proj2(context_bounded_cons M b c n ordinal ub uc un k HConsOrdinal)(conj HOrdinalB HNegCtx)). }
  assert(POrdinal:source_full_prv M ub uc un ordinal).
  { apply full_source_Ctx;[exists k;auto|].
    apply(proj2(context_member_cons M b c n ordinal ub uc un ordinal HConsOrdinal)). now left. }
  assert(PNeg:source_full_prv M ub uc un neg).
  { apply full_source_Ctx;[exists k;auto|].
    apply(proj2(context_member_cons M b c n ordinal ub uc un neg HConsOrdinal)). right.
    apply(proj2(context_member_cons M(zeroM M)(zeroM M)(zeroM M)neg b c n neg HConsNeg)). now left. }
  pose proof(source_full_negative_witness_bound M ub uc un domain phi test neg g ordinal goal k
    HD HB HBranch HG HTest HNeg HOrd HGoal POrdinal PNeg) as PGoal.
  pose proof(full_source_II M b c n ordinal goal target ub uc un(ex_intro _ k(conj HTargetB HNegCtx))
    PGoal HConsOrdinal HTarget) as PTarget.
  apply(proj1(source_zfr_descriptor_provable M result)).
  apply(source_descriptor_provable_from_empty M ZFRSourceDescriptor result).
  exact(full_source_II M(zeroM M)(zeroM M)(zeroM M)neg target result b c n
    (ex_intro _ k(conj HResultB(context_bounded_empty M(zeroM M)(zeroM M)k)))PTarget HConsNeg HResult).
Qed.

Print Assumptions source_zfr_witness_bound_negative.
