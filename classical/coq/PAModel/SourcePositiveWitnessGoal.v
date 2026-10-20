(** The actual positive witness theorem, with the ordinal existential
    introduced and all fixed mathematical laws discharged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalInstantiation NumericalSourceFull SourceDerivedRules
  SourceConjunctionRules SourceProofWeakening SourceLeastOrdinalWitness SourceOrdinalPredicate SourceHierarchySyntax
  SourceD0At SourcePositiveWitnessZFR SourceWitnessGoalIntroduction SourceWitnessBoundGoal SourceZFRProvability
  SourceInstantiationConstructors SourceOrdinalCollectorShell.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_positive_witness_goal M domain phi d y carrier ordinal known member instance
    body goal implication k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  coding_lt M d k ->coding_lt M y k ->coding_lt M carrier k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_LL_instance M d carrier known ->sf_relation M SFMember y carrier member ->
  numerical_instantiation M phi y instance ->
  source_positive_witness_antecedent M ordinal known member instance body ->
  source_witness_bound_goal M domain phi goal ->sf_relation M SFImpl body goal implication ->
  source_zfr_provable M implication.
Proof.
  intros HD HB HDB HYB HCB HOrd HKnown HMember HInstance HBody HGoal HImp.
  destruct(source_d0_at_total M domain phi d) as(request&HRequest).
  destruct(sf_relation_total M SFImpl body request) as(requestImp&HRequestImp).
  pose proof(source_zfr_positive_witness_request M domain phi d y carrier ordinal known member instance
    request body requestImp k HD HB HDB HYB HCB HOrd HKnown HMember HInstance HRequest HBody HRequestImp)
    as PRequestImp.
  destruct PRequestImp as(b&c&n&HC&PP).
  destruct(source_full_prv_wellformed M b c n requestImp PP) as(bound&HImpBound&HCtx).
  destruct(proj1(source_bounded_accept_binary M SFImpl body request requestImp bound
    (or_intror(or_intror eq_refl))HRequestImp)HImpBound) as(HBodyBound&HRequestBound).
  destruct(environment_cons_total M b c n body) as(ub&uc&un&HCons).
  assert(HBranch:context_bounded M ub uc un bound).
  { exact(proj2(context_bounded_cons M b c n body ub uc un bound HCons)(conj HBodyBound HCtx)). }
  assert(PBody:source_full_prv M ub uc un body).
  { apply full_source_Ctx;[exists bound;auto|].
    apply(proj2(context_member_cons M b c n body ub uc un body HCons)). now left. }
  assert(PRequest:source_full_prv M ub uc un request).
  { exact(source_full_modus_ponens M ub uc un body request requestImp HRequestImp
      (source_full_prv_weaken_bounded M b c n ub uc un requestImp bound PP
        (source_cons_tail_inclusion M b c n body ub uc un HCons)HBranch)PBody). }
  destruct HBody as(pair&inner&HPair&HInner&HBodyCode).
  pose proof(source_full_conjunction_left M ub uc un inner instance body HBodyCode PBody) as PInner.
  pose proof(source_full_conjunction_left M ub uc un pair member inner HInner PInner) as PPair.
  pose proof(source_full_conjunction_left M ub uc un ordinal known pair HPair PPair) as POrdinal.
  pose proof(source_full_witness_goal_introduction M ub uc un domain phi d ordinal request goal k
    HD HB HOrd HRequest HGoal POrdinal PRequest) as PGoal.
  exists b,c,n. split;[exact HC|].
  apply(full_source_II M b c n body goal implication ub uc un);try assumption.
  apply(source_wf_binary M b c n SFImpl body goal implication(or_intror(or_intror eq_refl))HImp).
  - exists bound;auto.
  - destruct(source_full_prv_wellformed M ub uc un goal PGoal) as(gbound&HG&HBG).
    exact(SourceOrdinalCollectorShell.source_oc_sequent_two_bounds M b c n goal gbound bound HG HCtx).
Qed.

Print Assumptions source_zfr_positive_witness_goal.
