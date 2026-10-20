(** Discharge the fixed hierarchy-law premises from the positive request.
    The resulting ZFR implication has an arbitrary internal matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalInstantiation NumericalSourceFull SourceSequents
  SourceConjunctionRules SourceProofWeakening SourceLeastOrdinalWitness SourceTraceBounds
  SourceDomainInstances SourceOrdinalPredicate SourceHierarchySyntax SourceD0At SourcePositiveWitnessPlan
  SourcePositiveWitnessRequest SourceFiniteProofContexts SourceDescriptorProvability SourceSetTheoryDescriptors
  SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_positive_witness_antecedent M ordinal known member instance body :=exists pair inner,
  sf_relation M SFAnd ordinal known pair /\sf_relation M SFAnd pair member inner /\
  sf_relation M SFAnd inner instance body.

Theorem source_zfr_positive_witness_request M domain phi d y carrier ordinal known member instance
    request body implication k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  coding_lt M d k ->coding_lt M y k ->coding_lt M carrier k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_LL_instance M d carrier known ->sf_relation M SFMember y carrier member ->
  numerical_instantiation M phi y instance ->source_d0_at M domain phi d request ->
  source_positive_witness_antecedent M ordinal known member instance body ->
  sf_relation M SFImpl body request implication ->source_zfr_provable M implication.
Proof.
  intros HD HB HDB HYB HCB HOrd HKnown HMember HInstance HRequest(pair&inner&HPair&HInner&HBody)HImp.
  destruct(source_positive_witness_plan_total M d y carrier) as(allUnique&allMove&HPlan&PAU&PAM).
  assert(Premises:forall f,In f[allUnique;allMove] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f[<-|[<-|[]]];apply(proj2(source_zfr_descriptor_provable M _));assumption. }
  destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises) as(b&c&n&HC&P).
  assert(HCtx:context_bounded M b c n k).
  { exact(context_bounded_monotone M b c n(zeroM M)k(proj1 HC)(coding_zero_lt_succ M k)). }
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k
    (source_ordinal_predicate_bounded M)HDB HOrd) as HOrdinalBound.
  pose proof(source_LL_instance_bounded M d carrier known k HDB HCB HKnown) as HKnownBound.
  assert(HMemberBound:source_bounded M member k).
  { apply(proj2(source_bounded_accept_atom M SFMember y carrier member k(or_introl eq_refl)HMember)). auto. }
  pose proof(numerical_instantiation_bounded M phi y instance k HB HYB HInstance) as HInstanceBound.
  pose proof(source_d0_at_bounded M domain phi d request k HD HB HDB HRequest) as HRequestBound.
  assert(HPairBound:source_bounded M pair k).
  { exact(proj2(source_bounded_accept_binary M SFAnd ordinal known pair k(or_introl eq_refl)HPair)
      (conj HOrdinalBound HKnownBound)). }
  assert(HInnerBound:source_bounded M inner k).
  { exact(proj2(source_bounded_accept_binary M SFAnd pair member inner k(or_introl eq_refl)HInner)
      (conj HPairBound HMemberBound)). }
  assert(HBodyBound:source_bounded M body k).
  { exact(proj2(source_bounded_accept_binary M SFAnd inner instance body k(or_introl eq_refl)HBody)
      (conj HInnerBound HInstanceBound)). }
  destruct(environment_cons_total M b c n body) as(ub&uc&un&HCons).
  assert(HBranch:context_bounded M ub uc un k).
  { exact(proj2(context_bounded_cons M b c n body ub uc un k HCons)(conj HBodyBound HCtx)). }
  assert(PBody:source_full_prv M ub uc un body).
  { apply full_source_Ctx;[exists k;auto|].
    apply(proj2(context_member_cons M b c n body ub uc un body HCons)). now left. }
  pose proof(source_full_conjunction_left M ub uc un inner instance body HBody PBody) as PInner.
  pose proof(source_full_conjunction_right M ub uc un inner instance body HBody PBody) as PInstance.
  pose proof(source_full_conjunction_left M ub uc un pair member inner HInner PInner) as PPair.
  pose proof(source_full_conjunction_right M ub uc un pair member inner HInner PInner) as PMember.
  pose proof(source_full_conjunction_left M ub uc un ordinal known pair HPair PPair) as POrdinal.
  pose proof(source_full_conjunction_right M ub uc un ordinal known pair HPair PPair) as PKnown.
  assert(PUnique:source_full_prv M ub uc un allUnique).
  { exact(source_full_prv_weaken_bounded M b c n ub uc un allUnique k(P allUnique ltac:(cbn;tauto))
      (source_cons_tail_inclusion M b c n body ub uc un HCons)HBranch). }
  assert(PMove:source_full_prv M ub uc un allMove).
  { exact(source_full_prv_weaken_bounded M b c n ub uc un allMove k(P allMove ltac:(cbn;tauto))
      (source_cons_tail_inclusion M b c n body ub uc un HCons)HBranch). }
  pose proof(source_full_positive_witness_request M ub uc un domain phi d y carrier ordinal known member
    instance request allUnique allMove k HD HB HBranch HDB HYB HCB HOrd HKnown HMember HInstance HRequest
    HPlan POrdinal PKnown PMember PInstance PUnique PMove) as PRequest.
  exists b,c,n. split;[exact(proj1(source_zfr_descriptor_context M b c n)HC)|].
  apply(full_source_II M b c n body request implication ub uc un);try assumption.
  exists k. split;[|exact HCtx].
  exact(proj2(source_bounded_accept_binary M SFImpl body request implication k
    (or_intror(or_intror eq_refl))HImp)(conj HBodyBound HRequestBound)).
Qed.

Print Assumptions source_zfr_positive_witness_request.
