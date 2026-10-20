(** A literal ordinal/Cond witness gives ex_cond by ordinary source ExI. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation NumericalContexts NumericalEnvironments NumericalSourceFull SourceDomainInstances SourceOrdinalPredicate
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionExistenceGoal SourcePieceConjunctionBounds
  SourcePieceBoundMaxJoint SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_zfr_reflection_existence_introduction M domain level sb sc n x d ordinal condition body goal implication k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->coding_lt M x k ->coding_lt M d k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_reflection_condition M domain level(source_ordinal_predicate_code M)sb sc n x d condition ->
  sf_relation M SFAnd ordinal condition body ->source_reflection_existence_goal M domain level sb sc n x goal ->
  sf_relation M SFImpl body goal implication ->source_zfr_provable M implication.
Proof.
  intros HD HL HV HX HDk HOrd HCond HBody HGoal HImp.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d ordinal k(source_ordinal_predicate_bounded M)HDk HOrd) as BO.
  pose proof(source_reflection_condition_bounded M domain level(source_ordinal_predicate_code M)sb sc n x d condition k
    HD HL(source_ordinal_predicate_bounded M)HV HX HDk HCond) as BC.
  pose proof(proj2(source_bounded_accept_binary M SFAnd ordinal condition body k(or_introl eq_refl)HBody)(conj BO BC)) as BB.
  pose proof(source_reflection_existence_bounded M domain level sb sc n x goal k HD HL HV HX HGoal) as BG.
  apply(proj1(source_zfr_descriptor_provable M implication)). apply(source_descriptor_provable_from_empty M ZFRSourceDescriptor implication).
  destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M)body) as(b&c&l&HCons).
  pose proof(proj2(context_bounded_cons M(zeroM M)(zeroM M)(zeroM M)body b c l k HCons)
    (conj BB(context_bounded_empty M(zeroM M)(zeroM M)k))) as HC.
  assert(PBody:source_full_prv M b c l body).
  { apply full_source_Ctx;[exists k;auto|]. apply(proj2(context_member_cons M(zeroM M)(zeroM M)(zeroM M)body b c l body HCons)). now left. }
  destruct(source_full_piece_conjunction_components M b c l ordinal condition body HBody PBody) as[PO PC].
  pose proof(source_full_reflection_existence_intro M b c l domain level sb sc n x goal d ordinal condition k
    HD HL HV HX HDk HC HGoal HOrd HCond PO PC) as PG.
  apply(full_source_II M(zeroM M)(zeroM M)(zeroM M)body goal implication b c l);[|exact PG|exact HCons|exact HImp].
  exists k. split;[|apply context_bounded_empty].
  exact(proj2(source_bounded_accept_binary M SFImpl body goal implication k(or_intror(or_intror eq_refl))HImp)(conj BB BG)).
Qed.

Print Assumptions source_zfr_reflection_existence_introduction.
