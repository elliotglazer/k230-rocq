(** Consume the actual L_common theorem under an exact model-valued L-domain
    table. This supplies an ordinary source proof and keeps its actual finite
    ZFR axiom context visible for subsequent witness elimination. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceTraceBounds NumericalContexts NumericalSourceFull SourceDomainContexts SourceDomainInstances
  SourcePredicateBlocks SourcePredicateBlockProofs SourceCommonLevelRecipe SourceCommonLevelInduction
  SourceLFixed SourceZFRProvability SourceProofWeakening SourceDerivedRules ContextCombination SourceClosedContextShift.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_zfr_common_level_domain_context M start count width db dc target :
  source_domain_context M(source_L_domain_code M)width db dc ->
  (forall i,coding_lt M i count ->coding_lt M(addM M i start)width) ->
  source_common_level_recipe M start count target ->
  exists ab ac an b c n,
    source_zfr_context M ab ac an /\context_union M ab ac an db dc width b c n /\source_full_prv M b c n target.
Proof.
  intros HDomain HNames HTarget.
  destruct(source_predicate_block_total M start(source_L_domain_code M)count) as(block&HBlock).
  destruct(sf_relation_total M SFImpl block target) as(law&HLaw).
  destruct(source_zfr_common_level_from_L_parameters M start count block target law HBlock HTarget HLaw)
    as(ab&ac&an&HAC&PLaw).
  destruct(context_union_total M ab ac an db dc width) as(b&c&n&HUnion).
  pose proof(source_zfr_context_closed M ab ac an HAC) as HAClosed.
  pose proof(context_bounded_monotone M ab ac an(zeroM M)width HAClosed(coding_zero_lt_succ M width)) as HAB.
  pose proof(source_domain_context_bounded M(source_L_domain_code M)width db dc(numerical_L_domain_bounded M)HDomain) as HDB.
  pose proof(source_context_union_bounded M ab ac an db dc width b c n width HUnion HAB HDB) as HC.
  pose proof(context_union_left M ab ac an db dc width b c n HUnion) as HLeft.
  pose proof(context_union_right M ab ac an db dc width b c n HUnion) as HRight.
  assert(PBlock:source_full_prv M b c n block).
  { apply(source_full_predicate_block_intro M start(source_L_domain_code M)count block b c n width
      HNames(numerical_L_domain_bounded M)HBlock HC).
    intros i f HI HF. apply full_source_Ctx.
    - exists width. split;[exact(source_domain_instance_bound M(source_L_domain_code M)(addM M i start)f width
        (numerical_L_domain_bounded M)(HNames i HI)HF)|exact HC].
    - apply HRight. apply(proj2(source_domain_context_member_iff M(source_L_domain_code M)width db dc f HDomain)).
      exists(addM M i start). split;[exact(HNames i HI)|exact HF]. }
  pose proof(source_full_prv_weaken_bounded M ab ac an b c n law width PLaw HLeft HC) as PLaw'.
  exists ab,ac,an,b,c,n. split;[exact HAC|]. split;[exact HUnion|].
  exact(source_full_modus_ponens M b c n block target law HLaw PLaw' PBlock).
Qed.
Print Assumptions source_zfr_common_level_domain_context.
