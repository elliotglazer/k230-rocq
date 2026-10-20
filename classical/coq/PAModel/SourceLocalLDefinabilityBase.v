(** Actual local L-definability in every included bounded branch context.
    A genuine finite closed ZFR base is constructed before any ordinal,
    level or parameter-membership assumptions and before eigenvariables.
    The branch consumes the exact internally finite membership block. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull NumericalInstantiation
 SourceRepresentationClosureRecipe SourceDefinabilityBounds SourceEnvInClosureRecipe
 SourceLocalDefinabilityContext SourceLocalDefinabilityProofContext SourceLocalLDefinabilityCanonical
 SourceLDefinableProfile SourceLFixed SourceOrdinalPredicate SourceHierarchySyntax
 SourceMembershipBlocks SourceMembershipBlockProofs SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_bounded code_relation source_L_definable_profile.
Theorem source_local_L_definability_base_total M count phi:
 source_bounded M phi(succM M count) ->exists fb fc fn,
 source_zfr_context M fb fc fn /\
 forall gb gc gn k ordinalName ordinal level block target,
 context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 numerical_instantiation M(source_ordinal_predicate_code M)ordinalName ordinal ->
 source_LL_instance M ordinalName(zeroM M)level ->
 source_membership_block M(code_numeral M 1)(zeroM M)count block ->
 source_full_prv M gb gc gn ordinal ->source_full_prv M gb gc gn level ->source_full_prv M gb gc gn block ->
 source_L_definable_profile M phi target ->source_full_prv M gb gc gn target.
Proof.
 intro BF.
 destruct(source_representation_in_closure_recipe_total M(succM M count)phi)as(repClosure&HRepClosure).
 destruct(source_envf_total M count)as(environment&HE).
 destruct(source_env_in_closure_recipe_total M count environment)as(envClosure&HEnvClosure).
 destruct(source_local_definability_proof_context_total M count phi repClosure environment envClosure BF HRepClosure HE HEnvClosure)
 as(fb&fc&fn&HFixed&PRepClosure&PEnvClosure).
 exists fb,fc,fn. split;[exact(proj1 HFixed)|].
 intros gb gc gn k ordinalName ordinal level block target HIncluded BC HOrdinal HLevel HBlock POrdinal PLevel PBlock HTarget.
 apply(source_full_local_L_definability_canonical M count phi repClosure environment envClosure fb fc fn gb gc gn k
  ordinalName ordinal level target BF HRepClosure HE HEnvClosure HFixed PRepClosure PEnvClosure HIncluded BC HOrdinal HLevel POrdinal PLevel);[|exact HTarget].
 intros i member HI HMember.
 set(K:=addM M k(succM M count)).
 assert(BCK:context_bounded M gb gc gn K).
 { intros f HF. exact(source_bounded_monotone M f k K(BC f HF)(coding_le_add M k(succM M count))). }
 assert(HNames:forall j,coding_lt M j count ->coding_lt M(addM M j(code_numeral M 1))K).
 { intros j HJ. change(coding_lt M(addM M j(succM M(zeroM M)))K).
   rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
   apply(source_bound_lt_le M(succM M j)(succM M count)K(proj2(coding_lt_succ_cancel M j count)HJ)).
   unfold K. rewrite Arithmetic.add_comm. apply coding_le_add. }
 assert(HZero:coding_lt M(zeroM M)K).
 { apply(source_bound_lt_le M(zeroM M)(succM M count)K(coding_zero_lt_succ M count)).
   unfold K. rewrite Arithmetic.add_comm. apply coding_le_add. }
 apply(source_full_membership_block_project M(code_numeral M 1)(zeroM M)count block gb gc gn K i member HNames HZero HBlock BCK PBlock HI).
 change(sf_relation M SFMember(addM M i(succM M(zeroM M)))(zeroM M)member).
 now rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Print Assumptions source_local_L_definability_base_total.
