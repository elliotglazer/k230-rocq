(** Actual native witness_closed image from one ordinary reflection
 theorem and literal carrier geometry. Every selector, input/output
 quantifier and finite ZFR background is constructed in the proof. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceWitnessThetaRecipe SourceUpperWitnessRecipes SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks
 SourceNativeWitnessClosure SourceNativeRelativeWitness SourceDomainCarrierTransport SourceRelativization
 SourceZFRProvability ContextCombination NumericalContexts NumericalSourceFull SourceProofWeakening
 SourceTraceBounds SourceClosedContextShift.
Unset Implicit Arguments.
Theorem source_full_native_witness_relative M domain phi shifted theta n beta carrier s t
 refl level block sY tY st raw contained relative gb gc gn k:
 source_bounded M domain(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_cutoff_shift M 2 phi shifted->source_witness_theta_recipe M phi theta->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)carrier raw->
 context_bounded M gb gc gn k->coding_lt M beta k->coding_lt M carrier k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_ordinary_reflection M domain(source_succ_iter M 4 n)theta beta refl->source_LL_instance M beta carrier level->
 source_membership_block M(code_numeral M 2)carrier n block->
 sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->sf_relation M SFMember s t st->
 source_domain_carrier M domain carrier contained->source_relativization M domain raw relative->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->
 source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->source_full_prv M gb gc gn contained->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un relative.
Proof.
 intros HD BP HCut HTheta HRaw BC HB HY HS HT HNames HR HL HBlock HSY HTY HST HContained HRelative PR PL PBlock PSY PTY PST PContained.
 destruct(source_full_native_reflected_witness_closure M domain phi shifted theta n beta carrier s t refl level block sY tY st raw gb gc gn k
  HD BP HCut HTheta HRaw BC HB HY HS HT HNames HR HL HBlock HSY HTY HST PR PL PBlock PSY PTY PST)
  as(matrix&reflectedAll&nb&nc&nn&ub&uc&un&HRawMatrix&BMatrix&HReflected&HNC&HU&PReflected).
 pose proof(source_zfr_context_closed M nb nc nn HNC)as BN0.
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k BN0(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 pose proof(source_full_prv_weaken_bounded M gb gc gn ub uc un contained k PContained
  (context_union_left M gb gc gn nb nc nn ub uc un HU)BU)as PContainedU.
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|].
 exact(source_full_native_relative_witness_closed M domain carrier matrix raw reflectedAll contained relative ub uc un k
  HD BMatrix HY BU HRawMatrix HReflected HContained HRelative PReflected PContainedU).
Qed.
Print Assumptions source_full_native_witness_relative.
