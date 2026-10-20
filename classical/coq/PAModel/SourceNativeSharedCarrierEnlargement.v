(** Enlarge an actual common L-level to one shared reflecting carrier.
 Positive selector witnesses are original element zero and the old carrier.
 Their membership, the entire new parameter block, and both reflections are
 actual source proofs. No pair-existence or shared-carrier premise is added. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceCommonLevelPoint SourceMembershipBlocks SourceMembershipBlockProofs SourceNativeCarrierMembers
 SourcePCSTables SourcePieceConjunctionBounds SourceHierarchySyntax SourceLFixed SourceOrdinaryReflectionSyntax
 SourceReflectionGeometryPoint SourceSharedGeometryReflectionsUse SourceHierarchyStrictUse SourceRawSubset
 SourceOrdinalPredicate NumericalInstantiation NumericalContexts NumericalSourceFull ContextCombination
 SourceTraceBounds SourceClosedContextShift SourceProofWeakening SourceConjunctionRules SourceNativeContextExtension SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_full_native_shared_carrier_enlargement M level sb sc pieces pb pc pn qb qc qn phi pcount psi qcount
 count seed oldY K beta Y common geometry newLevel reflP reflQ fullBlock inLevel subset st gb gc gn k:
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_bounded M phi pcount->source_pcs_table M(source_L_domain_code M)phi pcount pb pc pn->
 source_bounded M psi qcount->source_pcs_table M(source_L_domain_code M)psi qcount qb qc qn->
 source_piece_table_valid M sb sc pieces->context_included M pb pc pn sb sc pieces->context_included M qb qc qn sb sc pieces->
 coding_lt M(zeroM M)count->(forall i,coding_lt M i count->coding_lt M i k)->
 coding_lt M oldY k->coding_lt M Y k->context_bounded M gb gc gn k->
 source_common_level_point M(zeroM M)count seed oldY common->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc pieces seed K beta geometry->
 source_LL_instance M beta Y newLevel->source_ordinary_reflection M(source_L_domain_code M)pcount phi beta reflP->
 source_ordinary_reflection M(source_L_domain_code M)qcount psi beta reflQ->
 source_membership_block M(zeroM M)Y count fullBlock->sf_relation M SFMember oldY Y inLevel->
 source_raw_subset_graph M oldY Y subset->sf_relation M SFMember(zeroM M)oldY st->
 source_full_prv M gb gc gn common->source_full_prv M gb gc gn geometry->source_full_prv M gb gc gn newLevel->
 exists nb nc nn ub uc un ordinal,
 source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\
 source_full_prv M ub uc un reflP /\source_full_prv M ub uc un reflQ /\source_full_prv M ub uc un ordinal /\
 source_full_prv M ub uc un newLevel /\source_full_prv M ub uc un fullBlock /\
 source_full_prv M ub uc un inLevel /\source_full_prv M ub uc un st.
Proof.
 intros BL HL BP HPT BQ HQT HV HPIn HQIn H0 HNames BOld BY BC HCommon HG HNew HRP HRQ HBLock HIn HSubset Hst PCommon PG PNew.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)beta)as(ordinal&HO).
 destruct(sf_relation_total M SFMember seed beta)as(member&HM).
 destruct(source_full_shared_geometry_reflections M level sb sc pieces pb pc pn qb qc qn phi pcount psi qcount seed K beta
  geometry reflP reflQ ordinal member gb gc gn k BL HL BP HPT BQ HQT HV HPIn HQIn HG HRP HRQ HO HM BC PG)
  as(rb&rc&rn&xb&xc&xn&HRC&HX&PRP&PRQ&PO&PM).
 pose proof(context_bounded_monotone M rb rc rn(zeroM M)k(source_zfr_context_closed M rb rc rn HRC)(coding_zero_lt_succ M k))as BR.
 pose proof(source_context_union_bounded M gb gc gn rb rc rn xb xc xn k HX BC BR)as BX.
 assert(WX:forall f,source_full_prv M gb gc gn f->source_full_prv M xb xc xn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn xb xc xn f k PF(context_union_left M gb gc gn rb rc rn xb xc xn HX)BX). }
 destruct HCommon as(oldBlock&oldOrdinal&oldLevel&oldPair&HOldBlock&HOldOrdinal&HOldLevel&HOldPair&HCommon).
 pose proof(source_full_conjunction_left M gb gc gn oldPair oldBlock common HCommon PCommon)as POldPair.
 pose proof(source_full_conjunction_left M gb gc gn oldOrdinal oldLevel oldPair HOldPair POldPair)as POldOrdinal.
 pose proof(source_full_conjunction_right M gb gc gn oldOrdinal oldLevel oldPair HOldPair POldPair)as POldLevel.
 pose proof(source_full_conjunction_right M gb gc gn oldPair oldBlock common HCommon PCommon)as POldBlock.
 destruct(source_full_hierarchy_strict M seed beta oldY Y oldOrdinal ordinal member oldLevel newLevel inLevel subset xb xc xn k
  BX HOldOrdinal HO HM HOldLevel HNew HIn HSubset(WX _ POldOrdinal)PO PM(WX _ POldLevel)(WX _ PNew))
  as(sb'&sc'&sn'&yb&yc&yn&HSC&HY&PIn&PSubset).
 pose proof(context_bounded_monotone M sb' sc' sn'(zeroM M)k(source_zfr_context_closed M sb' sc' sn' HSC)(coding_zero_lt_succ M k))as BS.
 pose proof(source_context_union_bounded M xb xc xn sb' sc' sn' yb yc yn k HY BX BS)as BNew.
 assert(WY:forall f,source_full_prv M xb xc xn f->source_full_prv M yb yc yn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M xb xc xn yb yc yn f k PF(context_union_left M xb xc xn sb' sc' sn' yb yc yn HY)BNew). }
 assert(HAddNames:forall i,coding_lt M i count->coding_lt M(addM M i(zeroM M))k).
 { intros i HI. rewrite coding_add_zero_r. exact(HNames i HI). }
 pose proof(source_full_membership_block_carrier M(zeroM M)oldY Y count oldBlock fullBlock subset yb yc yn k
  HAddNames BOld BY BNew HOldBlock HBLock HSubset(WY _ (WX _ POldBlock))PSubset)as PFullBlock.
 assert(Pst:source_full_prv M yb yc yn st).
 { apply(source_full_membership_block_project M(zeroM M)oldY count oldBlock yb yc yn k(zeroM M)st
    HAddNames BOld HOldBlock BNew(WY _ (WX _ POldBlock))H0).
   rewrite coding_add_zero_r. exact Hst. }
 destruct(source_native_closed_extensions M gb gc gn rb rc rn xb xc xn sb' sc' sn' yb yc yn HRC HX HSC HY)
  as(nb&nc&nn&ub&uc&un&HNC&HU&HIncluded).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 assert(WF:forall f,source_full_prv M yb yc yn f->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M yb yc yn ub uc un f k PF HIncluded BU). }
 exists nb,nc,nn,ub,uc,un,ordinal. split;[exact HNC|]. split;[exact HU|]. split;[exact HO|].
 split;[exact(WF _ (WY _ PRP))|]. split;[exact(WF _ (WY _ PRQ))|]. split;[exact(WF _ (WY _ PO))|].
 split;[exact(WF _ (WY _ (WX _ PNew)))|]. split;[exact(WF _ PFullBlock)|]. split;[exact(WF _ PIn)|exact(WF _ Pst)].
Qed.
Print Assumptions source_full_native_shared_carrier_enlargement.
