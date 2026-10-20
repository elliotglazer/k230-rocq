(** Both substantive native carrier images from actual ordinary reflection
 proofs at one common level. Only generated finite ZFR contexts are added. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceWitnessThetaRecipe SourceUpperTraceFrame SourceUpperWitnessRecipes SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks
 SourceNativeWitnessRelative SourceNativePowerCarrierUse SourceNativePowerCarrierShell SourceNativePowerCarrierFixed SourceDomainCarrierTransport
 SourceLFixed SourceRelativization SourceZFRProvability ContextCombination NumericalContexts NumericalSourceFull
 SourceProofWeakening SourceTraceBounds SourceClosedContextShift NumericalInstantiation SourceOrdinalPredicate.
Unset Implicit Arguments.
Theorem source_full_native_reflected_carrier_images M phi shifted theta n beta carrier s t
 refl cp ordinal level block sY tY st rawW rawS contained relativeW relativeS gb gc gn k:
 source_bounded M(source_L_domain_code M)(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_cutoff_shift M 2 phi shifted->source_witness_theta_recipe M phi theta->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)carrier rawW->source_subset_closed_graph M carrier rawS->
 context_bounded M gb gc gn k->coding_lt M beta k->coding_lt M carrier k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_ordinary_reflection M(source_L_domain_code M)(source_succ_iter M 4 n)theta beta refl->
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M 4)
  (code_numeral M(sf_encode source_native_cp_theta))beta cp->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta carrier level->
 source_membership_block M(code_numeral M 2)carrier n block->
 sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->sf_relation M SFMember s t st->
 source_domain_carrier M(source_L_domain_code M)carrier contained->
 source_relativization M(source_L_domain_code M)rawW relativeW->source_relativization M(source_L_domain_code M)rawS relativeS->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn cp->source_full_prv M gb gc gn ordinal->
 source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->source_full_prv M gb gc gn sY->
 source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->source_full_prv M gb gc gn contained->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un relativeW /\source_full_prv M ub uc un relativeS.
Proof.
 intros HD BP HCut HTheta HW HS BC HB HY Hs Ht HNames HR HCP HO HL HBlock HsY HtY Hst HC HRW HRS
  PR PCP PO PL PBlock PsY PtY Pst PC.
 destruct(source_full_native_witness_relative M(source_L_domain_code M)phi shifted theta n beta carrier s t
  refl level block sY tY st rawW contained relativeW gb gc gn k HD BP HCut HTheta HW BC HB HY Hs Ht HNames
  HR HL HBlock HsY HtY Hst HC HRW PR PL PBlock PsY PtY Pst PC)
  as(wb&wc&wn&xb&xc&xn&HWC&HX&PW).
 pose proof(context_bounded_monotone M wb wc wn(zeroM M)k(source_zfr_context_closed M wb wc wn HWC)
  (coding_zero_lt_succ M k))as BW.
 pose proof(source_context_union_bounded M gb gc gn wb wc wn xb xc xn k HX BC BW)as BX.
 assert(HXProof:forall f,source_full_prv M gb gc gn f->source_full_prv M xb xc xn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn xb xc xn f k PF
   (context_union_left M gb gc gn wb wc wn xb xc xn HX)BX). }
 destruct(source_full_native_cp_subset M beta carrier s t cp ordinal level st sY tY rawS relativeS xb xc xn k
  BX HCP HO HL Hst HsY HtY HS HRS(HXProof _ PCP)(HXProof _ PO)(HXProof _ PL)
  (HXProof _ Pst)(HXProof _ PsY)(HXProof _ PtY))as(sb&sc&sn&yb&yc&yn&HSC&HYUnion&PS).
 destruct(context_union_total M wb wc wn sb sc sn)as(nb&nc&nn&HN).
 assert(HNC:source_zfr_context M nb nc nn).
 { intros a HA. apply(proj1(proj2 HN a))in HA. destruct HA as[HA|HA];[exact(HWC a HA)|exact(HSC a HA)]. }
 destruct(context_union_total M gb gc gn nb nc nn)as(ub&uc&un&HU).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 assert(HXIn:context_included M xb xc xn ub uc un).
 { intros a HA. apply(proj1(proj2 HX a))in HA. apply(proj2(proj2 HU a)).
   destruct HA as[HA|HA];[now left|right;apply(proj2(proj2 HN a));now left]. }
 assert(HYIn:context_included M yb yc yn ub uc un).
 { intros a HA. apply(proj1(proj2 HYUnion a))in HA. destruct HA as[HA|HA].
   - exact(HXIn a HA).
   - apply(proj2(proj2 HU a)). right. apply(proj2(proj2 HN a)). now right. }
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|]. split.
 - exact(source_full_prv_weaken_bounded M xb xc xn ub uc un relativeW k PW HXIn BU).
 - exact(source_full_prv_weaken_bounded M yb yc yn ub uc un relativeS k PS HYIn BU).
Qed.
Print Assumptions source_full_native_reflected_carrier_images.
