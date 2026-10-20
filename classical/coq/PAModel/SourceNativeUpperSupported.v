(** Support-normalized actual native upper inference from two ordinary reflection theorems
 at one common carrier, plus the actual internally generated L trace theorem. All finite
 ZFR backgrounds and the pure relativized carrier proof are constructed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceWitnessThetaRecipe SourceUpperWitnessRecipes SourceUpperTraceProfile SourceUpperTraceFrame SourceNativeKRecipes
 SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks SourceDomainCarrierTransport SourceLFixed
 SourceNativePowerCarrierFixed SourceNativeRelativeCarrier SourceNativeRelativePremiseGraphs SourceNativeReflectedCarrierImages
 SourceZeroTransposition SourceRelativization NumericalRenaming NumericalContexts NumericalSourceFull ContextCombination
 SourceZFRProvability SourceTraceBounds SourceProofWeakening SourceClosedContextShift SourceContextTransport
 SourceDomainContexts SourceDomainInstances NumericalInstantiation SourceOrdinalPredicate
 SourceNativeUpperFromReflection SourceNativeLTraceExistence SourceKZFCForwardSchemas BetaExtension Arithmetic
 SourceNativeSupportedTrace SourceNativeSupportedCarrierRule SourceNativeWitnessCarrierRenaming.
Unset Implicit Arguments.
Theorem source_full_native_upper_supported M phi shifted theta n fresh b c
 profile exprofile witness subsetclosed xb pb target relative ie iw iset ix ip re rw rs
 beta s t refl cp ordinal level block sY tY st contained carrier_domain:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M(source_L_domain_code M)(code_numeral M 1)->source_bounded M phi(succM M(succM M n))->
 source_cutoff_shift M 2 phi shifted->source_witness_theta_recipe M phi theta->
 coding_lt M(succM M(succM M n))fresh->source_zero_transposition M fresh b c->
 source_upper_trace_profile M shifted profile->sf_relation M SFEx profile(zeroM M)exprofile->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)(zeroM M)witness->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)fresh iw->
 source_subset_closed_graph M(zeroM M)subsetclosed->source_subset_closed_graph M fresh iset->
 sf_relation M SFMember fresh(zeroM M)xb->sf_relation M SFMember(code_numeral M 1)(zeroM M)pb->
 sf_relation M SFMember(zeroM M)fresh ix->sf_relation M SFMember(code_numeral M 1)fresh ip->
 source_upper_conclusion_recipe M phi target->source_relativization M(source_L_domain_code M)target relative->
 numerical_renaming M exprofile b c(succM M fresh)(zeroM M)ie->
 source_relativization M(source_L_domain_code M)ie re->source_relativization M(source_L_domain_code M)iw rw->
 source_relativization M(source_L_domain_code M)iset rs->
 source_ordinary_reflection M(source_L_domain_code M)(source_succ_iter M 4 n)theta beta refl->
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M 4)
  (code_numeral M(sf_encode source_native_cp_theta))beta cp->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta fresh level->
 source_membership_block M(code_numeral M 2)fresh n block->
 sf_relation M SFMember s fresh sY->sf_relation M SFMember t fresh tY->sf_relation M SFMember s t st->
 source_domain_carrier M(source_L_domain_code M)fresh contained->
 numerical_instantiation M(source_L_domain_code M)fresh carrier_domain->
 forall gb gc gn k db dc,
 context_bounded M gb gc gn k->
 source_domain_context M(source_L_domain_code M)(succM M(succM M n))db dc->
 context_included M db dc(succM M(succM M n))gb gc gn->
 coding_lt M beta k->coding_lt M fresh k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn cp->
 source_full_prv M gb gc gn ordinal->source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->
 source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->
 source_full_prv M gb gc gn contained->source_full_prv M gb gc gn ix->source_full_prv M gb gc gn ip->source_full_prv M gb gc gn carrier_domain->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un relative.
Proof.
 intros LSep LRep HD BP HCut HTheta HF HTrans HProfile HEx HW HW' HS HS' HXB HPB HIX HIP HT HR RE HRE HRW HRS
  HRefl HCP HO HL HBlock HsY HtY Hst HC HDCarrier gb gc gn k db dc BC HDC HDCIn HB HY Hs Ht HNames
  PR PCP PO PL PBlock PsY PtY Pst PC PX PP PY.
 destruct(source_zfr_L_upper_trace_supported M phi shifted n fresh b c profile exprofile ie re
  LSep LRep BP HCut HF HTrans HProfile HEx RE HRE)as(tb&tc&tn&HTC&HTrace).
 destruct(context_union_total M gb gc gn tb tc tn)as(xb'&xc'&xn'&HX).
 pose proof(context_bounded_monotone M tb tc tn(zeroM M)k(source_zfr_context_closed M tb tc tn HTC)
  (coding_zero_lt_succ M k))as BT.
 pose proof(source_context_union_bounded M gb gc gn tb tc tn xb' xc' xn' k HX BC BT)as BX.
 assert(HWeaken:forall f,source_full_prv M gb gc gn f->source_full_prv M xb' xc' xn' f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn xb' xc' xn' f k PF
   (context_union_left M gb gc gn tb tc tn xb' xc' xn' HX)BX). }
 assert(PDom:forall i di,coding_lt M i(succM M(succM M n))->numerical_instantiation M(source_L_domain_code M)i di->source_full_prv M xb' xc' xn' di).
 { intros i di HI HDI. apply HWeaken. apply full_source_Ctx.
   - exists k. split;[|exact BC]. apply(source_domain_instance_bound M(source_L_domain_code M)i di k HD);[|exact HDI].
     exact(coding_lt_trans M i fresh k(coding_lt_trans M i(succM M(succM M n))fresh HI HF)HY).
   - apply HDCIn. apply(proj2(source_domain_context_member_iff M(source_L_domain_code M)(succM M(succM M n))db dc di HDC)). exists i. auto. }
 assert(PYDom:forall di,numerical_instantiation M(source_L_domain_code M)fresh di->source_full_prv M xb' xc' xn' di).
 { intros di HDI. pose proof(numerical_instantiation_functional M(source_L_domain_code M)fresh di carrier_domain HDI HDCarrier)as E.
   subst di. exact(HWeaken _ PY). }
 pose proof(HTrace xb' xc' xn'(ex_intro _ k BX)(context_union_right M gb gc gn tb tc tn xb' xc' xn' HX)PDom PYDom)as PE.
 destruct(source_full_native_reflected_carrier_images M phi shifted theta n beta fresh s t
  refl cp ordinal level block sY tY st iw iset contained rw rs xb' xc' xn' k
  HD BP HCut HTheta HW' HS' BX HB HY Hs Ht HNames HRefl HCP HO HL HBlock HsY HtY Hst HC HRW HRS
  (HWeaken _ PR)(HWeaken _ PCP)(HWeaken _ PO)(HWeaken _ PL)(HWeaken _ PBlock)
  (HWeaken _ PsY)(HWeaken _ PtY)(HWeaken _ Pst)(HWeaken _ PC))as(nb&nc&nn&yb&yc&yn&HNC&HYUnion&PW&PS).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M xb' xc' xn' nb nc nn yb yc yn k HYUnion BX BN)as BY.
 assert(HWeakenY:forall f,source_full_prv M xb' xc' xn' f->source_full_prv M yb yc yn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M xb' xc' xn' yb yc yn f k PF
   (context_union_left M xb' xc' xn' nb nc nn yb yc yn HYUnion)BY). }
 assert(RW:numerical_renaming M witness b c(succM M fresh)(zeroM M)iw).
 { exact(source_native_witness_carrier_transposition M phi shifted n fresh b c witness iw BP HCut HF HTrans HW HW'). }
 assert(RS:numerical_renaming M subsetclosed b c(succM M fresh)(zeroM M)iset).
 { exact(source_subset_closed_carrier_renaming M(zeroM M)subsetclosed fresh iset b c(succM M fresh)(zeroM M)HS HS'
   (source_zero_transposition_zero M fresh b c HTrans)). }
 assert(PResult:source_full_prv M yb yc yn relative).
 { apply(source_full_native_relative_carrier_supported M(source_L_domain_code M)phi shifted n fresh b c
   profile exprofile witness subsetclosed xb pb target relative ie iw iset ix ip re rw rs yb yc yn
   HD BP HCut HF HTrans HProfile HEx HW HS HXB HPB HT HR RE RW RS HIX HIP HRE HRW HRS(ex_intro _ k BY)).
   - intros i di HI HDI. exact(HWeakenY _ (PDom i di HI HDI)).
   - intros di HDI. exact(HWeakenY _ (PYDom di HDI)).
   - exact(HWeakenY _ PE).
   - exact PW.
   - exact PS.
   - exact(HWeakenY _ (HWeaken _ PX)).
   - exact(HWeakenY _ (HWeaken _ PP)). }
 destruct(context_union_total M tb tc tn nb nc nn)as(ab&ac&an&HAUnion).
 assert(HAC:source_zfr_context M ab ac an).
 { intros a HA. apply(proj1(proj2 HAUnion a))in HA. destruct HA as[HA|HA];[exact(HTC a HA)|exact(HNC a HA)]. }
 destruct(context_union_total M gb gc gn ab ac an)as(ub&uc&un&HU).
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k(source_zfr_context_closed M ab ac an HAC)
  (coding_zero_lt_succ M k))as BA.
 pose proof(source_context_union_bounded M gb gc gn ab ac an ub uc un k HU BC BA)as BU.
 assert(HYIn:context_included M yb yc yn ub uc un).
 { intros a HA. apply(proj1(proj2 HYUnion a))in HA. apply(proj2(proj2 HU a)). destruct HA as[HA|HA].
   - apply(proj1(proj2 HX a))in HA. destruct HA as[HA|HA];[now left|right;apply(proj2(proj2 HAUnion a));now left].
   - right. apply(proj2(proj2 HAUnion a)). now right. }
 exists ab,ac,an,ub,uc,un. split;[exact HAC|]. split;[exact HU|].
 exact(source_full_prv_weaken_bounded M yb yc yn ub uc un relative k PResult HYIn BU).
Qed.
Print Assumptions source_full_native_upper_supported.
