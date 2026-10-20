(** Actual native upper inference from two ordinary reflection theorems
 at one common carrier, plus the actual relative trace theorem. All finite
 ZFR backgrounds and the pure relativized carrier proof are constructed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceWitnessThetaRecipe SourceUpperWitnessRecipes SourceUpperTraceProfile SourceUpperTraceFrame SourceNativeKRecipes
 SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks SourceDomainCarrierTransport SourceLFixed
 SourceNativePowerCarrierFixed SourceNativeRelativeCarrier SourceNativeRelativePremiseGraphs SourceNativeReflectedCarrierImages
 SourceZeroTransposition SourceRelativization NumericalRenaming NumericalContexts NumericalSourceFull ContextCombination
 SourceZFRProvability SourceTraceBounds SourceProofWeakening SourceClosedContextShift SourceContextTransport
 SourceDomainContexts SourceDomainInstances NumericalInstantiation SourceOrdinalPredicate.
Unset Implicit Arguments.
Theorem source_full_native_upper_from_reflection M phi shifted theta n fresh b c
 profile exprofile witness subsetclosed xb pb target relative ie iw iset ix ip re rw rs
 beta s t refl cp ordinal level block sY tY st contained:
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
 exists bound,forall gb gc gn k db dc,
 coding_lt M bound(succM M k)->context_bounded M gb gc gn k->
 source_domain_context M(source_L_domain_code M)k db dc->context_included M db dc k gb gc gn->
 coding_lt M beta k->coding_lt M fresh k->coding_lt M s k->coding_lt M t k->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_full_prv M gb gc gn re->source_full_prv M gb gc gn refl->source_full_prv M gb gc gn cp->
 source_full_prv M gb gc gn ordinal->source_full_prv M gb gc gn level->source_full_prv M gb gc gn block->
 source_full_prv M gb gc gn sY->source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->
 source_full_prv M gb gc gn contained->source_full_prv M gb gc gn ix->source_full_prv M gb gc gn ip->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\
 source_full_prv M ub uc un relative.
Proof.
 intros HD BP HCut HTheta HF HTrans HProfile HEx HW HW' HS HS' HXB HPB HIX HIP HT HR RE HRE HRW HRS
  HRefl HCP HO HL HBlock HsY HtY Hst HC.
 pose proof(source_native_relative_premise_graphs M(source_L_domain_code M)phi shifted n fresh b c
  exprofile witness subsetclosed xb pb ie iw iset ix ip re rw rs BP HCut HF HTrans HW HW' HS HS'
  HXB HPB HIX HIP RE HRE HRW HRS)as HImages.
 destruct(source_full_native_relative_carrier M(source_L_domain_code M)phi shifted n fresh b c
  profile exprofile witness subsetclosed xb pb target relative re rw rs ix ip
  HD BP HCut HF HTrans HProfile HEx HW HS HXB HPB HT HR HImages)as(bound&HApply).
 exists bound. intros gb gc gn k db dc HBound BC HDC HDCIn HB HY Hs Ht HNames
  PE PR PCP PO PL PBlock PsY PtY Pst PC PX PP.
 destruct(source_full_native_reflected_carrier_images M phi shifted theta n beta fresh s t
  refl cp ordinal level block sY tY st iw iset contained rw rs gb gc gn k
  HD BP HCut HTheta HW' HS' BC HB HY Hs Ht HNames HRefl HCP HO HL HBlock HsY HtY Hst HC HRW HRS
  PR PCP PO PL PBlock PsY PtY Pst PC)as(nb&nc&nn&ub&uc&un&HNC&HU&PW&PS).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)
  (coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 assert(HWeaken:forall f,source_full_prv M gb gc gn f->source_full_prv M ub uc un f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn ub uc un f k PF
   (context_union_left M gb gc gn nb nc nn ub uc un HU)BU). }
 assert(PD:forall i di,coding_lt M i k->numerical_instantiation M(source_L_domain_code M)i di->source_full_prv M ub uc un di).
 { intros i di HI HDI. apply full_source_Ctx.
   - exists k. split;[exact(source_domain_instance_bound M(source_L_domain_code M)i di k HD HI HDI)|exact BU].
   - apply(context_union_left M gb gc gn nb nc nn ub uc un HU). apply HDCIn.
     apply(proj2(source_domain_context_member_iff M(source_L_domain_code M)k db dc di HDC)). exists i. auto. }
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|].
 exact(HApply k ub uc un HBound(ex_intro _ k BU)PD(HWeaken _ PE)PW PS(HWeaken _ PX)(HWeaken _ PP)).
Qed.
Print Assumptions source_full_native_upper_from_reflection.
