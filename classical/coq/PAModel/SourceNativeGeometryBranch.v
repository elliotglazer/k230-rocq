(** Complete ordinary native branch from actual common-level, shared
 geometry and new hierarchy witnesses. All carrier/profile/selector syntax,
 domains and relative proof certificates are generated inside the branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceNativeKRecipes SourceFiniteCutoffShift SourceWitnessThetaRecipe SourceNativePowerCarrierFixed SourceNativeSharedGeometryTotal
 SourceCommonLevelPoint SourcePCSTables SourcePieceConjunctionBounds SourceLFixed SourceHierarchySyntax
 SourceReflectionGeometryPoint SourceOrdinaryReflectionSyntax SourceOrdinalPredicate SourceMembershipBlocks
 SourceMembershipBlockProofs SourceNativeSharedCarrierEnlargement SourceNativeHierarchyCarrierUse SourceNativeUpperBlockConsumer
 SourceDomainCarrierTransport SourceRawSubset SourceKZFCForwardSchemas SourceDomainContexts SourceRelativization
 NumericalInstantiation NumericalContexts NumericalSourceFull SourceZFRProvability ContextCombination
 SourceTraceBounds SourceClosedContextShift SourceProofWeakening SourceNativeContextExtension.
Unset Implicit Arguments.
Theorem source_full_native_geometry_branch M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
 seed oldY K beta carrier common geometry newLevel gb gc gn k db dc:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M phi(succM M(succM M n))->source_witness_theta_recipe M phi theta->
 source_upper_conclusion_recipe M phi upper->source_relativization M(source_L_domain_code M)upper relative->
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_pcs_table M(source_L_domain_code M)theta(source_succ_iter M 4 n)pb pc pn->
 source_pcs_table M(source_L_domain_code M)(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)qb qc qn->
 source_piece_table_valid M sb sc pieces->context_included M pb pc pn sb sc pieces->context_included M qb qc qn sb sc pieces->
 coding_lt M(succM M(succM M n))carrier->coding_lt M oldY k->coding_lt M beta k->coding_lt M carrier k->
 (forall i,coding_lt M i(succM M(succM M n))->coding_lt M i k)->context_bounded M gb gc gn k->
 source_domain_context M(source_L_domain_code M)(succM M(succM M n))db dc->context_included M db dc(succM M(succM M n))gb gc gn->
 source_common_level_point M(zeroM M)(succM M(succM M n))seed oldY common->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc pieces seed K beta geometry->source_LL_instance M beta carrier newLevel->
 source_full_prv M gb gc gn common->source_full_prv M gb gc gn geometry->source_full_prv M gb gc gn newLevel->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros LS LR BP HTheta HUpper HR BL HL HPT HQT HV HPIn HQIn HF BOld BB BY HNames BC HDC HIncluded
  HCommon HG HNew PCommon PG PNew.
 pose proof(source_witness_theta_recipe_bound M phi theta n BP HTheta)as BTheta.
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)(source_succ_iter M 4 n)theta beta)as(refl&HRefl).
 destruct(source_ordinary_reflection_total M(source_L_domain_code M)(code_numeral M 4)(code_numeral M(sf_encode source_native_cp_theta))beta)as(cp&HCP).
 destruct(source_membership_block_total M(zeroM M)carrier(succM M(succM M n)))as(full&HFull).
 destruct(sf_relation_total M SFMember oldY carrier)as(inLevel&HIn).
 destruct(source_raw_subset_total M oldY carrier)as(subset&HSubset).
 destruct(sf_relation_total M SFMember(zeroM M)oldY)as(st&Hst).
 destruct(source_full_native_shared_carrier_enlargement M level sb sc pieces pb pc pn qb qc qn theta(source_succ_iter M 4 n)
  (code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)(succM M(succM M n))seed oldY K beta carrier
  common geometry newLevel refl cp full inLevel subset st gb gc gn k BL HL BTheta HPT(source_native_cp_theta_bounded M)HQT
  HV HPIn HQIn(coding_zero_lt_succ M(succM M n))HNames BOld BY BC HCommon HG HNew HRefl HCP HFull HIn HSubset Hst PCommon PG PNew)
  as(ab&ac&an&xb&xc&xn&ordinal&HAC&HX&HO&PR&PCP&PO&PL&PFull&PIn&Pst).
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k(source_zfr_context_closed M ab ac an HAC)(coding_zero_lt_succ M k))as BA.
 pose proof(source_context_union_bounded M gb gc gn ab ac an xb xc xn k HX BC BA)as BX.
 destruct(numerical_instantiation_total M(source_L_domain_code M)carrier)as(carrier_domain&HDCarrier).
 destruct(source_domain_carrier_total M(source_L_domain_code M)carrier)as(contained&HContained).
 destruct(source_full_native_hierarchy_carrier M beta carrier ordinal newLevel carrier_domain contained xb xc xn k HO HNew HDCarrier HContained BX PO PL)
  as(eb&ec&en&yb&yc&yn&HEC&HY&PDCarrier&PContained).
 pose proof(context_bounded_monotone M eb ec en(zeroM M)k(source_zfr_context_closed M eb ec en HEC)(coding_zero_lt_succ M k))as BE.
 pose proof(source_context_union_bounded M xb xc xn eb ec en yb yc yn k HY BX BE)as BNew.
 assert(WY:forall f,source_full_prv M xb xc xn f->source_full_prv M yb yc yn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M xb xc xn yb yc yn f k PF(context_union_left M xb xc xn eb ec en yb yc yn HY)BNew). }
 assert(HDY:context_included M db dc(succM M(succM M n))yb yc yn).
 { intros f HH. apply(context_union_left M xb xc xn eb ec en yb yc yn HY).
   apply(context_union_left M gb gc gn ab ac an xb xc xn HX). exact(HIncluded f HH). }
 assert(B0:coding_lt M(zeroM M)k)by(exact(HNames _ (coding_zero_lt_succ M(succM M n)))).
 destruct(sf_relation_total M SFMember(zeroM M)carrier)as(sY&HsY).
 assert(PsY:source_full_prv M xb xc xn sY).
 { apply(source_full_membership_block_project M(zeroM M)carrier(succM M(succM M n))full xb xc xn k(zeroM M)sY).
   - intros i HI. rewrite coding_add_zero_r. exact(HNames i HI).
   - exact BY.
   - exact HFull.
   - exact BX.
   - exact PFull.
   - exact(coding_zero_lt_succ M(succM M n)).
   - rewrite coding_add_zero_r. exact HsY. }
 destruct(source_full_native_upper_block M phi theta n beta carrier(zeroM M)oldY upper relative
  refl cp ordinal newLevel full sY inLevel st contained carrier_domain yb yc yn k db dc
  LS LR BP HTheta HUpper HR HF BNew BB BY B0 BOld HNames HDC HDY HRefl HCP HO HNew HFull HsY HIn Hst HContained HDCarrier
  (WY _ PR)(WY _ PCP)(WY _ PO)(WY _ PL)(WY _ PFull)(WY _ PsY)(WY _ PIn)(WY _ Pst)PContained PDCarrier)
  as(fb&fc&fn&zb&zc&zn&HFC&HZ&PResult).
 destruct(source_native_closed_extensions M xb xc xn eb ec en yb yc yn fb fc fn zb zc zn HEC HY HFC HZ)
  as(vb&vc&vn&wb&wc&wn&HVC&HW&HZW).
 destruct(source_native_closed_extensions M gb gc gn ab ac an xb xc xn vb vc vn wb wc wn HAC HX HVC HW)
  as(nb&nc&nn&ub&uc&un&HNC&HU&HWU).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn ub uc un k HU BC BN)as BU.
 exists nb,nc,nn,ub,uc,un. split;[exact HNC|]. split;[exact HU|].
 apply(source_full_prv_weaken_bounded M zb zc zn ub uc un relative k PResult);[|exact BU].
 intros f HH. exact(HWU f(HZW f HH)).
Qed.
Print Assumptions source_full_native_geometry_branch.
