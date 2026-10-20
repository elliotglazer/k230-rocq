(** From an actual common L-level, construct and eliminate both shared
 reflection-geometry witnesses and the new hierarchy carrier. Only the two
 original common-level witnesses remain; no geometric proof is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNativeKRecipes SourceWitnessThetaRecipe SourceFiniteCutoffShift SourceNativePowerCarrierFixed SourceNativeSharedGeometryTotal
 SourceCommonLevelPoint SourcePCSTables SourcePieceConjunctionBounds SourceLFixed SourceHierarchySyntax
 SourceReflectionGeometryPoint SourceReflectionGeometryTheorem SourceReflectionGeometryElimination SourceReflectionGeometryRecipe
 SourceOrdinalPredicate SourceNativeGeometryCarrierElimination SourceNativeFreshWitnessExtrusion SourceConjunctionRules
 SourceKZFCForwardSchemas SourceDomainContexts SourceRelativization NumericalInstantiation NumericalContexts NumericalEnvironments
 NumericalSourceFull SourceZFRProvability ContextCombination SourceTraceBounds SourceClosedContextShift SourceProofWeakening
 SourceNativeContextExtension SourceDerivedRules SourceContextProofHelpers SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Theorem source_full_native_common_point_to_upper M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
 seed oldY common gb gc gn k db dc:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M phi(succM M(succM M n))->source_witness_theta_recipe M phi theta->
 source_upper_conclusion_recipe M phi upper->source_relativization M(source_L_domain_code M)upper relative->
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_pcs_table M(source_L_domain_code M)theta(source_succ_iter M 4 n)pb pc pn->
 source_pcs_table M(source_L_domain_code M)(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)qb qc qn->
 source_piece_table_valid M sb sc pieces->context_included M pb pc pn sb sc pieces->context_included M qb qc qn sb sc pieces->
 coding_lt M(succM M(succM M n))(succM M k)->coding_lt M seed k->coding_lt M oldY k->
 (forall i,coding_lt M i(succM M(succM M n))->coding_lt M i k)->context_bounded M gb gc gn k->source_bounded M relative k->
 source_domain_context M(source_L_domain_code M)(succM M(succM M n))db dc->context_included M db dc(succM M(succM M n))gb gc gn->
 source_common_level_point M(zeroM M)(succM M(succM M n))seed oldY common->source_full_prv M gb gc gn common->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros LS LR BP HTheta HUpper HR BL HL HPT HQT HV HPIn HQIn HLive BSeed BOld HNames BC BG HDC HIncluded HCommon PCommon.
 pose proof HCommon as HCommonData. destruct HCommonData as(oldBlock&oldOrdinal&oldLevel&oldPair&HOldBlock&HOldOrd&HOldLevel&HOldPair&HCommonAnd).
 pose proof(source_full_conjunction_left M gb gc gn oldPair oldBlock common HCommonAnd PCommon)as POldPair.
 pose proof(source_full_conjunction_left M gb gc gn oldOrdinal oldLevel oldPair HOldPair POldPair)as POldOrd.
 destruct(source_zfr_reflection_geometry_total M level sb sc pieces seed HL HV)
  as(ordinalSeed&target&law&HOrdSeed&HTarget&HImpl&PLaw).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)seed ordinalSeed oldOrdinal HOrdSeed HOldOrd)as E;subst ordinalSeed.
 destruct PLaw as(ab&ac&an&HAC&PLaw).
 destruct(context_union_total M gb gc gn ab ac an)as(xb&xc&xn&HX).
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k(source_zfr_context_closed M ab ac an HAC)(coding_zero_lt_succ M k))as BA.
 pose proof(source_context_union_bounded M gb gc gn ab ac an xb xc xn k HX BC BA)as BX.
 assert(WX:forall f,source_full_prv M gb gc gn f->source_full_prv M xb xc xn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn xb xc xn f k PF(context_union_left M gb gc gn ab ac an xb xc xn HX)BX). }
 pose proof(source_full_prv_weaken_bounded M ab ac an xb xc xn law k PLaw(context_union_right M gb gc gn ab ac an xb xc xn HX)BX)as PLawX.
 pose proof(source_full_modus_ponens M xb xc xn oldOrdinal target law HImpl PLawX(WX _ POldOrd))as PTarget.
 destruct(source_reflection_geometry_point_total M(source_L_domain_code M)level sb sc pieces seed k(succM M k))as(point&HPoint).
 destruct(environment_cons_total M xb xc xn point)as(bb&bc&bn&HCons).
 assert(KSS:coding_lt M k(succM M(succM M k)))by exact(coding_lt_trans M k(succM M k)(succM M(succM M k))(coding_lt_succ M k)(coding_lt_succ M _)).
 assert(KSSS:coding_lt M k(succM M(succM M(succM M k))))by exact(coding_lt_trans M k(succM M(succM M k))(succM M(succM M(succM M k)))KSS(coding_lt_succ M _)).
 assert(BSeedUp:coding_lt M seed(succM M(succM M k)))by exact(coding_lt_trans M seed k(succM M(succM M k))BSeed KSS).
 assert(BOldUp:coding_lt M oldY(succM M(succM M k)))by exact(coding_lt_trans M oldY k(succM M(succM M k))BOld KSS).
 pose proof(source_reflection_geometry_point_bounded M(source_L_domain_code M)level sb sc pieces seed k(succM M k)point(succM M(succM M k))
  (numerical_L_domain_bounded M)BL HV BSeedUp KSS(coding_lt_succ M(succM M k))HPoint)as BPoint.
 pose proof(context_bounded_monotone M xb xc xn k(succM M(succM M k))BX KSSS)as BXUp.
 pose proof(proj2(context_bounded_cons M xb xc xn point bb bc bn(succM M(succM M k))HCons)(conj BPoint BXUp))as BBranch.
 pose proof(source_full_cons_head M xb xc xn point bb bc bn(succM M(succM M k))HCons BPoint BBranch)as PPoint.
 assert(WB:forall f,source_full_prv M xb xc xn f->source_full_prv M bb bc bn f).
 { intros f PF. exact(source_full_cons_weaken M xb xc xn point bb bc bn(succM M(succM M k))f HCons BBranch PF). }
 destruct(source_full_reflection_geometry_point_facts M(source_L_domain_code M)level sb sc pieces seed k(succM M k)point bb bc bn HPoint PPoint)
  as(m&o&kf&u&ob&lim&mb&s&Hm&Ho&Hkf&Hu&Hob&Hlim&Hmb&Hs&Pm&Po&Pkf&Pu&Pob&Plim&Pmb&Ps).
 assert(HDB:context_included M db dc(succM M(succM M n))bb bc bn).
 { intros f HH. apply(source_cons_tail_inclusion M xb xc xn point bb bc bn HCons).
   apply(context_union_left M gb gc gn ab ac an xb xc xn HX). exact(HIncluded f HH). }
 assert(HCarrier:coding_lt M(succM M(succM M n))(succM M(succM M k))).
 { exact(coding_le_lt_trans M(succM M(succM M n))k(succM M(succM M k))HLive KSS). }
 pose proof(source_bounded_monotone M relative k(succM M(succM M k))BG KSSS)as BGUp.
 destruct(source_full_native_geometry_without_carrier M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
  seed oldY k(succM M k)(succM M(succM M k))common point ob bb bc bn(succM M(succM M k))db dc
  LS LR BP HTheta HUpper HR BL HL HPT HQT HV HPIn HQIn HCarrier BOldUp(coding_lt_succ M(succM M k))
  (coding_lt_succ M(succM M(succM M k)))BGUp
  (fun i HI=>coding_lt_trans M i k(succM M(succM M k))(HNames i HI)KSS)BBranch HDC HDB HCommon HPoint Hob
  (WB _ (WX _ PCommon))PPoint Pob)as(eb&ec&en&ub&uc&un&HEC&HU&PGoal).
 destruct(source_full_closed_zfr_geometry_fresh M(source_L_domain_code M)level sb sc pieces seed xb xc xn k(succM M k)
  point target relative k(succM M k)bb bc bn eb ec en ub uc un
  (numerical_L_domain_bounded M)BL HV BSeed BX BG(coding_lt_succ M k)(coding_lt_succ M k)(coding_lt_succ M(succM M k))
  HPoint HTarget HCons HEC HU PGoal PTarget)as(yb&yc&yn&HY&PRelative).
 destruct(source_native_closed_extensions M gb gc gn ab ac an xb xc xn eb ec en yb yc yn HAC HX HEC HY)
  as(nb&nc&nn&vb&vc&vn&HNC&HVUnion&HIn).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn vb vc vn k HVUnion BC BN)as BV.
 exists nb,nc,nn,vb,vc,vn. split;[exact HNC|]. split;[exact HVUnion|].
 exact(source_full_prv_weaken_bounded M yb yc yn vb vc vn relative k PRelative HIn BV).
Qed.
Print Assumptions source_full_native_common_point_to_upper.
