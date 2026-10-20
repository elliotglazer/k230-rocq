(** Actual native proof after eliminating its fresh hierarchy carrier from actual common-level, shared
 geometry and new hierarchy witnesses. All carrier/profile/selector syntax,
 domains and relative proof certificates are generated inside the branch. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceNativeKRecipes SourceFiniteCutoffShift SourceWitnessThetaRecipe SourceNativePowerCarrierFixed SourceNativeSharedGeometryTotal
 SourceCommonLevelPoint SourcePCSTables SourcePieceConjunctionBounds SourceLFixed SourceHierarchySyntax
 SourceReflectionGeometryPoint SourceOrdinaryReflectionSyntax SourceOrdinalPredicate SourceMembershipBlocks
 SourceMembershipBlockProofs SourceNativeSharedCarrierEnlargement SourceNativeHierarchyCarrierUse SourceNativeUpperBlockConsumer
 SourceDomainCarrierTransport SourceRawSubset SourceKZFCForwardSchemas SourceDomainContexts SourceRelativization
 NumericalInstantiation NumericalContexts NumericalSourceFull SourceZFRProvability ContextCombination
 SourceTraceBounds SourceClosedContextShift SourceProofWeakening SourceNativeContextExtension SourceNativeGeometryBranch SourceHierarchyExistsShell SourceClosedZFRExists
 SourceDerivedRules SourceUpperProofHelpers SourceContextProofHelpers SourceLeastOrdinalWitness SourceBoundMonotone NumericalEnvironments NumericalSubstitutionMaps SubstitutionSource FiniteCRT.
Unset Implicit Arguments.
Theorem source_full_native_geometry_without_carrier M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
 seed oldY K beta carrier common geometry ordinal gb gc gn k db dc:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M phi(succM M(succM M n))->source_witness_theta_recipe M phi theta->
 source_upper_conclusion_recipe M phi upper->source_relativization M(source_L_domain_code M)upper relative->
 source_bounded M level(code_numeral M 2)->source_LL_instance M(code_numeral M 1)(zeroM M)level->
 source_pcs_table M(source_L_domain_code M)theta(source_succ_iter M 4 n)pb pc pn->
 source_pcs_table M(source_L_domain_code M)(code_numeral M(sf_encode source_native_cp_theta))(code_numeral M 4)qb qc qn->
 source_piece_table_valid M sb sc pieces->context_included M pb pc pn sb sc pieces->context_included M qb qc qn sb sc pieces->
 coding_lt M(succM M(succM M n))carrier->coding_lt M oldY k->coding_lt M beta k->coding_lt M k(succM M carrier)->source_bounded M relative k->
 (forall i,coding_lt M i(succM M(succM M n))->coding_lt M i k)->context_bounded M gb gc gn k->
 source_domain_context M(source_L_domain_code M)(succM M(succM M n))db dc->context_included M db dc(succM M(succM M n))gb gc gn->
 source_common_level_point M(zeroM M)(succM M(succM M n))seed oldY common->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc pieces seed K beta geometry->numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->
 source_full_prv M gb gc gn common->source_full_prv M gb gc gn geometry->source_full_prv M gb gc gn ordinal->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros LS LR BP HTheta HUpper HR BL HL HPT HQT HV HPIn HQIn HF BOld BB HFresh BG HNames BC HDC HIncluded
  HCommon HG HO PCommon PG PO.
 destruct(source_zfr_hierarchy_exists_shell M beta)as(ordinal'&body&ex&law&(HO'&HBody&HEx&HImpl)&PLaw).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)beta ordinal' ordinal HO' HO)as E;subst ordinal'.
 destruct PLaw as(ab&ac&an&HAC&PLaw).
 destruct(context_union_total M gb gc gn ab ac an)as(xb&xc&xn&HX).
 pose proof(context_bounded_monotone M ab ac an(zeroM M)k(source_zfr_context_closed M ab ac an HAC)(coding_zero_lt_succ M k))as BA.
 pose proof(source_context_union_bounded M gb gc gn ab ac an xb xc xn k HX BC BA)as BX.
 assert(WX:forall f,source_full_prv M gb gc gn f->source_full_prv M xb xc xn f).
 { intros f PF. exact(source_full_prv_weaken_bounded M gb gc gn xb xc xn f k PF(context_union_left M gb gc gn ab ac an xb xc xn HX)BX). }
 pose proof(source_full_prv_weaken_bounded M ab ac an xb xc xn law k PLaw(context_union_right M gb gc gn ab ac an xb xc xn HX)BX)as PLawX.
 pose proof(source_full_modus_ponens M xb xc xn ordinal ex law HImpl PLawX(WX _ PO))as PEx.
 destruct(source_LL_instance_total M beta carrier)as(newLevel&HNew).
 assert(HInst:numerical_instantiation M body carrier newLevel).
 { apply(source_LL_instance_instantiation M(succM M beta)(zeroM M)body beta carrier newLevel carrier HBody HNew).
   - intros b c HH. exact(substitution_singleton_tail M b c beta).
   - intros b c HH. exact HH. }
 assert(BBody:source_bounded M body(succM M k)).
 { exact(source_LL_instance_bounded M(succM M beta)(zeroM M)body(succM M k)
   (proj2(coding_lt_succ_cancel M beta k)BB)(coding_zero_lt_succ M k)HBody). }
 assert(KUp:coding_lt M k(succM M(succM M carrier))).
 { exact(coding_lt_trans M k(succM M carrier)(succM M(succM M carrier))HFresh(coding_lt_succ M _)). }
 assert(BXUp:context_bounded M xb xc xn(succM M carrier))by exact(context_bounded_monotone M xb xc xn k(succM M carrier)BX KUp).
 assert(BBeta:coding_lt M beta(succM M carrier))by exact(coding_lt_trans M beta k(succM M carrier)BB HFresh).
 assert(BOldUp:coding_lt M oldY(succM M carrier))by exact(coding_lt_trans M oldY k(succM M carrier)BOld HFresh).
 pose proof(source_LL_instance_bounded M beta carrier newLevel(succM M carrier)BBeta(coding_lt_succ M carrier)HNew)as BNew.
 destruct(environment_cons_total M xb xc xn newLevel)as(bb&bc&bn&HCons).
 pose proof(proj2(context_bounded_cons M xb xc xn newLevel bb bc bn(succM M carrier)HCons)(conj BNew BXUp))as BBranch.
 pose proof(source_full_cons_head M xb xc xn newLevel bb bc bn(succM M carrier)HCons BNew BBranch)as PNew.
 assert(WB:forall f,source_full_prv M xb xc xn f->source_full_prv M bb bc bn f).
 { intros f PF. exact(source_full_cons_weaken M xb xc xn newLevel bb bc bn(succM M carrier)f HCons BBranch PF). }
 assert(HDB:context_included M db dc(succM M(succM M n))bb bc bn).
 { intros f HH. apply(source_cons_tail_inclusion M xb xc xn newLevel bb bc bn HCons).
   apply(context_union_left M gb gc gn ab ac an xb xc xn HX). exact(HIncluded f HH). }
 destruct(source_full_native_geometry_branch M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
  seed oldY K beta carrier common geometry newLevel bb bc bn(succM M carrier)db dc
  LS LR BP HTheta HUpper HR BL HL HPT HQT HV HPIn HQIn HF BOldUp BBeta(coding_lt_succ M carrier)
  (fun i HI=>coding_lt_trans M i k(succM M carrier)(HNames i HI)HFresh)BBranch HDC HDB HCommon HG HNew
  (WB _ (WX _ PCommon))(WB _ (WX _ PG))PNew)as(eb&ec&en&ub&uc&un&HEC&HU&PGoal).
 destruct(source_full_closed_zfr_fresh_exists M xb xc xn body ex carrier newLevel relative bb bc bn eb ec en ub uc un k
  BX BG BBody HFresh HEx HInst HCons HEC HU PGoal PEx)as(yb&yc&yn&HY&PRelative).
 destruct(source_native_closed_extensions M gb gc gn ab ac an xb xc xn eb ec en yb yc yn HAC HX HEC HY)
  as(nb&nc&nn&vb&vc&vn&HNC&HVUnion&HIn).
 pose proof(context_bounded_monotone M nb nc nn(zeroM M)k(source_zfr_context_closed M nb nc nn HNC)(coding_zero_lt_succ M k))as BN.
 pose proof(source_context_union_bounded M gb gc gn nb nc nn vb vc vn k HVUnion BC BN)as BV.
 exists nb,nc,nn,vb,vc,vn. split;[exact HNC|]. split;[exact HVUnion|].
 exact(source_full_prv_weaken_bounded M yb yc yn vb vc vn relative k PRelative HIn BV).
Qed.
Print Assumptions source_full_native_geometry_without_carrier.
