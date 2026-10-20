(** Actual native upper proof from one ordinary reflected carrier and a
 full original-parameter membership block. All raw syntax, transposition,
 relative premise codes, block slicing and source proof certificates are
 generated internally. No native premise image is supplied by the caller. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceNativeKRecipes SourceWitnessThetaRecipe SourceNativePowerCarrierFixed SourceLFixed
 SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceOrdinalPredicate SourceMembershipBlocks SourceMembershipBlockProofs
 SourceNativeCarrierMembers SourceUpperTraceProfile SourceUpperTraceFrame SourceUpperWitnessRecipes SourceZeroTransposition
 SourceNativeUpperSupported SourceDomainCarrierTransport SourceDomainContexts SourceKZFCForwardSchemas SourceRelativization
 NumericalInstantiation NumericalRenaming NumericalContexts NumericalSourceFull SourceZFRProvability ContextCombination.
Unset Implicit Arguments.
Lemma source_native_subset_closed_total M carrier:exists f,source_subset_closed_graph M carrier f.
Proof. apply code_relation_total. Qed.
Theorem source_full_native_upper_block M phi theta n beta carrier s t upper relative
 refl cp ordinal level fullBlock sY tY st contained carrier_domain gb gc gn k db dc:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M phi(succM M(succM M n))->source_witness_theta_recipe M phi theta->
 source_upper_conclusion_recipe M phi upper->source_relativization M(source_L_domain_code M)upper relative->
 coding_lt M(succM M(succM M n))carrier->context_bounded M gb gc gn k->
 coding_lt M beta k->coding_lt M carrier k->coding_lt M s k->coding_lt M t k->
 (forall i,coding_lt M i(succM M(succM M n))->coding_lt M i k)->
 source_domain_context M(source_L_domain_code M)(succM M(succM M n))db dc->
 context_included M db dc(succM M(succM M n))gb gc gn->
 source_ordinary_reflection M(source_L_domain_code M)(source_succ_iter M 4 n)theta beta refl->
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M 4)(code_numeral M(sf_encode source_native_cp_theta))beta cp->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal->source_LL_instance M beta carrier level->
 source_membership_block M(zeroM M)carrier(succM M(succM M n))fullBlock->
 sf_relation M SFMember s carrier sY->sf_relation M SFMember t carrier tY->sf_relation M SFMember s t st->
 source_domain_carrier M(source_L_domain_code M)carrier contained->numerical_instantiation M(source_L_domain_code M)carrier carrier_domain->
 source_full_prv M gb gc gn refl->source_full_prv M gb gc gn cp->source_full_prv M gb gc gn ordinal->
 source_full_prv M gb gc gn level->source_full_prv M gb gc gn fullBlock->source_full_prv M gb gc gn sY->
 source_full_prv M gb gc gn tY->source_full_prv M gb gc gn st->source_full_prv M gb gc gn contained->source_full_prv M gb gc gn carrier_domain->
 exists nb nc nn ub uc un,source_zfr_context M nb nc nn /\context_union M gb gc gn nb nc nn ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros LS LR BP HTheta HUpper HR HF BC HB HY HS HT HNames HDC HIncluded
  HRefl HCP HO HL HFull HsY HtY Hst HC HDCarrier PR PCP PO PL PFull PsY PtY Pst PC PDCarrier.
 assert(HAddNames:forall i,coding_lt M i(succM M(succM M n))->coding_lt M(addM M i(zeroM M))k).
 { intros i HI. rewrite coding_add_zero_r. exact(HNames i HI). }
 assert(HTailRange:forall i,coding_lt M i n->coding_lt M(addM M i(code_numeral M 2))(succM M(succM M n))).
 { intros i HI. rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
   apply(proj2(coding_lt_succ_cancel M(succM M i)(succM M n))),(proj2(coding_lt_succ_cancel M i n));exact HI. }
 destruct(source_membership_block_total M(code_numeral M 2)carrier n)as(block&HBlock).
 assert(PBlock:source_full_prv M gb gc gn block).
 { apply(source_full_membership_block_slice M(zeroM M)(code_numeral M 2)carrier(succM M(succM M n))n
   fullBlock block gb gc gn k HAddNames HTailRange HY BC HFull);[|exact PFull].
   rewrite coding_add_zero_r. exact HBlock. }
 destruct(source_cutoff_shift_total M 2 phi)as(shifted&HCut).
 destruct(source_zero_transposition_total M carrier)as(rb&rc&HTrans).
 destruct(source_upper_trace_profile_total M shifted)as(profile&HProfile).
 destruct(sf_relation_total M SFEx profile(zeroM M))as(exprofile&HEx).
 destruct(source_upper_witness_closed_total M shifted(code_numeral M 1)(zeroM M))as(witness&HW).
 destruct(source_upper_witness_closed_total M shifted(code_numeral M 1)carrier)as(iw&HIW).
 destruct(source_native_subset_closed_total M(zeroM M))as(subsetclosed&HSC).
 destruct(source_native_subset_closed_total M carrier)as(iset&HSet).
 destruct(sf_relation_total M SFMember carrier(zeroM M))as(xb&HXB).
 destruct(sf_relation_total M SFMember(code_numeral M 1)(zeroM M))as(pb&HPB).
 destruct(sf_relation_total M SFMember(zeroM M)carrier)as(ix&HIX).
 destruct(sf_relation_total M SFMember(code_numeral M 1)carrier)as(ip&HIP).
 destruct(numerical_renaming_total M exprofile rb rc(succM M carrier)(zeroM M))as(ie&RE).
 destruct(source_relativization_total M(source_L_domain_code M)ie)as(re&HRE).
 destruct(source_relativization_total M(source_L_domain_code M)iw)as(rw&HRW).
 destruct(source_relativization_total M(source_L_domain_code M)iset)as(rs&HRS).
 assert(PX:source_full_prv M gb gc gn ix).
 { apply(source_full_membership_block_project M(zeroM M)carrier(succM M(succM M n))fullBlock gb gc gn k(zeroM M)ix
   HAddNames HY HFull BC PFull(coding_zero_lt_succ M(succM M n))). rewrite coding_add_zero_r. exact HIX. }
 assert(PP:source_full_prv M gb gc gn ip).
 { apply(source_full_membership_block_project M(zeroM M)carrier(succM M(succM M n))fullBlock gb gc gn k(code_numeral M 1)ip
   HAddNames HY HFull BC PFull).
   - apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M n))). apply coding_zero_lt_succ.
   - rewrite coding_add_zero_r. exact HIP. }
 exact(source_full_native_upper_supported M phi shifted theta n carrier rb rc profile exprofile witness subsetclosed xb pb
  upper relative ie iw iset ix ip re rw rs beta s t refl cp ordinal level block sY tY st contained carrier_domain
  LS LR(numerical_L_domain_bounded M)BP HCut HTheta HF HTrans HProfile HEx HW HIW HSC HSet HXB HPB HIX HIP HUpper HR RE HRE HRW HRS
  HRefl HCP HO HL HBlock HsY HtY Hst HC HDCarrier gb gc gn k db dc BC HDC HIncluded HB HY HS HT
  (fun i HI=>HNames(addM M i(code_numeral M 2))(HTailRange i HI))
  PR PCP PO PL PBlock PsY PtY Pst PC PX PP PDCarrier).
Qed.
Print Assumptions source_native_subset_closed_total.
Print Assumptions source_full_native_upper_block.
