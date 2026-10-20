(** Close the actual L Separation image from the genuine common-reflected-level law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments
 NumericalContextRenaming NumericalSourceFull SourceTraceBounds SourceClosedContextShift SourceContextTransport SourceProofWeakening
 SourceLeastOrdinalWitness SourceDerivedRules ContextCombination SourceDomainContexts SourcePredicateBlocks SourceRelativizationBounds
 SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceRelativization SourceSetRelativization SourceLDefinableProfile
 SchemaRenamingDescriptors SchemaRenamingBounds SetSchemaConstructors SchemaConstructorBounds SourceSchemaRelativization SourceRelativeSchemaConstructors
 SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceLSeparationConstructorShell SourceLSeparationSharedWitnessBase SourceLSeparationGuardParameters
 SourceCommonReflectedLevel SourceZFRProvability SourceZFRDomainPrefix NumericalSetClosure.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_L_separation_closed_from_shared M phi psi body matrix rp lp sp defex allr witness params rawopen target f rf block whole law:
 source_bounded M phi(succM M params) ->source_l_psiS M phi psi ->schema_renaming M SepBody phi body ->
 source_cutoff_shift_thrice M phi matrix ->source_relativization M(source_L_domain_code M)body rp ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_L_definable_profile M psi defex ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 code_relation M(L_definable_profile_environment rp(source_L_domain_code M))(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
 sf_separation_constructor M body rawopen ->sf_relative_separation_constructor M(source_L_domain_code M)rp target ->
 all_prefix M params rawopen f ->source_relativization M(source_L_domain_code M)rawopen target ->source_relativization M(source_L_domain_code M)f rf ->
 source_predicate_block M(zeroM M)(source_L_domain_code M)(succM M params)block ->
 source_common_reflected_level_recipe M(zeroM M)(succM M params)(succM M params)phi whole ->
 sf_relation M SFImpl block whole law ->source_zfr_provable M law ->source_zfr_provable M rf.
Proof.
 intros HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness HRaw HTarget HClosed HOpenImage HImage HBlock HWhole HLaw PLaw.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(schema_separation_bound M phi body params HP HBody)as BB.
 pose proof(schema_separation_constructor_bound M body rawopen params BB HRaw)as BRaw.
 pose proof(source_relativization_preserves_bound M body(source_L_domain_code M)(succM M(succM M(succM M params)))rp HD BB HRP)as BRP.
 destruct(source_L_separation_shared_witness_base M phi psi body matrix rp lp sp defex allr witness params
  HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness)as(fb&fc&fn&HBase&PWitnessAt).
 destruct PLaw as(lb&lc&ln&HLC&PLaw).
 destruct(context_union_total M fb fc fn lb lc ln)as(gb&gc&gn&HBaseUnion).
 assert(HG:source_zfr_context M gb gc gn).
 { intros a HA. apply(proj1(proj2 HBaseUnion a))in HA. destruct HA as[HA|HA];[exact(HBase a HA)|exact(HLC a HA)]. }
 pose proof(context_union_left M fb fc fn lb lc ln gb gc gn HBaseUnion)as HFBase.
 pose proof(context_union_right M fb fc fn lb lc ln gb gc gn HBaseUnion)as HLBase.
 destruct(source_domain_context_total M(source_L_domain_code M)params)as(db&dc&HDomain).
 destruct(context_union_total M gb gc gn db dc params)as(b&c&n&HUnion).
 pose proof(context_union_left M gb gc gn db dc params b c n HUnion)as HBaseIn.
 pose proof(context_bounded_monotone M gb gc gn(zeroM M)params(source_zfr_context_closed M gb gc gn HG)(coding_zero_lt_succ M params))as HGB.
 pose proof(source_domain_context_bounded M(source_L_domain_code M)params db dc HD HDomain)as HDB.
 pose proof(source_context_union_bounded M gb gc gn db dc params b c n params HUnion HGB HDB)as HC.
 destruct(context_shift_total M b c n)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b c n sb sc params HS HC)as HSC.
 destruct(environment_cons_total M sb sc n(source_L_domain_code M))as(eb&ec&en&HCons).
 pose proof(proj2(context_bounded_cons M sb sc n(source_L_domain_code M)eb ec en(succM M params)HCons)
  (conj(sr_domain_bound_succ M(source_L_domain_code M)params HD)HSC))as HBranch.
 pose proof(source_full_L_separation_guard_parameters M params gb gc gn db dc b c n sb sc eb ec en block HG HDomain HUnion HS HCons HBlock)as PBlock.
 assert(HFIncluded:context_included M fb fc fn eb ec en).
 { pose proof(context_included_trans M fb fc fn gb gc gn b c n HFBase HBaseIn)as HI.
   pose proof(source_context_included_shift M fb fc fn b c n fb fc sb sc HI(source_closed_context_shift_self M fb fc fn(source_zfr_context_closed M fb fc fn HBase))HS)as HSI.
   intros a HA. exact(source_cons_tail_inclusion M sb sc n(source_L_domain_code M)eb ec en HCons a(HSI a HA)). }
 assert(HLIncluded:context_included M lb lc ln eb ec en).
 { pose proof(context_included_trans M lb lc ln gb gc gn b c n HLBase HBaseIn)as HI.
   pose proof(source_context_included_shift M lb lc ln b c n lb lc sb sc HI(source_closed_context_shift_self M lb lc ln(source_zfr_context_closed M lb lc ln HLC))HS)as HSI.
   intros a HA. exact(source_cons_tail_inclusion M sb sc n(source_L_domain_code M)eb ec en HCons a(HSI a HA)). }
 pose proof(source_full_modus_ponens M eb ec en block whole law HLaw
  (source_full_prv_weaken_bounded M lb lc ln eb ec en law(succM M params)PLaw HLIncluded HBranch)PBlock)as PWhole.
 destruct(PWitnessAt eb ec en whole HFIncluded HBranch HWhole PWhole)
 as(ab&ac&an&wb&wc&wn&HAC&HBranchUnion&PWitness).
 destruct(context_union_total M ab ac an b c n)as(ub&uc&un&HFinalUnion).
 pose proof(context_union_left M ab ac an b c n ub uc un HFinalUnion)as HLeft.
 pose proof(context_union_right M ab ac an b c n ub uc un HFinalUnion)as HRight.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)params(source_zfr_context_closed M ab ac an HAC)(coding_zero_lt_succ M params))as HAB.
 pose proof(source_context_union_bounded M ab ac an b c n ub uc un params HFinalUnion HAB HC)as HUC.
 destruct(context_shift_total M ub uc un)as(us&vs&HUS).
 pose proof(context_shift_preserves_bound M ub uc un us vs params HUS HUC)as HUSC.
 destruct(environment_cons_total M us vs un(source_L_domain_code M))as(cb&cc&cn&HNewCons).
 pose proof(proj2(context_bounded_cons M us vs un(source_L_domain_code M)cb cc cn(succM M params)HNewCons)
  (conj(sr_domain_bound_succ M(source_L_domain_code M)params HD)HUSC))as HNewBranch.
 pose proof(source_context_included_shift M b c n ub uc un sb sc us vs HRight HS HUS)as HShiftRight.
 pose proof(source_context_included_cons M sb sc n us vs un(source_L_domain_code M)eb ec en cb cc cn HShiftRight HCons HNewCons)as HBranchRight.
 pose proof(source_context_included_shift M ab ac an ub uc un ab ac us vs HLeft
  (source_closed_context_shift_self M ab ac an(source_zfr_context_closed M ab ac an HAC))HUS)as HShiftLeft.
 assert(HInclude:context_included M wb wc wn cb cc cn).
 { intros a HA. apply(proj1(proj2 HBranchUnion a))in HA. destruct HA as[HA|HA].
   - exact(source_cons_tail_inclusion M us vs un(source_L_domain_code M)cb cc cn HNewCons a(HShiftLeft a HA)).
   - exact(HBranchRight a HA). }
 pose proof(source_full_prv_weaken_bounded M wb wc wn cb cc cn witness(succM M params)PWitness HInclude HNewBranch)as PWitnessNew.
 pose proof(source_full_relative_separation_outer M ub uc un us vs cb cc cn(source_L_domain_code M)rp witness target params
  HD BRP HUC HTarget HWitness HUS HNewCons PWitnessNew)as PTarget.
 exact(source_zfr_domain_prefix_from_union M(source_L_domain_code M)params rawopen target f rf gb gc gn db dc b c n ab ac an ub uc un
  HD BRaw HClosed HOpenImage HImage HG HDomain HUnion HAC HFinalUnion PTarget).
Qed.
Print Assumptions source_zfr_L_separation_closed_from_shared.
