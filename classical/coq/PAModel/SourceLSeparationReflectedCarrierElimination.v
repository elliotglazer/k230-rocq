(** A real shared-carrier existential discharges the carrier branch of Separation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SchemaRenamingDescriptors SchemaRenamingBounds NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
 ContextCombination SourceTraceBounds SourceProofWeakening SourceContextTransport SourceLeastOrdinalWitness SourceClosedContextShift
 SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceRelativization SourceRelativizationBounds SourceSetRelativization
 SourceLDefinableProfile SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceLSeparationSchemaShift SourceLSeparationCarrierElimination
 SourceLSeparationChosenCarrier SourceZFRProvability SourceOrdinalPredicate SourceHierarchySyntax NumericalInstantiation
 SourceOrdinaryReflectionSyntax SourceMembershipBlocks.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_full_L_reflected_carrier_elimination M phi psi body matrix rp lp sp defex allr witness params wide
 b c n sb sc eb ec en tb tc exbody ex d ordinal level refl block:
 source_bounded M phi(succM M params) ->coding_lt M params(succM M wide) ->
 source_l_psiS M phi psi ->schema_renaming M SepBody phi body ->source_cutoff_shift_thrice M phi matrix ->
 source_relativization M(source_L_domain_code M)body rp ->source_relativization M(source_L_domain_code M)matrix lp ->
 source_set_relativization M(code_numeral M 2)matrix sp ->source_L_definable_profile M psi defex ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 code_relation M(L_definable_profile_environment rp(source_L_domain_code M))(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
 context_bounded M b c n(succM M wide) ->context_shift M b c n sb sc ->
 environment_cons M sb sc n exbody eb ec en ->context_bounded M eb ec en(succM M(succM M wide)) ->context_shift M eb ec en tb tc ->
 sf_relation M SFEx exbody(zeroM M)ex ->coding_lt M d(succM M(succM M wide)) ->
 numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->source_LL_instance M d(zeroM M)level ->
 source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_membership_block M(code_numeral M 1)(zeroM M)(succM M params)block ->
 source_full_prv M b c n ex ->source_full_prv M eb ec en defex ->source_full_prv M eb ec en ordinal ->
 source_full_prv M eb ec en level ->source_full_prv M eb ec en refl ->source_full_prv M eb ec en block ->
 exists ab ac an ub uc un,source_zfr_context M ab ac an /\context_union M ab ac an b c n ub uc un /\source_full_prv M ub uc un witness.
Proof.
 intros HP HCount HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness HC HS HCons HBranch HT HEx BD HO HL HR HB PEx PDef PO PL PR PB.
 assert(HPWide:source_bounded M phi(succM M wide)).
 { exact(SourceBoundMonotone.source_bounded_monotone M phi(succM M params)(succM M wide)HP
   (proj2(coding_lt_succ_cancel M params(succM M wide))HCount)). }
 destruct(code_relation_total M(E_L_carrier_separation(CEvar 1)(CEvar 0))
  (L_definable_profile_environment lp(source_L_domain_code M)))as(carrier&HCarrier).
 destruct(source_full_L_chosen_carrier_separation M phi psi matrix lp sp defex allr carrier params wide
  eb ec en tb tc d ordinal level refl block HP HCount HPsi HMatrix HLP HSP HDef HRef HCarrier HBranch HT BD HO HL HR HB PDef PO PL PR PB)
 as(ab&ac&an&ob&oc&on&HAC&HCarrierUnion&PCarrier).
 pose proof(source_zfr_context_closed M ab ac an HAC)as HAClosed.
 destruct(context_union_total M ab ac an b c n)as(ub&uc&un&HUnion).
 pose proof(context_union_left M ab ac an b c n ub uc un HUnion)as HLeft.
 pose proof(context_union_right M ab ac an b c n ub uc un HUnion)as HRight.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)(succM M wide)HAClosed(coding_zero_lt_succ M(succM M wide)))as HAB.
 pose proof(source_context_union_bounded M ab ac an b c n ub uc un(succM M wide)HUnion HAB HC)as HUC.
 destruct(context_shift_total M ub uc un)as(us&vs&HUS).
 pose proof(context_shift_preserves_bound M ub uc un us vs(succM M wide)HUS HUC)as HUSC.
 destruct(environment_cons_total M us vs un exbody)as(cb&cc&cn&HNewCons).
 assert(HBodyBound:source_bounded M exbody(succM M(succM M wide))).
 { apply HBranch. apply(proj2(context_member_cons M sb sc n exbody eb ec en exbody HCons)). now left. }
 pose proof(proj2(context_bounded_cons M us vs un exbody cb cc cn(succM M(succM M wide))HNewCons)(conj HBodyBound HUSC))as HNewBranch.
 pose proof(source_context_included_shift M b c n ub uc un sb sc us vs HRight HS HUS)as HShiftRight.
 pose proof(source_context_included_cons M sb sc n us vs un exbody eb ec en cb cc cn HShiftRight HCons HNewCons)as HBranchRight.
 pose proof(source_context_included_shift M ab ac an ub uc un ab ac us vs HLeft(source_closed_context_shift_self M ab ac an HAClosed)HUS)as HShiftLeft.
 assert(HBranchLeft:context_included M ab ac an cb cc cn).
 { intros f HF. exact(source_cons_tail_inclusion M us vs un exbody cb cc cn HNewCons f(HShiftLeft f HF)). }
 assert(HCarrierIncluded:context_included M ob oc on cb cc cn).
 { intros f HF. apply(proj1(proj2 HCarrierUnion f))in HF.
   destruct HF as[HF|HF];[exact(HBranchLeft f HF)|exact(HBranchRight f HF)]. }
 pose proof(source_full_prv_weaken_bounded M ob oc on cb cc cn carrier(succM M(succM M wide))PCarrier HCarrierIncluded HNewBranch)as PCarrierNew.
 pose proof(source_full_prv_weaken_bounded M b c n ub uc un ex(succM M wide)PEx HRight HUC)as PExNew.
 pose proof(source_L_SepBody_witness_carrier_shift M(source_L_domain_code M)phi body matrix rp lp witness carrier wide
  (numerical_L_domain_bounded M)HPWide HBody HMatrix HRP HLP HWitness HCarrier)as HWitnessShift.
 pose proof(source_relativization_preserves_bound M body(source_L_domain_code M)(succM M(succM M(succM M wide)))rp
  (numerical_L_domain_bounded M)(schema_separation_bound M phi body wide HPWide HBody)HRP)as BRP.
 pose proof(source_lsep_canonical_witness_bounded M(source_L_domain_code M)rp witness wide(numerical_L_domain_bounded M)BRP HWitness)as BWitness.
 exists ab,ac,an,ub,uc,un. split;[exact HAC|]. split;[exact HUnion|].
 exact(full_source_ExE M ub uc un exbody ex witness carrier us vs cb cc cn
  (ex_intro _ (succM M wide)(conj BWitness HUC))PExNew PCarrierNew HEx HUS HNewCons HWitnessShift).
Qed.
Print Assumptions source_full_L_reflected_carrier_elimination.
