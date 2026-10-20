(** A genuine shared reflected carrier and actual local definability yield the canonical Separation witness. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SchemaRenamingDescriptors NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
 SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceRelativization SourceSetRelativization SourceLDefinableProfile
 SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceLocalLDefinabilityBase SourceLSeparationChosenCarrier SourceLSeparationReflectedCarrierElimination
 SourceCommonReflectedLevel SourceCommonReflectedOpening SourceZFRProvability ContextCombination
 SourceContextTransport SourceLeastOrdinalWitness SourceClosedContextShift SourceContextProofHelpers.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_L_separation_shared_carrier_base M phi psi body matrix rp lp sp defex allr witness params:
 source_bounded M phi(succM M params) ->source_l_psiS M phi psi ->schema_renaming M SepBody phi body ->
 source_cutoff_shift_thrice M phi matrix ->source_relativization M(source_L_domain_code M)body rp ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_L_definable_profile M psi defex ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 code_relation M(L_definable_profile_environment rp(source_L_domain_code M))(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
 exists fb fc fn,source_zfr_context M fb fc fn /\
 forall wide b c n beta exbody ex,
 context_included M fb fc fn b c n ->coding_lt M params(succM M wide) ->context_bounded M b c n(succM M wide) ->
 coding_lt M beta(succM M wide) ->
 source_common_reflected_level_point M(code_numeral M 1)(succM M params)(succM M params)phi(succM M beta)(zeroM M)exbody ->
 sf_relation M SFEx exbody(zeroM M)ex ->source_full_prv M b c n ex ->
 exists ab ac an ub uc un,source_zfr_context M ab ac an /\context_union M ab ac an b c n ub uc un /\source_full_prv M ub uc un witness.
Proof.
 intros HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness.
 destruct(source_local_L_definability_base_total M(succM M params)psi(source_l_psiS_bounded M phi psi params HP HPsi))as(fb&fc&fn&HBase&PBase).
 exists fb,fc,fn. split;[exact HBase|].
 intros wide b c n beta exbody ex HIncluded HCount HC BB HPoint HEx PEx.
 assert(HNames:forall i,coding_lt M i(succM M params) ->coding_lt M(addM M i(code_numeral M 1))(succM M(succM M wide))).
 { intros i HI. rewrite source_lsep_add_one. apply coding_lt_succ_cancel.
   exact(SourceBoundMonotone.source_bound_lt_le M i(succM M params)(succM M wide)HI
    (proj2(coding_lt_succ_cancel M params(succM M wide))HCount)). }
 assert(BD:coding_lt M(succM M beta)(succM M(succM M wide)))by(now apply coding_lt_succ_cancel).
 assert(BBody:source_bounded M exbody(succM M(succM M wide))).
 { exact(source_common_reflected_level_point_bounded M(code_numeral M 1)(succM M params)(succM M params)phi
   (succM M beta)(zeroM M)exbody(succM M(succM M wide))HP HNames BD(coding_zero_lt_succ M(succM M wide))HPoint). }
 destruct(context_shift_total M b c n)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b c n sb sc(succM M wide)HS HC)as HSC.
 destruct(environment_cons_total M sb sc n exbody)as(eb&ec&en&HCons).
 pose proof(proj2(context_bounded_cons M sb sc n exbody eb ec en(succM M(succM M wide))HCons)(conj BBody HSC))as HBranch.
 destruct(context_shift_total M eb ec en)as(tb&tc&HT).
 pose proof(source_full_cons_head M sb sc n exbody eb ec en(succM M(succM M wide))HCons BBody HBranch)as PPoint.
 destruct(source_full_common_reflected_components M(code_numeral M 1)(succM M params)(succM M params)phi
  (succM M beta)(zeroM M)exbody eb ec en HPoint PPoint)
 as(ordinal&level&block&refl&HO&HL&HB&HR&PO&PL&PB&PR).
 pose proof(source_zfr_context_closed M fb fc fn HBase)as HClosed.
 pose proof(source_context_included_shift M fb fc fn b c n fb fc sb sc HIncluded
  (source_closed_context_shift_self M fb fc fn HClosed)HS)as HShiftIncluded.
 assert(HBaseBranch:context_included M fb fc fn eb ec en).
 { intros f HF. exact(source_cons_tail_inclusion M sb sc n exbody eb ec en HCons f(HShiftIncluded f HF)). }
 pose proof(PBase eb ec en(succM M(succM M wide))(succM M beta)ordinal level block defex
  HBaseBranch HBranch HO HL HB PO PL PB HDef)as PDef.
 exact(source_full_L_reflected_carrier_elimination M phi psi body matrix rp lp sp defex allr witness params wide
  b c n sb sc eb ec en tb tc exbody ex(succM M beta)ordinal level refl block HP HCount HPsi HBody HMatrix HRP HLP HSP HDef HRef HWitness
  HC HS HCons HBranch HT HEx BD HO HL HR HB PEx PDef PO PL PR PB).
Qed.
Print Assumptions source_L_separation_shared_carrier_base.
