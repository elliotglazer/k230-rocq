(** The real L-relative native trace theorem requires domains only for
 the original parameters and the selected carrier. Its unused internal
 proof names are projected away before any geometric witness is eliminated. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceFiniteCutoffShift
 SourceUpperTraceProfile SourceUpperPremiseBounds SetFormulaCodes SourceLFixed SourceKZFCForwardSchemas
 SourceNativeLTraceExistence SourceNativeSupportProjection SourceNativeProjectionInvariance SourceZeroTransposition
 SourceDomainSupportedRenaming SourceDomainContexts SourceRelativization SourceRelativizationRenaming SourceRelativizationFunctionality
 SourceZFRProvability NumericalRenaming NumericalContexts NumericalSourceFull ContextCombination SourceContextTransport NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_zfr_L_upper_trace_supported M phi shifted n fresh tb tc profile exprofile ie relative:
 L_separation_image_obligation M->L_replacement_image_obligation M->
 source_bounded M phi(succM M(succM M n))->source_cutoff_shift M 2 phi shifted->
 coding_lt M(succM M(succM M n))fresh->source_zero_transposition M fresh tb tc->
 source_upper_trace_profile M shifted profile->sf_relation M SFEx profile(zeroM M)exprofile->
 numerical_renaming M exprofile tb tc(succM M fresh)(zeroM M)ie->source_relativization M(source_L_domain_code M)ie relative->
 exists ab ac an,source_zfr_context M ab ac an /\forall gb gc gn,
 source_context_finite_bound M gb gc gn->context_included M ab ac an gb gc gn->
 (forall i di,coding_lt M i(succM M(succM M n))->numerical_instantiation M(source_L_domain_code M)i di->source_full_prv M gb gc gn di)->
 (forall di,numerical_instantiation M(source_L_domain_code M)fresh di->source_full_prv M gb gc gn di)->
 source_full_prv M gb gc gn relative.
Proof.
 intros LSep LRep BP HCut HF HTrans HProfile HEx RE HR.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(source_cutoff_shift_bounded M 2 phi shifted n BP HCut)as BShift.
 pose proof(source_upper_trace_profile_bound M shifted profile(succM M n)BShift HProfile)as BProfile.
 pose proof(proj2(source_bounded_accept_unary M SFEx profile exprofile(succM M(succM M n))(or_intror eq_refl)HEx)BProfile)as BE.
 destruct(source_zfr_L_upper_trace_renamed_exists M shifted(succM M n)profile exprofile ie tb tc(succM M fresh)(zeroM M)relative
  LSep LRep BShift HProfile HEx RE HR)as(bound&ab&ac&an&HAC&HTrace).
 destruct(source_domain_context_total M(source_L_domain_code M)bound)as(db&dc&HDC).
 destruct(context_union_total M ab ac an db dc bound)as(ub&uc&un&HU).
 pose proof(HTrace bound db dc ub uc un(coding_lt_succ M bound)HDC HU)as PRelative.
 destruct(source_native_support_projection_total M(succM M(succM M n))fresh bound)as(rb&rc&HProjection).
 pose proof(source_transposed_bounded_projection_fixed M exprofile(succM M(succM M n))fresh tb tc ie bound rb rc
  BE HF HTrans RE HProjection)as RIE.
 destruct(source_relativization_renaming_exists M ie(source_L_domain_code M)rb rc bound(zeroM M)ie relative HD RIE HR)
  as(result&HResult&RRelative).
 pose proof(source_relativization_functional M ie(source_L_domain_code M)result relative HResult HR)as E;subst result.
 exists ab,ac,an. split;[exact HAC|]. intros gb gc gn HC HIn PD PY.
 apply(source_full_domain_supported_renaming M(source_L_domain_code M)ab ac an bound db dc ub uc un relative
  rb rc bound(zeroM M)relative gb gc gn HD(source_zfr_context_closed M ab ac an HAC)HDC HU PRelative RRelative HC HIn).
 intros i j di HI Hij HDI. destruct(proj2(proj2 HProjection)i j HI Hij)as[HJ|[EJ|EJ]].
 - exact(PD j di HJ HDI).
 - subst j. exact(PY di HDI).
 - subst j. exact(PD(zeroM M)di(coding_zero_lt_succ M(succM M n))HDI).
Qed.
Print Assumptions source_zfr_L_upper_trace_supported.
