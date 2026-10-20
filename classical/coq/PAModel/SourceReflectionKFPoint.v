(** Actual ExE of the closure successor, yielding the K-successor profile. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate
 SourceRecursionNextIn SourceRecursionClosureUse SourceRecursionExAAdjoin
 SourceReflectionStep SourceReflectionOrdinalChartRules SourceReflectionKFInputs SourceReflectionKFNext SourceReflectionKFBranch SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_KF_point M level sb sc count phi a Y K x A target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->coding_lt M x k ->
 source_reflection_KF_inputs M phi a Y K x A ->source_reflection_KF_next M(source_L_domain_code M)level sb sc count K x target ->
 source_finite_telescope M A target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HMatrix BA BY BK BX HA HT HLaw. set(s:=succM M).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_KF_inputs_bounded M phi a Y K x A k BP BA BY BK BX HA)as Bounds.
 pose proof(source_reflection_KF_next_bounded M(source_L_domain_code M)level sb sc count K x target k(numerical_L_domain_bounded M)HL HV BK BX HT)as BT.
 destruct(source_rec_next_in_total M phi x Y)as(available&HAvailable).
 pose proof(source_rec_next_in_bounded M phi x Y available k BP BX BY HAvailable)as BAvailable.
 pose proof HAvailable as HNext. destruct HNext as(binary&memberY&body&HBinary&HMY&HBody&HEx).
 destruct(source_reflection_KF_inputs_total M phi(s a)(s Y)(s K)(s x))as(AS&HAS).
 pose proof(source_reflection_KF_inputs_shift M phi a Y K x A AS BP HA HAS)as HS.
 destruct(source_reflection_KF_next_total M(source_L_domain_code M)level sb sc count(s K)(s x))as(targetS&HTS).
 pose proof(source_reflection_KF_next_shift M(source_L_domain_code M)level sb sc count K x target targetS(numerical_L_domain_bounded M)HL HV HT HTS)as STarget.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_reflection_KF_branch M level sb sc count phi(s a)(s Y)(s K)(s x)(zeroM M)AS binary memberY body targetS branch(s k)HLevel HV BP HMatrix);
    try(rec_exa_name_bound);assumption. }
 destruct(source_finite_telescope_total M(A++[available])target)as(exLaw&HExLaw).
 pose proof(source_zfr_finite_telescope_exists M A AS body available target targetS branch exLaw k Bounds BAvailable BT HS HEx STarget HBranch HExLaw PBranch)as PExLaw.
 pose proof HA as HInputs. destruct HA as(chart&closure&memberK&E&HC&HClosure&HMK). subst A.
 apply(source_zfr_finite_rule M[exLaw][chart;closure;memberK]target law k Bounds BT HLaw).
 - intros f[<-|[]]. exact PExLaw.
 - intros b c n BC Laws Premises.
   destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)x)as(ordinal&HO).
   destruct(sf_relation_total M SFMember x Y)as(memberXY&HXY).
   destruct(source_full_reflection_ordinal_chart_out M b c n Y K chart x memberK memberXY ordinal HC HMK HXY HO
    (Premises chart ltac:(cbn;tauto))(Premises memberK ltac:(cbn;tauto)))as(PXY&_).
   pose proof(source_full_rec_closure_next M b c n phi a Y closure x memberXY available BP HClosure HXY HAvailable
    (Premises closure ltac:(cbn;tauto))PXY)as PAvailable.
   apply(source_full_finite_telescope_apply M([chart;closure;memberK]++[available])target exLaw HExLaw b c n(Laws exLaw(or_introl eq_refl))).
   intros f HF. apply in_app_or in HF. destruct HF as[HF|[<-|[]]];[exact(Premises f HF)|exact PAvailable].
Qed.
Print Assumptions source_zfr_reflection_KF_point.
