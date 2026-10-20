(** The actual ordinal-family proof obtained from the ordinal subcarrier chart. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalSourceFull SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceZFRFiniteRule
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceCofinalOrdinalsShell
 SourceReflectionOrdinalChart SourceReflectionOrdinalChartTransport SourceReflectionOrdinalChartRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_reflection_ordinal_family M Y K chart out law k:
 coding_lt M Y k ->coding_lt M K k ->source_reflection_ordinal_chart M Y K chart ->source_cofinal_ordinals M K out ->
 source_finite_telescope M[chart]out law ->source_zfr_provable M law.
Proof.
 intros BY BK HC HT HLaw.
 pose proof(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC)as BC.
 pose proof(source_cofinal_ordinals_bounded M K out k BK HT)as BT.
 destruct(source_cofinal_ordinals_shell M K out HT)as(guard&point&HG&HP&HAll).
 pose proof(proj1(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HAll)BT)as BPoint.
 destruct(source_reflection_ordinal_chart_total M(succM M Y)(succM M K))as(chartS&HCS).
 pose proof(source_reflection_ordinal_chart_shift M Y K chart chartS HC HCS)as HS.
 destruct(source_finite_telescope_total M[chartS]point)as(branch&HBranch).
 assert(HBranchTel:source_finite_telescope M[chartS;guard](source_ordinal_predicate_code M)branch).
 { apply(source_finite_telescope_prefix M[chartS][guard]point(source_ordinal_predicate_code M)branch HBranch). exists(source_ordinal_predicate_code M). split;[reflexivity|exact HP]. }
 pose proof(source_reflection_ordinal_chart_bounded M(succM M Y)(succM M K)chartS(succM M k)
  (proj2(coding_lt_succ_cancel M Y k)BY)(proj2(coding_lt_succ_cancel M K k)BK)HCS)as BCS.
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ guard(succM M k)(or_introl eq_refl)HG)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M K k)BK)))as BG.
 assert(BO:source_bounded M(source_ordinal_predicate_code M)(succM M k)).
 { exact(source_bounded_monotone M _ (code_numeral M 1)(succM M k)(source_ordinal_predicate_bounded M)
   (proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k))). }
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_finite_rule M[][chartS;guard](source_ordinal_predicate_code M)branch(succM M k)).
   - intros f[<-|[<-|[]]];assumption.
   - exact BO.
   - exact HBranchTel.
   - intros f HF. contradiction.
   - intros b c n BContext Laws Premises.
     destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(memberY&HMY).
     exact(proj2(source_full_reflection_ordinal_chart_out M b c n(succM M Y)(succM M K)chartS(zeroM M)guard memberY(source_ordinal_predicate_code M)
      HCS HG HMY(source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))
      (Premises chartS(or_introl eq_refl))(Premises guard(or_intror(or_introl eq_refl))))). }
 exact(source_zfr_finite_telescope_all M[chart][chartS]point out branch law k
  ltac:(intros f[<-|[]];exact BC)BPoint ltac:(constructor;[exact HS|constructor])HAll HBranch HLaw PBranch).
Qed.
Print Assumptions source_zfr_reflection_ordinal_family.
