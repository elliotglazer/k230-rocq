(** Actual complete geometry payload from ordinal chart,Clos,Ord(seed),and Union. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalInstantiation
 NumericalContexts NumericalSourceFull SourceConjunctionRules SourceFiniteTelescope SourceZFRFiniteRule
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourceOrdinalPredicate SourceDomainInstances SourceRecursionClosureSyntax
 SourceReflectionStep SourceReflectionOrdinalChart SourceReflectionOrdinalChartRules SourceReflectionOrdinalFamily SourceCofinalGeometry
 SourceReflectionKF SourceReflectionKFProof SourceReflectionKFNoLast SourceReflectionGeometryPredicates SourceReflectionUnionShell
 SourceReflectionGeometryPoint SourceReflectionGeometryIntro SourceRecursionPrimitiveRelations SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_reflection_geometry_point M level sb sc count phi a Y K beta chart closure ordA union target law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->coding_lt M beta k ->
 source_reflection_ordinal_chart M Y K chart ->source_rec_closure M phi a Y closure ->numerical_instantiation M(source_ordinal_predicate_code M)a ordA ->
 source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union ->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc count a K beta target ->
 source_finite_telescope M[chart;closure;ordA;union]target law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HMatrix BA BY BK BB HC HClosure HOrdA HUnion HTarget HLaw.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_geometry_point_bounded M(source_L_domain_code M)level sb sc count a K beta target k(numerical_L_domain_bounded M)HL HV BA BK BB HTarget)as BT.
 destruct HTarget as(mAK&ordinals&kf&u&ob&limit&mAB&subsets&HMAK&HOrdinals&HKF&HU&HOB&HLim&HMAB&HSubsets&HPoint).
 assert(E:u=union)by(eapply code_relation_functional;eassumption). subst u.
 destruct(source_zfr_reflection_union_shell M K beta a)as(mAK'&ordinals'&noLast&union'&ob'&limit'&mAB'&subsets'&r1&r2&result&unionLaw&HMAK'&HOrdinals'&HNoLast&HUnion'&HOB'&HLim'&HMAB'&HSubsets'&HR2&HR1&HResult&HUnionLaw&PUnionLaw).
 assert(E:mAK'=mAK)by(eapply sf_relation_functional;eassumption). subst mAK'.
 assert(E:ordinals'=ordinals)by(eapply code_relation_functional;eassumption). subst ordinals'.
 assert(E:union'=union)by(eapply code_relation_functional;eassumption). subst union'.
 assert(E:ob'=ob)by(eapply numerical_instantiation_functional;eassumption). subst ob'.
 assert(E:limit'=limit)by(eapply code_relation_functional;eassumption). subst limit'.
 assert(E:mAB'=mAB)by(eapply sf_relation_functional;eassumption). subst mAB'.
 assert(E:subsets'=subsets)by(eapply code_relation_functional;eassumption). subst subsets'.
 destruct(source_finite_telescope_total M[chart]ordinals)as(ordLaw&HOrdLaw).
 pose proof(source_zfr_reflection_ordinal_family M Y K chart ordinals ordLaw k BY BK HC HOrdinals HOrdLaw)as POrdLaw.
 destruct(source_finite_telescope_total M[chart;closure]kf)as(kfLaw&HKFLaw).
 pose proof(source_zfr_reflection_KF M level sb sc count phi a Y K chart closure kf kfLaw k HLevel HV BP HMatrix BA BY BK HC HClosure HKF HKFLaw)as PKFLaw.
 destruct(source_finite_telescope_total M[kf]noLast)as(nlLaw&HNLaw).
 pose proof(source_zfr_reflection_KF_no_last M(source_L_domain_code M)level sb sc count K kf noLast nlLaw k(numerical_L_domain_bounded M)HL HV BK HKF HNoLast HNLaw)as PNLaw.
 pose proof(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC)as BChart.
 pose proof(source_rec_closure_bounded M phi a Y closure k BP BA BY HClosure)as BClosure.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)a ordA k(source_ordinal_predicate_bounded M)BA HOrdA)as BOrdA.
 assert(BNames:forall i,(i<2)%nat ->coding_lt M(source_rec_env2 K beta i)k)by(intros[|i]HI;[exact BK|exact BB]).
 pose proof(source_reflection_geometry_instance_bounded M ReflectionUnion(source_rec_env2 K beta)union k BNames HUnion)as BUnion.
 pose proof(proj2(source_bounded_accept_atom M SFMember a K mAK k(or_introl eq_refl)HMAK)(conj BA BK))as BMAK.
 pose proof(source_cofinal_ordinals_bounded M K ordinals k BK HOrdinals)as BOrdinals.
 pose proof(source_reflection_KF_bounded M(source_L_domain_code M)level sb sc count K kf k(numerical_L_domain_bounded M)HL HV BK HKF)as BKF.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob k(source_ordinal_predicate_bounded M)BB HOB)as BOB.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionLimit(fun _=>beta)limit k ltac:(intros i HI;exact BB)HLim)as BLimit.
 pose proof(proj2(source_bounded_accept_atom M SFMember a beta mAB k(or_introl eq_refl)HMAB)(conj BA BB))as BMAB.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets k BNames HSubsets)as BSubsets.
 assert(BValues:forall i,source_bounded M(source_reflection_geometry_values mAK ordinals kf union ob limit mAB subsets i)k).
 { intros[|[|[|[|[|[|[|i]]]]]]];cbn[source_reflection_geometry_values];assumption. }
 apply(source_zfr_finite_rule M[ordLaw;kfLaw;nlLaw;unionLaw][chart;closure;ordA;union]target law k).
 - intros f[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros f[<-|[<-|[<-|[<-|[]]]]];assumption.
 - intros b c n BC Laws Premises.
   assert(POrdinals:source_full_prv M b c n ordinals).
   { apply(source_full_finite_telescope_apply M[chart]ordinals ordLaw HOrdLaw b c n(Laws ordLaw ltac:(cbn;tauto))). intros f[<-|[]]. apply Premises. now left. }
   assert(PKF:source_full_prv M b c n kf).
   { apply(source_full_finite_telescope_apply M[chart;closure]kf kfLaw HKFLaw b c n(Laws kfLaw ltac:(cbn;tauto))). intros f HF. apply Premises. cbn in HF|-*. tauto. }
   assert(PNoLast:source_full_prv M b c n noLast).
   { apply(source_full_finite_telescope_apply M[kf]noLast nlLaw HNLaw b c n(Laws nlLaw ltac:(cbn;tauto))). intros f[<-|[]]. exact PKF. }
   pose proof HClosure as HCGraph. destruct HCGraph as(initial&guard&binary&member&body&ex&point&all&HInitial&HG&HB&HM&HBody&HEx&HP&HA&HClose).
   pose proof(source_full_conjunction_left M b c n initial all closure HClose(Premises closure ltac:(cbn;tauto)))as PInitial.
   pose proof(source_full_reflection_ordinal_chart_in M b c n Y K chart a mAK initial ordA HC HMAK HInitial HOrdA
    (Premises chart ltac:(cbn;tauto))PInitial(Premises ordA ltac:(cbn;tauto)))as PMAK.
   assert(PResult:source_full_prv M b c n result).
   { apply(source_full_finite_telescope_apply M[mAK;ordinals;noLast;union]result unionLaw HUnionLaw b c n(Laws unionLaw ltac:(cbn;tauto))).
     intros f[<-|[<-|[<-|[<-|[]]]]];first[assumption|apply Premises;cbn;tauto]. }
   pose proof(source_full_conjunction_left M b c n ob r1 result HResult PResult)as POB.
   pose proof(source_full_conjunction_right M b c n ob r1 result HResult PResult)as PR1.
   pose proof(source_full_conjunction_left M b c n limit r2 r1 HR1 PR1)as PLimit.
   pose proof(source_full_conjunction_right M b c n limit r2 r1 HR1 PR1)as PR2.
   pose proof(source_full_conjunction_left M b c n mAB subsets r2 HR2 PR2)as PMAB.
   pose proof(source_full_conjunction_right M b c n mAB subsets r2 HR2 PR2)as PSubsets.
   exact(source_full_reflection_geometry_intro M b c n mAK ordinals kf union ob limit mAB subsets target k BValues BC HPoint
    PMAK POrdinals PKF(Premises union ltac:(cbn;tauto))POB PLimit PMAB PSubsets).
Qed.
Print Assumptions source_zfr_reflection_geometry_point.
