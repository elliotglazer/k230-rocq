(** Actual introduction of an ordinal/limit/member/reflection witness from
    completed geometry, using the union ordinal at variable zero. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation
 SourceBounded NumericalContexts NumericalSourceFull SourceFiniteFamilyBounds SourceFiniteTelescope SourceZFRFiniteRule
 SourceLFixed SourceHierarchySyntax SourcePCSTables SourcePieceConjunctionBounds SourceOrdinalPredicate
 SourceReflectionGeometryPoint SourceReflectionGeometryElimination SourceReflectionGeometryPredicates
 SourceGeometryOrdinaryReflection SourceOrdinaryReflectionSyntax SourceOrdinaryReflectionExists
 SourceOrdinaryReflectionExistsTransport SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_zfr_geometry_reflection_exists M level sb sc pieces phi count seed K geometry target law:
 source_bounded M level(code_numeral M 2) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
 source_bounded M phi count ->source_pcs_table M(source_L_domain_code M)phi count sb sc pieces ->
 source_reflection_geometry_point M(source_L_domain_code M)level sb sc pieces seed K(zeroM M)geometry ->
 source_ordinary_reflection_exists M(source_L_domain_code M)count phi seed target ->
 source_finite_telescope M[geometry]target law ->source_zfr_provable M law.
Proof.
 intros HL HLg HP HPCS HG HTarget HLaw.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(source_pcs_table_valid M(source_L_domain_code M)phi count sb sc pieces HD HP HPCS)as HV.
 destruct(source_finite_names_bound M[seed;K;zeroM M])as(k&BN).
 assert(BSeed:coding_lt M seed k)by(apply BN;cbn;tauto).
 assert(BK:coding_lt M K k)by(apply BN;cbn;tauto).
 assert(BZero:coding_lt M(zeroM M)k)by(apply BN;cbn;tauto).
 pose proof(source_reflection_geometry_point_bounded M(source_L_domain_code M)level sb sc pieces
  seed K(zeroM M)geometry k HD HL HV BSeed BK BZero HG)as BG.
 pose proof(source_ordinary_reflection_exists_bounded M(source_L_domain_code M)count phi seed target k HD HP BSeed HTarget)as BT.
 destruct(source_ordinary_reflection_point_total M(source_L_domain_code M)count phi seed(zeroM M))as(point&HPoint).
 pose proof(source_ordinary_reflection_point_bounded M(source_L_domain_code M)count phi seed(zeroM M)point k HD HP BSeed BZero HPoint)as BP.
 pose proof HPoint as(ordinal&limit&member&refl&tail&middle&HO&HLim&HM&HRefl&HTail&HMiddle&HOut).
 destruct(source_finite_telescope_total M[geometry]refl)as(reflLaw&HReflLaw).
 pose proof(source_zfr_geometry_ordinary_reflection M level sb sc pieces phi count seed K(zeroM M)geometry refl reflLaw
  HL HLg HP HPCS HG HRefl HReflLaw)as PReflLaw.
 apply(source_zfr_finite_rule M[reflLaw][geometry]target law k).
 - intros a[EA|[]]. now subst a.
 - exact BT.
 - exact HLaw.
 - intros a[EA|[]]. now subst a.
 - intros b c n BC Laws Premises.
   pose proof(Premises geometry(or_introl eq_refl))as PGeometry.
   pose proof(source_full_finite_telescope_apply M[geometry]refl reflLaw HReflLaw b c n
    (Laws reflLaw(or_introl eq_refl))Premises)as PRefl.
   destruct(source_full_reflection_geometry_point_facts M(source_L_domain_code M)level sb sc pieces
    seed K(zeroM M)geometry b c n HG PGeometry)
    as(m&o&kf&u&ob&l&mb&s&HMemberK&HOrdK&HKF&HU&HOB&HLGeo&HMB&HS&PM&PO&PKF&PU&POB&PL&PMB&PS).
   pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(zeroM M)ob ordinal HOB HO)as E. subst ob.
   pose proof(code_relation_functional M _ (fun _=>zeroM M)l limit HLGeo HLim)as E. subst l.
   pose proof(sf_relation_functional M SFMember seed(zeroM M)mb member HMB HM)as E. subst mb.
   pose proof(proj1(source_bounded_accept_binary M SFAnd ordinal middle point k(or_introl eq_refl)HOut)BP)as(BO&BMiddle).
   pose proof(proj1(source_bounded_accept_binary M SFAnd limit tail middle k(or_introl eq_refl)HMiddle)BMiddle)as(BLimit&BTail).
   pose proof(full_source_CI M b c n member refl tail(ex_intro _ k(conj BTail BC))PMB PRefl HTail)as PTail.
   pose proof(full_source_CI M b c n limit tail middle(ex_intro _ k(conj BMiddle BC))PL PTail HMiddle)as PMiddle.
   pose proof(full_source_CI M b c n ordinal middle point(ex_intro _ k(conj BP BC))POB PMiddle HOut)as PPoint.
   destruct HTarget as(body&HBody&HEx).
   pose proof(source_ordinary_reflection_exists_instance_zero M(source_L_domain_code M)count phi seed body target point
    HD HP HBody HEx HPoint)as HInstance.
   exact(full_source_ExI M b c n body target(zeroM M)point(ex_intro _ k(conj BT BC))PPoint HEx HInstance).
Qed.
Print Assumptions source_zfr_geometry_reflection_exists.
