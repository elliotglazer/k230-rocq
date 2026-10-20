(** Genuine uniform ordinary reflection in every PA model. Both geometry
    witnesses are eliminated by actual source ExE rules; the conclusion keeps
    Ord(beta), Lim(beta), seed in beta and the literal ordinary Refl formula. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalInstantiation NumericalSourceFull SourceDomainInstances SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax
 SourcePCSTables SourcePieceConjunctionBounds SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceReflectionGeometryRecipe SourceReflectionGeometryTheorem SourceGeometryReflectionExists
 SourceOrdinaryReflectionExists SourceOrdinaryReflectionExistsTransport SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.

Theorem source_zfr_ordinary_reflection_exists_at_table M level sb sc pieces phi count seed ordinal target law:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_bounded M phi count ->
 source_pcs_table M(source_L_domain_code M)phi count sb sc pieces ->
 numerical_instantiation M(source_ordinal_predicate_code M)seed ordinal ->
 source_ordinary_reflection_exists M(source_L_domain_code M)count phi seed target ->
 source_finite_telescope M[ordinal]target law ->source_zfr_provable M law.
Proof.
 intros HLg HP HPCS HO HT HLaw.
 pose proof(numerical_L_domain_bounded M)as HD.
 pose proof(source_pcs_table_valid M(source_L_domain_code M)phi count sb sc pieces HD HP HPCS)as HV.
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLg)as HL.
 set(k:=succM M seed).
 assert(BSeed:coding_lt M seed k)by(apply coding_lt_succ).
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)seed ordinal k
  (source_ordinal_predicate_bounded M)BSeed HO)as BO.
 pose proof(source_ordinary_reflection_exists_bounded M(source_L_domain_code M)count phi seed target k HD HP BSeed HT)as BT.
 destruct(source_reflection_geometry_recipe_total M(source_L_domain_code M)level sb sc pieces seed)as(geometry&HGeometry).
 pose proof(source_reflection_geometry_recipe_bounded M(source_L_domain_code M)level sb sc pieces seed geometry k HD HL HV BSeed HGeometry)as BG.
 destruct(source_finite_telescope_total M[ordinal]geometry)as(geometryLaw&HGeometryLaw).
 pose proof(source_zfr_reflection_geometry M level sb sc pieces seed ordinal geometry geometryLaw HLg HV HO HGeometry HGeometryLaw)as PGeometryLaw.
 pose proof HGeometry as(body&inner&HBody&HInnerEx&HOuterEx).
 pose proof(proj1(source_bounded_accept_unary M SFEx inner geometry k(or_intror eq_refl)HOuterEx)BG)as BInner.
 destruct(source_ordinary_reflection_exists_total M(source_L_domain_code M)count phi(succM M seed))as(targetS&HTS).
 destruct(source_ordinary_reflection_exists_total M(source_L_domain_code M)count phi(succM M(succM M seed)))as(targetSS&HTSS).
 pose proof(source_ordinary_reflection_exists_shift M(source_L_domain_code M)count phi seed target targetS HD HP HT HTS)as ST.
 pose proof(source_ordinary_reflection_exists_shift M(source_L_domain_code M)count phi(succM M seed)targetS targetSS HD HP HTS HTSS)as STS.
 pose proof(source_ordinary_reflection_exists_bounded M(source_L_domain_code M)count phi(succM M seed)targetS(succM M k)
  HD HP(proj2(coding_lt_succ_cancel M seed k)BSeed)HTS)as BTS.
 destruct(source_finite_telescope_total M[body]targetSS)as(branch&HBranch).
 pose proof(source_zfr_geometry_reflection_exists M level sb sc pieces phi count(succM M(succM M seed))(code_numeral M 1)
  body targetSS branch HL HLg HP HPCS HBody HTSS HBranch)as PBranch.
 destruct(source_finite_telescope_total M[inner]targetS)as(innerLaw&HInnerLaw).
 assert(PInnerLaw:source_zfr_provable M innerLaw).
 { apply(source_zfr_finite_telescope_exists M[][]body inner targetS targetSS branch innerLaw(succM M k)).
   - intros a HA. contradiction.
   - exact BInner.
   - exact BTS.
   - constructor.
   - exact HInnerEx.
   - exact STS.
   - exact HBranch.
   - exact HInnerLaw.
   - exact PBranch. }
 destruct(source_finite_telescope_total M[geometry]target)as(outerLaw&HOuterLaw).
 assert(POuterLaw:source_zfr_provable M outerLaw).
 { apply(source_zfr_finite_telescope_exists M[][]inner geometry target targetS innerLaw outerLaw k).
   - intros a HA. contradiction.
   - exact BG.
   - exact BT.
   - constructor.
   - exact HOuterEx.
   - exact ST.
   - exact HInnerLaw.
   - exact HOuterLaw.
   - exact PInnerLaw. }
 apply(source_zfr_finite_rule M[geometryLaw;outerLaw][ordinal]target law k).
 - intros a[EA|[]]. now subst a.
 - exact BT.
 - exact HLaw.
 - intros a[EA|[EA|[]]];subst a;assumption.
 - intros b c n BC Laws Premises.
   pose proof(source_full_finite_telescope_apply M[ordinal]geometry geometryLaw HGeometryLaw b c n
    (Laws geometryLaw(or_introl eq_refl))Premises)as PGeometry.
   apply(source_full_finite_telescope_apply M[geometry]target outerLaw HOuterLaw b c n
    (Laws outerLaw(or_intror(or_introl eq_refl)))).
   intros a[EA|[]]. now subst a.
Qed.

Theorem source_zfr_ordinary_reflection_exists M phi count seed ordinal target law:
 source_bounded M phi count ->numerical_instantiation M(source_ordinal_predicate_code M)seed ordinal ->
 source_ordinary_reflection_exists M(source_L_domain_code M)count phi seed target ->
 source_finite_telescope M[ordinal]target law ->source_zfr_provable M law.
Proof.
 intros HP HO HT HLaw.
 destruct(source_pcs_table_total M(source_L_domain_code M)phi count)as(sb&sc&pieces&HPCS).
 destruct(source_LL_instance_total M(code_numeral M 1)(zeroM M))as(level&HLg).
 exact(source_zfr_ordinary_reflection_exists_at_table M level sb sc pieces phi count seed ordinal target law HLg HP HPCS HO HT HLaw).
Qed.

Theorem source_zfr_ordinary_reflection_exists_total M phi count seed:
 source_bounded M phi count ->exists ordinal target law,
 numerical_instantiation M(source_ordinal_predicate_code M)seed ordinal /\
 source_ordinary_reflection_exists M(source_L_domain_code M)count phi seed target /\
 sf_relation M SFImpl ordinal target law /\source_zfr_provable M law.
Proof.
 intro HP.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)seed)as(ordinal&HO).
 destruct(source_ordinary_reflection_exists_total M(source_L_domain_code M)count phi seed)as(target&HT).
 destruct(sf_relation_total M SFImpl ordinal target)as(law&HImpl).
 exists ordinal,target,law. split;[exact HO|]. split;[exact HT|]. split;[exact HImpl|].
 apply(source_zfr_ordinary_reflection_exists M phi count seed ordinal target law HP HO HT).
 exists target. split;[reflexivity|exact HImpl].
Qed.
Print Assumptions source_zfr_ordinary_reflection_exists_at_table.
Print Assumptions source_zfr_ordinary_reflection_exists.
Print Assumptions source_zfr_ordinary_reflection_exists_total.
