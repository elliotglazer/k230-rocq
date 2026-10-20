(** Reduce PH's ordinary geometry list to the actual eight-fact payload
    and one supplied hierarchy, deriving Cover by the fixed ZFR law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalSourceFull
  SourceCofinalGeometry SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations SourceHierarchySyntax
  SourceReflectionGeometryPoint SourceReflectionGeometryElimination SourceReflectionCoverShell
  SourcePropositionalTemplates SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_PH_geometry_payload M K beta Lb member ordinals kf union ob limit memberBeta subsets
    payload lb cover block goal pointLaw law k:
  source_cofinal_ordinals M K ordinals ->
  source_reflection_geometry_instance M ReflectionUnion(source_rec_env2 K beta)union ->
  source_reflection_geometry_instance M ReflectionLimit(fun _=>beta)limit ->
  source_LL_instance M beta Lb lb ->source_cofinal_cover M K Lb cover ->
  code_relation M(source_reflection_geometry_values member ordinals kf union ob limit memberBeta subsets)
    (source_prop_expression source_reflection_geometry_payload)payload ->
  source_bounded M payload k ->source_bounded M lb k ->source_bounded M block k ->source_bounded M goal k ->
  source_finite_telescope M[member;ordinals;cover;ob;subsets;lb;kf;block]goal pointLaw ->
  source_finite_telescope M[payload;lb;block]goal law ->
  source_zfr_provable M pointLaw ->source_zfr_provable M law.
Proof.
  intros HO HU HL HLb HC HGraph BP BL BB BG HPoint HLaw PPoint.
  destruct(source_zfr_reflection_cover_shell M K beta Lb)
    as(ordinals'&union'&limit'&lb'&cover'&coverLaw&HO'&HU'&HL'&HLb'&HC'&HTel&PCover).
  assert(E:ordinals'=ordinals)by(eapply code_relation_functional;eassumption). subst ordinals'.
  assert(E:union'=union)by(eapply code_relation_functional;eassumption). subst union'.
  assert(E:limit'=limit)by(eapply code_relation_functional;eassumption). subst limit'.
  assert(E:lb'=lb)by(eapply source_LL_instance_functional;eassumption). subst lb'.
  assert(E:cover'=cover)by(eapply code_relation_functional;eassumption). subst cover'.
  apply(source_zfr_finite_rule M[coverLaw;pointLaw][payload;lb;block]goal law k).
  - intros f[EF|[EF|[EF|[]]]];subst f;assumption.
  - exact BG.
  - exact HLaw.
  - intros f[EF|[EF|[]]];subst f;assumption.
  - intros b c n BC Laws Premises.
    destruct(source_full_reflection_geometry_leaves M member ordinals kf union ob limit memberBeta subsets
      payload b c n HGraph(Premises payload ltac:(cbn;tauto)))
      as(PMember&POrdinals&PKF&PUnion&POb&PLimit&PMemberBeta&PSubsets).
    assert(PCoverHere:source_full_prv M b c n cover).
    { apply(source_full_finite_telescope_apply M[ordinals;union;limit;lb]cover coverLaw HTel b c n
        (Laws coverLaw ltac:(cbn;tauto))).
      intros f[EF|[EF|[EF|[EF|[]]]]];subst f;try assumption;apply Premises;cbn;tauto. }
    apply(source_full_finite_telescope_apply M[member;ordinals;cover;ob;subsets;lb;kf;block]goal pointLaw HPoint b c n
      (Laws pointLaw ltac:(cbn;tauto))).
    intros f[EF|[EF|[EF|[EF|[EF|[EF|[EF|[EF|[]]]]]]]]];subst f;
      try assumption;apply Premises;cbn;tauto.
Qed.

Print Assumptions source_zfr_PH_geometry_payload.
