(** The actual three-premise shared-carrier deduction closes its two output
    witnesses using genuine source ExI rules. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceCommonReflectedLevel SourceCommonReflectedLevelRule SourceCommonReflectedLevelWitness
 SourceCommonLevelPoint SourceOrdinaryReflectionExists SourceLFixed SourceHierarchySyntax
 SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_common_reflected_level_point_recipe M start paramCount reflectCount phi seed oldY beta Y
 common reflection level target law k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 coding_lt M seed k ->coding_lt M oldY k ->coding_lt M beta k ->coding_lt M Y k ->
 source_common_level_point M start paramCount seed oldY common ->
 source_ordinary_reflection_point M(source_L_domain_code M)reflectCount phi seed beta reflection ->
 source_LL_instance M beta Y level ->source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 source_finite_telescope M[common;reflection;level]target law ->source_zfr_provable M law.
Proof.
 intros BF HNames BSeed BOldY BBeta BY HCommon HReflection HLevel HTarget HLaw.
 destruct(source_common_reflected_level_point_total M start paramCount reflectCount phi beta Y)as(point&HPoint).
 destruct(source_finite_telescope_total M[common;reflection;level]point)as(core&HCore).
 pose proof(source_zfr_common_reflected_level_core M start paramCount reflectCount phi seed oldY beta Y
  common reflection level point core k BF HNames BSeed BOldY BBeta BY HCommon HReflection HLevel HPoint HCore)as PCore.
 apply(source_zfr_finite_rule M[core][common;reflection;level]target law k).
 - intros a[<-|[<-|[<-|[]]]].
   + exact(source_common_level_point_bounded M start paramCount seed oldY common k HNames BSeed BOldY HCommon).
   + exact(source_ordinary_reflection_point_bounded M(source_L_domain_code M)reflectCount phi seed beta reflection k
      (numerical_L_domain_bounded M)BF BSeed BBeta HReflection).
   + exact(source_LL_instance_bounded M beta Y level k BBeta BY HLevel).
 - exact(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HTarget).
 - exact HLaw.
 - intros f[<-|[]]. exact PCore.
 - intros b c n BC Laws Premises.
   apply(source_full_common_reflected_level_witness M b c n start paramCount reflectCount phi beta Y point target k
    BF HNames BC HPoint HTarget).
   exact(source_full_finite_telescope_apply M[common;reflection;level]point core HCore b c n
    (Laws core(or_introl eq_refl))Premises).
Qed.
Print Assumptions source_zfr_common_reflected_level_point_recipe.
