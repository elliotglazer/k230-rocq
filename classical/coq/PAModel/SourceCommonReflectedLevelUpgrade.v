(** A real ZFR proof upgrades any common L-level to one reflecting the
    arbitrary internal matrix. Both new witnesses are eliminated, and the
    reflection theorem is generated from the matrix's numerical bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceLFixed SourceCommonLevelPoint SourceCommonLevelWitness SourceCommonLevelShift
 SourceCommonReflectedLevel SourceCommonReflectedLevelShift SourceCommonReflectedLevelLL
 SourceOrdinaryReflectionExists SourceUniformOrdinaryReflection SourceOrdinalPredicate NumericalInstantiation
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule SourceZFRProvability SourceConjunctionRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_common_reflected_level_upgrade M start paramCount reflectCount phi seed oldY common target law k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->coding_lt M seed k ->coding_lt M oldY k ->
 source_common_level_point M start paramCount seed oldY common ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 source_finite_telescope M[common]target law ->source_zfr_provable M law.
Proof.
 intros BF HNames BS BY HCommon HTarget HLaw.
 pose proof(source_common_level_point_bounded M start paramCount seed oldY common k HNames BS BY HCommon)as BC.
 pose proof(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HTarget)as BT.
 assert(HNamesS:forall i,coding_lt M i paramCount ->coding_lt M(addM M i(succM M start))(succM M k)).
 { intros i HI. rewrite source_common_add_successor. exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)). }
 destruct(source_common_level_point_total M(succM M start)paramCount(succM M seed)(succM M oldY))as(commonS&HCommonS).
 destruct(source_common_reflected_level_recipe_total M(succM M start)paramCount reflectCount phi)as(targetS&HTargetS).
 pose proof(source_common_level_point_shift M start paramCount seed oldY common commonS HCommon HCommonS)as SC.
 pose proof(source_common_reflected_level_recipe_shift M start paramCount reflectCount phi target targetS BF HTarget HTargetS)as ST.
 destruct(source_ordinary_reflection_exists_total M(source_L_domain_code M)reflectCount phi seed)as(existsRefl&HExists).
 pose proof HExists as(body&HBody&HEx).
 pose proof(source_ordinary_reflection_exists_bounded M(source_L_domain_code M)reflectCount phi seed existsRefl k
  (numerical_L_domain_bounded M)BF BS HExists)as BE.
 destruct(source_finite_telescope_total M[commonS;body]targetS)as(branch&HBranch).
 pose proof(source_zfr_common_reflected_level_eliminate_LL M(succM M start)paramCount reflectCount phi
  (succM M seed)(succM M oldY)(zeroM M)commonS body targetS branch(succM M k)
  BF HNamesS(proj2(coding_lt_succ_cancel M seed k)BS)(proj2(coding_lt_succ_cancel M oldY k)BY)
  (coding_zero_lt_succ M k)HCommonS HBody HTargetS HBranch)as PBranch.
 destruct(source_finite_telescope_total M[common;existsRefl]target)as(withEx&HWithEx).
 assert(PWithEx:source_zfr_provable M withEx).
 { apply(source_zfr_finite_telescope_exists M[common][commonS]body existsRefl target targetS branch withEx k).
   - intros a[<-|[]]. exact BC.
   - exact BE.
   - exact BT.
   - constructor;[exact SC|constructor].
   - exact HEx.
   - exact ST.
   - exact HBranch.
   - exact HWithEx.
   - exact PBranch. }
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)seed)as(ordinal&HOrdinal).
 destruct(source_finite_telescope_total M[ordinal]existsRefl)as(reflLaw&HReflLaw).
 pose proof(source_zfr_ordinary_reflection_exists M phi reflectCount seed ordinal existsRefl reflLaw
  BF HOrdinal HExists HReflLaw)as PReflLaw.
 apply(source_zfr_finite_rule M[reflLaw;withEx][common]target law k).
 - intros a[<-|[]]. exact BC.
 - exact BT.
 - exact HLaw.
 - intros f[<-|[<-|[]]];assumption.
 - intros b c n BContext Laws Premises.
   pose proof HCommon as(members&oldOrdinal&level&pair&HM&HO&HL&HP&HOut).
   pose proof(numerical_instantiation_functional M _ seed ordinal oldOrdinal HOrdinal HO)as E;subst oldOrdinal.
   assert(PCommon:NumericalSourceFull.source_full_prv M b c n common)by(apply Premises;now left).
   pose proof(source_full_conjunction_left M b c n pair members common HOut PCommon)as PPair.
   pose proof(source_full_conjunction_left M b c n ordinal level pair HP PPair)as POrdinal.
   assert(PExists:NumericalSourceFull.source_full_prv M b c n existsRefl).
   { apply(source_full_finite_telescope_apply M[ordinal]existsRefl reflLaw HReflLaw b c n(Laws reflLaw(or_introl eq_refl))).
     intros f[<-|[]]. exact POrdinal. }
   apply(source_full_finite_telescope_apply M[common;existsRefl]target withEx HWithEx b c n
    (Laws withEx(or_intror(or_introl eq_refl)))).
   intros f[<-|[<-|[]]];assumption.
Qed.
Print Assumptions source_zfr_common_reflected_level_upgrade.
