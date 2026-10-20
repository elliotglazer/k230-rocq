(** Eliminate the new hierarchy-carrier witness in the shared reflection
    argument. Hierarchy existence and every shifted point are constructed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceLFixed SourceCommonLevelPoint SourceCommonLevelWitness SourceCommonLevelShift
 SourceCommonReflectedLevel SourceCommonReflectedLevelShift SourceCommonReflectedLevelPointRecipe
 SourceOrdinaryReflectionExists SourceOrdinaryReflectionWitnessOpening SourceHierarchySyntax SourceHierarchyExistsShell
 SourceOrdinalPredicate NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenaming RenamingSubstitution SourceRecursionShiftGraphs SourceQuantifierRules SourceFiniteTelescope
 SourceFiniteTelescopeExists SourceZFRFiniteRule SourceZFRProvability SourceConjunctionRules SourceDerivedRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.
Theorem source_zfr_common_reflected_level_eliminate_LL M start paramCount reflectCount phi seed oldY beta
 common reflection target law k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 coding_lt M seed k ->coding_lt M oldY k ->coding_lt M beta k ->
 source_common_level_point M start paramCount seed oldY common ->
 source_ordinary_reflection_point M(source_L_domain_code M)reflectCount phi seed beta reflection ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 source_finite_telescope M[common;reflection]target law ->source_zfr_provable M law.
Proof.
 intros BF HNames BS BOldY BB HCommon HReflection HTarget HLaw.
 pose proof(source_common_level_point_bounded M start paramCount seed oldY common k HNames BS BOldY HCommon)as BC.
 pose proof(source_ordinary_reflection_point_bounded M(source_L_domain_code M)reflectCount phi seed beta reflection k
  (numerical_L_domain_bounded M)BF BS BB HReflection)as BR.
 pose proof(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HTarget)as BT.
 assert(HNamesS:forall i,coding_lt M i paramCount ->coding_lt M(addM M i(succM M start))(succM M k)).
 { intros i HI. rewrite source_common_add_successor. exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)). }
 destruct(source_common_level_point_total M(succM M start)paramCount(succM M seed)(succM M oldY))as(commonS&HCommonS).
 destruct(source_ordinary_reflection_point_total M(source_L_domain_code M)reflectCount phi(succM M seed)(succM M beta))as(reflectionS&HReflectionS).
 destruct(source_common_reflected_level_recipe_total M(succM M start)paramCount reflectCount phi)as(targetS&HTargetS).
 pose proof(source_common_level_point_shift M start paramCount seed oldY common commonS HCommon HCommonS)as SC.
 assert(SR:source_formula_shift M reflection reflectionS).
 { apply(proj2(numerical_renaming_empty_substitution M reflection(zeroM M)(zeroM M)(code_numeral M 1)reflectionS)).
   exact(source_ordinary_reflection_point_substitution M(source_L_domain_code M)reflectCount phi seed beta reflection
    (succM M seed)(succM M beta)reflectionS(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (numerical_L_domain_bounded M)BF HReflection HReflectionS(source_rec_shift_lookup M seed)(source_rec_shift_lookup M beta)). }
 pose proof(source_common_reflected_level_recipe_shift M start paramCount reflectCount phi target targetS BF HTarget HTargetS)as ST.
 destruct(source_zfr_hierarchy_exists_shell M beta)as(ordinal&body&exLL&existsLaw&HExists&PExists).
 destruct HExists as(HOrdinal&HBody&HEx&HExistsImpl).
 destruct(source_finite_telescope_total M[commonS;reflectionS;body]targetS)as(branch&HBranch).
 pose proof(source_zfr_common_reflected_level_point_recipe M(succM M start)paramCount reflectCount phi
  (succM M seed)(succM M oldY)(succM M beta)(zeroM M)commonS reflectionS body targetS branch(succM M k)
  BF HNamesS(proj2(coding_lt_succ_cancel M seed k)BS)(proj2(coding_lt_succ_cancel M oldY k)BOldY)
  (proj2(coding_lt_succ_cancel M beta k)BB)(coding_zero_lt_succ M k)HCommonS HReflectionS HBody HTargetS HBranch)as PBranch.
 assert(BEx:source_bounded M exLL k).
 { apply(proj2(source_bounded_accept_unary M SFEx body exLL k(or_intror eq_refl)HEx)).
   exact(source_LL_instance_bounded M(succM M beta)(zeroM M)body(succM M k)
    (proj2(coding_lt_succ_cancel M beta k)BB)(coding_zero_lt_succ M k)HBody). }
 destruct(source_finite_telescope_total M[common;reflection;exLL]target)as(withEx&HWithEx).
 assert(PWithEx:source_zfr_provable M withEx).
 { apply(source_zfr_finite_telescope_exists M[common;reflection][commonS;reflectionS]body exLL target targetS branch withEx k).
   - intros a[<-|[<-|[]]];assumption.
   - exact BEx.
   - exact BT.
   - constructor;[exact SC|]. constructor;[exact SR|constructor].
   - exact HEx.
   - exact ST.
   - exact HBranch.
   - exact HWithEx.
   - exact PBranch. }
 apply(source_zfr_finite_rule M[existsLaw;withEx][common;reflection]target law k).
 - intros a[<-|[<-|[]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros f[<-|[<-|[]]];assumption.
 - intros b c n BContext Laws Premises.
   pose proof HReflection as(o&limit&member&refl&tail&middle&HO&HL&HM&HR&HT&HMid&HOut).
   pose proof(numerical_instantiation_functional M _ beta ordinal o HOrdinal HO)as E;subst o.
   assert(PReflection:NumericalSourceFull.source_full_prv M b c n reflection)by(apply Premises;right;now left).
   pose proof(source_full_conjunction_left M b c n ordinal middle reflection HOut PReflection)as PO.
   pose proof(source_full_modus_ponens M b c n ordinal exLL existsLaw HExistsImpl
    (Laws existsLaw(or_introl eq_refl))PO)as PEx.
   apply(source_full_finite_telescope_apply M[common;reflection;exLL]target withEx HWithEx b c n
    (Laws withEx(or_intror(or_introl eq_refl)))).
   intros f[<-|[<-|[<-|[]]]];[apply Premises;now left|exact PReflection|exact PEx].
Qed.
Print Assumptions source_zfr_common_reflected_level_eliminate_LL.
