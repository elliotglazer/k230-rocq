(** Genuine uniform shared reflected-level existence in any PA model.
    Every common-level, reflecting-ordinal and hierarchy-carrier witness
    is removed by actual source proof rules. Both counts may be internal
    and are independent. No image-family or per-matrix proof premise occurs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceLFixed SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelWitness SourceCommonLevelInduction
 SourceCommonLevelSuccessorZFR SourceCommonReflectedLevel SourceCommonReflectedLevelShift SourceCommonReflectedLevelUpgrade
 SourcePredicateBlocks SourcePredicateBlockProofs SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceZFRProvability SourceDerivedRules NumericalSourceFull.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_common_reflected_level_from_common M start paramCount reflectCount phi common target law k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 source_common_level_recipe M start paramCount common ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 source_finite_telescope M[common]target law ->source_zfr_provable M law.
Proof.
 intros BF HNames HCommon HTarget HLaw.
 pose proof(source_common_level_recipe_bounded M start paramCount common k HNames HCommon)as BC.
 pose proof(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HTarget)as BT.
 destruct(source_common_level_recipe_shell M start paramCount common HCommon)as(matrix&inner&HM&HY&HO).
 pose proof(proj1(source_bounded_accept_unary M SFEx inner common k(or_intror eq_refl)HO)BC)as BI.
 destruct(source_common_reflected_level_recipe_total M(succM M start)paramCount reflectCount phi)as(targetS&HTargetS).
 destruct(source_common_reflected_level_recipe_total M(succM M(succM M start))paramCount reflectCount phi)as(targetSS&HTargetSS).
 pose proof(source_common_reflected_level_recipe_shift M start paramCount reflectCount phi target targetS BF HTarget HTargetS)as ST.
 pose proof(source_common_reflected_level_recipe_shift M(succM M start)paramCount reflectCount phi targetS targetSS BF HTargetS HTargetSS)as STS.
 assert(HNamesS:forall i,coding_lt M i paramCount ->coding_lt M(addM M i(succM M start))(succM M k)).
 { intros i HI. rewrite source_common_add_successor. exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)). }
 assert(HNamesSS:forall i,coding_lt M i paramCount ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M k))).
 { intros i HI. rewrite source_common_add_successor. exact(proj2(coding_lt_succ_cancel M(addM M i(succM M start))(succM M k))(HNamesS i HI)). }
 pose proof(source_common_reflected_level_recipe_bounded M(succM M start)paramCount reflectCount phi targetS(succM M k)
  BF HNamesS HTargetS)as BTS.
 destruct(source_finite_telescope_total M[matrix]targetSS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_common_reflected_level_upgrade M(succM M(succM M start))paramCount reflectCount phi
    (code_numeral M 1)(zeroM M)matrix targetSS branch(succM M(succM M k))BF HNamesSS).
   - change(coding_lt M(succM M(zeroM M))(succM M(succM M k))).
     apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ.
   - apply coding_zero_lt_succ.
   - exact HM.
   - exact HTargetSS.
   - exact HBranch. }
 destruct(source_finite_telescope_total M[inner]targetS)as(innerLaw&HInnerLaw).
 assert(PInner:source_zfr_provable M innerLaw).
 { apply(source_zfr_finite_telescope_exists M[][]matrix inner targetS targetSS branch innerLaw(succM M k)).
   - intros a HA. contradiction.
   - exact BI.
   - exact BTS.
   - constructor.
   - exact HY.
   - exact STS.
   - exact HBranch.
   - exact HInnerLaw.
   - exact PBranch. }
 apply(source_zfr_finite_telescope_exists M[][]inner common target targetS innerLaw law k).
 - intros a HA. contradiction.
 - exact BC.
 - exact BT.
 - constructor.
 - exact HO.
 - exact ST.
 - exact HInnerLaw.
 - exact HLaw.
 - exact PInner.
Qed.
Theorem source_zfr_common_reflected_level_exists M start paramCount reflectCount phi block target law:
 source_bounded M phi reflectCount ->
 source_predicate_block M start(source_L_domain_code M)paramCount block ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 sf_relation M SFImpl block target law ->source_zfr_provable M law.
Proof.
 intros BF HBlock HTarget HLaw.
 set(k:=succM M(addM M paramCount start)).
 assert(HNames:forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k).
 { intros i HI. apply(source_common_parameter_bound M i paramCount start).
   exact(coding_lt_trans M i paramCount(succM M paramCount)HI(coding_lt_succ M paramCount)). }
 destruct(source_common_level_recipe_total M start paramCount)as(common&HCommon).
 destruct(sf_relation_total M SFImpl block common)as(commonLaw&HCommonLaw).
 pose proof(source_zfr_common_level_from_L_parameters M start paramCount block common commonLaw HBlock HCommon HCommonLaw)as PCommonLaw.
 destruct(source_finite_telescope_total M[common]target)as(upgrade&HUpgrade).
 pose proof(source_zfr_common_reflected_level_from_common M start paramCount reflectCount phi common target upgrade k
  BF HNames HCommon HTarget HUpgrade)as PUpgrade.
 apply(source_zfr_finite_rule M[commonLaw;upgrade][block]target law k).
 - intros a[<-|[]]. exact(source_predicate_block_bound M start(source_L_domain_code M)paramCount block k
    HNames(numerical_L_domain_bounded M)HBlock).
 - exact(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HTarget).
 - exists target. split;[reflexivity|exact HLaw].
 - intros f[<-|[<-|[]]];assumption.
 - intros b c n BC Laws Premises.
   assert(PBlock:source_full_prv M b c n block)by(apply Premises;now left).
   pose proof(source_full_modus_ponens M b c n block common commonLaw HCommonLaw
    (Laws commonLaw(or_introl eq_refl))PBlock)as PCommon.
   apply(source_full_finite_telescope_apply M[common]target upgrade HUpgrade b c n(Laws upgrade(or_intror(or_introl eq_refl)))).
   intros f[<-|[]]. exact PCommon.
Qed.
Print Assumptions source_zfr_common_reflected_level_from_common.
Print Assumptions source_zfr_common_reflected_level_exists.
