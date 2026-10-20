(** Genuine two-existential introduction of a common reflected level. The
    varying matrix is unchanged by the surrounding parameter binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceCommonReflectedLevel SourceCommonLevelWitness SourceSequents SourceQuantifierRules
 NumericalContexts NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
 SourceInstantiationConstructors.
Unset Implicit Arguments.
Theorem source_common_reflected_level_witness_instances M start paramCount reflectCount phi beta Y point target:
 source_bounded M phi reflectCount ->
 source_common_reflected_level_point M start paramCount reflectCount phi beta Y point ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 exists matrix exY matrixD exYD,
 sf_relation M SFEx matrix(zeroM M)exY /\sf_relation M SFEx exY(zeroM M)target /\
 sf_relation M SFEx matrixD(zeroM M)exYD /\numerical_instantiation M exY beta exYD /\
 numerical_instantiation M matrixD Y point.
Proof.
 intros BF HPoint(matrix&exY&HM&HY&HT).
 destruct(source_common_reflected_level_point_total M(succM M start)paramCount reflectCount phi(succM M beta)(zeroM M))as(matrixD&HMD).
 destruct(sf_relation_total M SFEx matrixD(zeroM M))as(exYD&HYD).
 exists matrix,exY,matrixD,exYD. split;[exact HY|]. split;[exact HT|]. split;[exact HYD|]. split.
 - destruct(substitution_singleton_total M beta)as(b&c&HH&HTail).
   destruct(substitution_lift_total M b c(succM M(zeroM M))(zeroM M))as(u&v&l&HLift).
   exists b,c. split;[exact HH|].
   apply(proj2(numerical_substitution_quantifier M false matrix exY b c(succM M(zeroM M))(zeroM M)exYD HY)).
   exists u,v,l,matrixD. split;[exact HLift|]. split;[|exact HYD].
   apply(source_common_reflected_level_point_substitution M(succM M(succM M start))paramCount reflectCount phi
    (code_numeral M 1)(zeroM M)matrix(succM M start)(succM M beta)(zeroM M)matrixD u v l(succM M(zeroM M))BF HM HMD).
   + apply(proj2(substitution_lift_tail M b c(succM M(zeroM M))(zeroM M)u v l(zeroM M)beta HLift)). exact HH.
   + apply(proj2(substitution_lift_head M b c(succM M(zeroM M))(zeroM M)u v l(zeroM M)HLift)). reflexivity.
   + intros i HI. rewrite !source_common_add_successor.
     apply(proj2(substitution_lift_tail M b c(succM M(zeroM M))(zeroM M)u v l
      (succM M(addM M i start))(addM M i start)HLift)). exact(HTail(addM M i start)).
 - destruct(substitution_singleton_total M Y)as(b&c&HH&HTail).
   exists b,c. split;[exact HH|].
   apply(source_common_reflected_level_point_substitution M(succM M start)paramCount reflectCount phi
    (succM M beta)(zeroM M)matrixD start beta Y point b c(succM M(zeroM M))(zeroM M)BF HMD HPoint).
   + exact(HTail beta).
   + exact HH.
   + intros i HI. rewrite source_common_add_successor. exact(HTail(addM M i start)).
Qed.
Theorem source_full_common_reflected_level_witness M b c n start paramCount reflectCount phi beta Y point target k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->context_bounded M b c n k ->
 source_common_reflected_level_point M start paramCount reflectCount phi beta Y point ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi target ->
 source_full_prv M b c n point ->source_full_prv M b c n target.
Proof.
 intros BF HNames BC HPoint HRecipe PPoint.
 destruct(source_common_reflected_level_witness_instances M start paramCount reflectCount phi beta Y point target BF HPoint HRecipe)
  as(matrix&exY&matrixD&exYD&HY&HT&HYD&HInstD&HInstY).
 assert(HWF:source_sequent_wf M b c n target).
 { exists k. split;[exact(source_common_reflected_level_recipe_bounded M start paramCount reflectCount phi target k BF HNames HRecipe)|exact BC]. }
 pose proof(source_wf_quantifier_instance M b c n SFEx exY target beta exYD(or_intror eq_refl)HT HWF HInstD)as HWFD.
 pose proof(full_source_ExI M b c n matrixD exYD Y point HWFD PPoint HYD HInstY)as PD.
 exact(full_source_ExI M b c n exY target beta exYD HWF PD HT HInstD).
Qed.
Print Assumptions source_common_reflected_level_witness_instances.
Print Assumptions source_full_common_reflected_level_witness.
