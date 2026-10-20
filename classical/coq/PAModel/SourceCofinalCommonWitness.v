(** Actual two existential witnesses; K-membership is transported through
    both binder substitutions along with the original common-level matrix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceSequents SourceQuantifierRules NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceInstantiationConstructors
 SourceCommonLevelWitness SourceCofinalCommonPoint SourceCofinalCommonRecipe.
Unset Implicit Arguments.
Theorem source_cofinal_common_recipe_bounded M start count K target k :
 (forall i,coding_lt M i count ->coding_lt M(addM M i start)k) ->coding_lt M K k ->
 source_cofinal_common_recipe M start count K target ->source_bounded M target k.
Proof.
 intros HN HK(point&exY&HP&HY&HT).
 apply(proj2(source_bounded_accept_unary M SFEx exY target k(or_intror eq_refl)HT)).
 apply(proj2(source_bounded_accept_unary M SFEx point exY(succM M k)(or_intror eq_refl)HY)).
 apply(source_cofinal_common_point_bounded M(succM M(succM M start))count(succM M(succM M K))
 (code_numeral M 1)(zeroM M)point(succM M(succM M k))).
 - intros i HI. rewrite !source_common_add_successor.
   apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M k))).
   exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HN i HI)).
 - apply(proj2(coding_lt_succ_cancel M(succM M K)(succM M k))).
   exact(proj2(coding_lt_succ_cancel M K k)HK).
 - change(coding_lt M(succM M(zeroM M))(succM M(succM M k))).
   apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ.
 - apply coding_zero_lt_succ.
 - exact HP.
Qed.
Theorem source_cofinal_common_witness_instances M start count K d y point target :
 source_cofinal_common_point M start count K d y point ->source_cofinal_common_recipe M start count K target ->
 exists matrix exY matrixD exYD,
 sf_relation M SFEx matrix(zeroM M)exY /\sf_relation M SFEx exY(zeroM M)target /\
 sf_relation M SFEx matrixD(zeroM M)exYD /\numerical_instantiation M exY d exYD /\
 numerical_instantiation M matrixD y point.
Proof.
 intros HPoint(matrix&exY&HM&HY&HT).
 destruct(source_cofinal_common_point_total M(succM M start)count(succM M K)(succM M d)(zeroM M))as(matrixD&HMD).
 destruct(sf_relation_total M SFEx matrixD(zeroM M))as(exYD&HYD).
 exists matrix,exY,matrixD,exYD. split;[exact HY|]. split;[exact HT|]. split;[exact HYD|]. split.
 - destruct(substitution_singleton_total M d)as(b&c&HH&HTail).
   destruct(substitution_lift_total M b c(succM M(zeroM M))(zeroM M))as(u&v&l&HLift).
   exists b,c. split;[exact HH|].
   apply(proj2(numerical_substitution_quantifier M false matrix exY b c(succM M(zeroM M))(zeroM M)exYD HY)).
   exists u,v,l,matrixD. split;[exact HLift|]. split;[|exact HYD].
   apply(source_cofinal_common_point_substitution M(succM M(succM M start))count(succM M(succM M K))
    (code_numeral M 1)(zeroM M)matrix(succM M start)(succM M K)(succM M d)(zeroM M)matrixD
    u v l(succM M(zeroM M))HM HMD).
   + apply(proj2(substitution_lift_tail M b c(succM M(zeroM M))(zeroM M)u v l(succM M K)K HLift)). exact(HTail K).
   + apply(proj2(substitution_lift_tail M b c(succM M(zeroM M))(zeroM M)u v l(zeroM M)d HLift)). exact HH.
   + apply(proj2(substitution_lift_head M b c(succM M(zeroM M))(zeroM M)u v l(zeroM M)HLift)). reflexivity.
   + intros i HI. rewrite !source_common_add_successor.
     apply(proj2(substitution_lift_tail M b c(succM M(zeroM M))(zeroM M)u v l
      (succM M(addM M i start))(addM M i start)HLift)). exact(HTail(addM M i start)).
 - destruct(substitution_singleton_total M y)as(b&c&HH&HTail).
   exists b,c. split;[exact HH|].
   apply(source_cofinal_common_point_substitution M(succM M start)count(succM M K)(succM M d)(zeroM M)matrixD
    start K d y point b c(succM M(zeroM M))(zeroM M)HMD HPoint).
   + exact(HTail K).
   + exact(HTail d).
   + exact HH.
   + intros i HI. rewrite source_common_add_successor. exact(HTail(addM M i start)).
Qed.
Theorem source_full_cofinal_common_witness M b c n start count K d y point target k :
 (forall i,coding_lt M i count ->coding_lt M(addM M i start)k) ->coding_lt M K k ->context_bounded M b c n k ->
 source_cofinal_common_point M start count K d y point ->source_cofinal_common_recipe M start count K target ->
 source_full_prv M b c n point ->source_full_prv M b c n target.
Proof.
 intros HN HK HC HPoint HRecipe PPoint.
 destruct(source_cofinal_common_witness_instances M start count K d y point target HPoint HRecipe)
 as(matrix&exY&matrixD&exYD&HY&HT&HYD&HInstD&HInstY).
 assert(HWF:source_sequent_wf M b c n target).
 { exists k. split;[exact(source_cofinal_common_recipe_bounded M start count K target k HN HK HRecipe)|exact HC]. }
 pose proof(source_wf_quantifier_instance M b c n SFEx exY target d exYD(or_intror eq_refl)HT HWF HInstD)as HWFD.
 pose proof(full_source_ExI M b c n matrixD exYD y point HWFD PPoint HYD HInstY)as PD.
 exact(full_source_ExI M b c n exY target d exYD HWF PD HT HInstD).
Qed.
Print Assumptions source_cofinal_common_recipe_bounded.
Print Assumptions source_cofinal_common_witness_instances.
Print Assumptions source_full_cofinal_common_witness.
