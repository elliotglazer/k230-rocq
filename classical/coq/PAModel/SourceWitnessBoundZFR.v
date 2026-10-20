(** Actual uniform ZFR witness bound for arbitrary internally coded source
    matrices in arbitrary PA models. Every mathematical input is proved. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceRelativizationRules SourceRelativizationBounds SourceD0Recipe SourceLFixed
  SourceOrdinalPredicate SourceDomainInstances SourceWitnessBoundGoal SourceWitnessBoundPositive
  SourceWitnessBoundNegativeZFR SourceWitnessBoundClassical SourceWitnessProofComposition
  SourcePropositionalTemplates SourceFunctionalityShells SetSchemaConstructors SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code source_L_domain source_L_domain_code.

Theorem source_zfr_witness_bound M phi g ordinal goal implication k :
  source_bounded M phi(succM M k) ->coding_lt M g k ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_witness_bound_goal M(source_L_domain_code M)phi goal ->
  sf_relation M SFImpl ordinal goal implication ->source_zfr_provable M implication.
Proof.
  intros HB HG HOrd HGoal HImp.
  pose proof(numerical_L_domain_bounded M) as HD.
  destruct(sr_quantifier_total M false(source_L_domain_code M)phi) as(test&HTest).
  destruct(sf_relation_total M SFImpl test(zeroM M)) as(neg&HNeg).
  destruct(sf_relation_total M SFImpl test implication) as(positive&HPositive).
  destruct(sf_relation_total M SFImpl neg implication) as(negative&HNegative).
  pose proof(source_zfr_witness_bound_positive M phi g ordinal test goal implication positive k
    HB HG HOrd HTest HGoal HImp HPositive) as PPositive.
  pose proof(source_zfr_witness_bound_negative M(source_L_domain_code M)phi g ordinal test neg goal
    implication negative k HD HB HG HOrd HTest HNeg HGoal HImp HNegative) as PNegative.
  pose proof(source_guarded_exists_bounded M(source_L_domain_code M)phi test k
    (sr_domain_bound_succ M(source_L_domain_code M)k HD)HB HTest) as HTestB.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)g ordinal k
    (source_ordinal_predicate_bounded M)HG HOrd) as HOrdinalB.
  pose proof(source_witness_bound_goal_bounded M(source_L_domain_code M)phi goal k HD HB HGoal) as HGoalB.
  set(rho:=schema_env3 test ordinal goal).
  assert(HBounds:forall i,source_bounded M(rho i)k).
  { intros[|[|i]];cbn[rho schema_env3];assumption. }
  assert(HPositiveGraph:code_relation M rho(source_prop_expression witness_bound_cases_positive)positive).
  { unfold witness_bound_cases_positive,source_prop_expression,rho,schema_env3. functionality_graph. }
  assert(HNegativeGraph:code_relation M rho(source_prop_expression witness_bound_cases_negative)negative).
  { unfold witness_bound_cases_negative,source_prop_expression,rho,schema_env3. functionality_graph. }
  assert(HResultGraph:code_relation M rho(source_prop_expression witness_bound_cases_result)implication).
  { unfold witness_bound_cases_result,source_prop_expression,rho,schema_env3. functionality_graph. }
  exact(source_zfr_prop_two M _ _ _ source_witness_bound_cases_program rho k positive negative implication
    HBounds HPositiveGraph HNegativeGraph HResultGraph PPositive PNegative).
Qed.

Theorem source_zfr_witness_bound_total M phi g k :
  source_bounded M phi(succM M k) ->coding_lt M g k ->
  exists ordinal goal implication,
    numerical_instantiation M(source_ordinal_predicate_code M)g ordinal /\
    source_witness_bound_goal M(source_L_domain_code M)phi goal /\
    sf_relation M SFImpl ordinal goal implication /\source_zfr_provable M implication.
Proof.
  intros HB HG.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)g) as(ordinal&HOrd).
  destruct(source_witness_bound_goal_total M(source_L_domain_code M)phi) as(goal&HGoal).
  destruct(sf_relation_total M SFImpl ordinal goal) as(implication&HImp).
  exists ordinal,goal,implication. repeat split;try assumption.
  exact(source_zfr_witness_bound M phi g ordinal goal implication k HB HG HOrd HGoal HImp).
Qed.

Print Assumptions source_zfr_witness_bound.
Print Assumptions source_zfr_witness_bound_total.
