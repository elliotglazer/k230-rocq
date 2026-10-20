(** Uniform ex_cond: every internally coded x has an ordinal d satisfying
    the exact Cond formula for an internally finite valid piece table.
    All proof contexts and all witness constructions are generated. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceDomainInstances SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax
  SourcePieceConjunctionBounds SourceReflectionExistenceGoal SourceReflectionExistencePositive SourceReflectionExistenceNegative
  SourceClassicalCases SourcePieceBoundTwoWitnesses SourceWitnessProofComposition SourcePropositionalTemplates SourceFunctionalityShells SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_zfr_reflection_existence M level sb sc n x goal:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  source_reflection_existence_goal M(source_L_domain_code M)level sb sc n x goal ->source_zfr_provable M goal.
Proof.
  intros HLevel HV HGoal.
  pose proof(numerical_L_domain_bounded M) as HD.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)x) as(ordinal&HOrdinal).
  destruct(sf_relation_total M SFImpl ordinal(zeroM M)) as(neg&HNeg).
  destruct(sf_relation_total M SFImpl ordinal goal) as(positive&HPositive).
  destruct(sf_relation_total M SFImpl neg goal) as(negative&HNegative).
  pose proof(source_zfr_reflection_existence_positive M level sb sc n x ordinal goal positive(succM M x)
    HLevel HV(coding_lt_succ M x)HOrdinal HGoal HPositive) as PPositive.
  pose proof(source_zfr_reflection_existence_negative M(source_L_domain_code M)level sb sc n x ordinal neg goal negative(succM M x)
    HD HL HV(coding_lt_succ M x)HOrdinal HNeg HGoal HNegative) as PNegative.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)x ordinal(succM M x)
    (source_ordinal_predicate_bounded M)(coding_lt_succ M x)HOrdinal) as BO.
  pose proof(source_reflection_existence_bounded M(source_L_domain_code M)level sb sc n x goal(succM M x)
    HD HL HV(coding_lt_succ M x)HGoal) as BG.
  apply(source_zfr_prop_two M source_cases_positive source_cases_negative(SPTSlot 1)source_classical_cases_program
    (source_pcf_four_environment ordinal goal goal goal)(succM M x)positive negative goal).
  - intros[|[|[|i]]];cbn[source_pcf_four_environment];assumption.
  - unfold source_cases_positive,source_prop_expression. functionality_graph.
  - unfold source_cases_negative,source_prop_expression. functionality_graph.
  - reflexivity.
  - exact PPositive.
  - exact PNegative.
Qed.

Theorem source_zfr_reflection_existence_total M level sb sc n x:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  exists goal,source_reflection_existence_goal M(source_L_domain_code M)level sb sc n x goal /\source_zfr_provable M goal.
Proof.
  intros HL HV. destruct(source_reflection_existence_total M(source_L_domain_code M)level sb sc n x) as(goal&HG).
  exists goal. split;[exact HG|exact(source_zfr_reflection_existence M level sb sc n x goal HL HV HG)].
Qed.

Print Assumptions source_zfr_reflection_existence.
Print Assumptions source_zfr_reflection_existence_total.
