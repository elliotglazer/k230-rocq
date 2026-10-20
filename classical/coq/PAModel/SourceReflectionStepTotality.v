(** Actual totality of the reflection ordinal step. Its canonical bound
    variables are input0/output1; under forall/exists they become input1/output0. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds
  SourceReflectionLeast SourceReflectionStep SourceReflectionStepLeastLink SourceWitnessProofComposition SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_ordinal_predicate_code.

Definition source_reflection_step_totality_graph M level sb sc n matrix total:=exists body ex,
  source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix /\
  source_reflection_step M(source_L_domain_code M)level sb sc n(code_numeral M 1)(zeroM M)body /\
  sf_relation M SFEx body(zeroM M)ex /\sf_relation M SFAll ex(zeroM M)total.

Theorem source_zfr_reflection_step_totality M level sb sc n matrix total:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  source_reflection_step_totality_graph M level sb sc n matrix total ->source_zfr_provable M total.
Proof.
  intros HLevel HV(body&ex&HM&HBody&HEx&HAll).
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  destruct(source_zfr_reflection_least_total M level sb sc n(zeroM M)HLevel HV) as(least&(condition&HC&HLeast)&PLeast).
  destruct(source_reflection_step_least_link M(source_L_domain_code M)level sb sc n(zeroM M)condition least
    (numerical_L_domain_bounded M)HL HV HC HLeast) as(body'&HEx'&HBody').
  pose proof(source_reflection_step_functional M(source_L_domain_code M)level sb sc n(code_numeral M 1)(zeroM M)body' body HBody' HBody) as E. subst body'.
  pose proof(sf_relation_functional M SFEx body(zeroM M)least ex HEx' HEx) as E. subst least.
  exact(source_zfr_all_proof M ex total PLeast HAll).
Qed.

Theorem source_zfr_reflection_step_totality_total M level sb sc n:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->exists matrix total,
  source_reflection_step_totality_graph M level sb sc n matrix total /\source_zfr_provable M total.
Proof.
  intros HL HV.
  destruct(source_reflection_step_total M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)) as(matrix&HM).
  destruct(source_reflection_step_total M(source_L_domain_code M)level sb sc n(code_numeral M 1)(zeroM M)) as(body&HBody).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(ex&HEx).
  destruct(sf_relation_total M SFAll ex(zeroM M)) as(total&HAll).
  assert(HG:source_reflection_step_totality_graph M level sb sc n matrix total) by(exists body,ex;auto).
  exists matrix,total. split;[exact HG|exact(source_zfr_reflection_step_totality M level sb sc n matrix total HL HV HG)].
Qed.

Print Assumptions source_zfr_reflection_step_totality.
Print Assumptions source_zfr_reflection_step_totality_total.
