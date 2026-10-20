(** Actual least-Cond totality/functionality in the generic recursion interfaces. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds SourcePieceClosure
 SourceRecursionBinaryInstance SourceRecursionTotalRelation SourceRecursionFunctionality
 SourceReflectionStep SourceReflectionStepTotality SourceReflectionStepFunctionality SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_reflection_rec_binary M domain level sb sc n matrix u v out:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 source_reflection_step M domain level sb sc n(zeroM M)(code_numeral M 1)matrix ->
 source_rec_binary M matrix u v out ->source_reflection_step M domain level sb sc n u v out.
Proof.
 intros HD HL HV HM(rb&rc&HMap&HS).
 exact(source_reflection_step_substitution M domain level sb sc n(zeroM M)(code_numeral M 1)matrix rb rc(code_numeral M 2)(code_numeral M 2)u v out HD HL HV HM HS
  (source_pc_reopening_lookup M v u rb rc(code_numeral M 2)0 HMap ltac:(lia))
  (source_pc_reopening_lookup M v u rb rc(code_numeral M 2)1 HMap ltac:(lia))).
Qed.
Theorem source_zfr_reflection_rec_total M level sb sc n matrix total:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
 source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix ->
 source_rec_total_relation M matrix total ->source_zfr_provable M total.
Proof.
 intros HLevel HV HM(bodyEx&(body&HBody&HEx)&HAll).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_rec_binary M(source_L_domain_code M)level sb sc n matrix(code_numeral M 1)(zeroM M)body(numerical_L_domain_bounded M)HL HV HM HBody)as HStepBody.
 apply(source_zfr_reflection_step_totality M level sb sc n matrix total HLevel HV).
 exists body,bodyEx. auto.
Qed.
Theorem source_zfr_reflection_rec_functional M level sb sc n matrix funlaw:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
 source_reflection_step M(source_L_domain_code M)level sb sc n(zeroM M)(code_numeral M 1)matrix ->
 source_rec_functionality M matrix funlaw ->source_zfr_provable M funlaw.
Proof.
 intros HLevel HV HM(a&b&HA&HB&HF).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 exact(source_zfr_reflection_step_functionality M(source_L_domain_code M)level sb sc n matrix a b funlaw(numerical_L_domain_bounded M)HL HV HM HA HB HF).
Qed.
Print Assumptions source_reflection_rec_binary.
Print Assumptions source_zfr_reflection_rec_total.
Print Assumptions source_zfr_reflection_rec_functional.
