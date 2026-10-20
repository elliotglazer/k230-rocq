(** Actual functionality of the least-Cond reflection ordinal step, in the
    exact three-quantifier Replacement shape with literal RepA/RepB maps. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceReflectionStep SourceReflectionStepRenaming SourceReflectionStepUnique SourcePieceConjunctionBounds
  SchemaRenamingDescriptors SourceFunctionalityShells SourceWitnessProofComposition SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_zfr_reflection_step_functionality M domain level sb sc n matrix a b functionality:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_step M domain level sb sc n(zeroM M)(code_numeral M 1)matrix ->
  schema_renaming M RepA matrix a ->schema_renaming M RepB matrix b ->source_functionality_graph M a b functionality ->
  source_zfr_provable M functionality.
Proof.
  intros HD HL HV HM HA HB HF.
  pose proof(source_reflection_step_repA M domain level sb sc n matrix a HD HL HV HM HA) as HSA.
  pose proof(source_reflection_step_repB M domain level sb sc n matrix b HD HL HV HM HB) as HSB.
  destruct(sf_relation_total M SFEqual(code_numeral M 1)(zeroM M)) as(equal&HEqual).
  destruct(source_functionality_shell M a b equal functionality HEqual HF) as(rhs&point&p1&p2&HRight&HPoint&HAll1&HAll2&HAll3).
  pose proof(source_zfr_reflection_step_unique M domain level sb sc n(code_numeral M 2)(code_numeral M 1)(zeroM M)
    a b equal rhs point(code_numeral M 3)HD HL HV(coding_lt_succ M(code_numeral M 2))
    (proj2(coding_lt_succ_cancel M(zeroM M)(code_numeral M 2))(coding_zero_lt_succ M(code_numeral M 1)))
    (coding_zero_lt_succ M(code_numeral M 2))HSA HSB HEqual HRight HPoint) as PP.
  exact(source_zfr_all_proof M p2 functionality
    (source_zfr_all_proof M p1 p2(source_zfr_all_proof M point p1 PP HAll1)HAll2)HAll3).
Qed.

Print Assumptions source_zfr_reflection_step_functionality.
