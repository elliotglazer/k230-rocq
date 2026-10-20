(** Actual source renamings preserve both named roles of the least-Cond
    ordinal-step relation. The canonical relation has input0/output1. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming RenamingSubstitution SourcePieceConjunctionBounds SourceReflectionStep SchemaRenamingDescriptors.
Unset Implicit Arguments.

Theorem source_reflection_step_renaming M domain level sb sc n x y f rb rc rn delta u v out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_step M domain level sb sc n x y f ->numerical_renaming M f rb rc rn delta out ->
  renaming_lookup M rb rc rn delta x u ->renaming_lookup M rb rc rn delta y v ->
  source_reflection_step M domain level sb sc n u v out.
Proof.
  intros HD HL HV HF HR HX HY.
  exact(source_reflection_step_substitution M domain level sb sc n x y f rb rc rn(addM M rn delta)u v out HD HL HV HF
    (proj1(numerical_renaming_substitution_uniform M f rb rc rn delta out)HR)
    (proj1(renaming_substitution_lookup M rb rc rn delta x u)HX)(proj1(renaming_substitution_lookup M rb rc rn delta y v)HY)).
Qed.

Theorem source_reflection_step_repA M domain level sb sc n matrix a:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_step M domain level sb sc n(zeroM M)(code_numeral M 1)matrix ->schema_renaming M RepA matrix a ->
  source_reflection_step M domain level sb sc n(code_numeral M 2)(code_numeral M 1)a.
Proof.
  intros HD HL HV HM HR.
  apply(source_reflection_step_renaming M domain level sb sc n(zeroM M)(code_numeral M 1)matrix
    (code_numeral M 22)(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)(code_numeral M 2)(code_numeral M 1)a HD HL HV HM HR).
  - apply(proj2(schema_lookup_first M RepA _));reflexivity.
  - apply(proj2(schema_lookup_second M RepA _));reflexivity.
Qed.

Theorem source_reflection_step_repB M domain level sb sc n matrix b:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
  source_reflection_step M domain level sb sc n(zeroM M)(code_numeral M 1)matrix ->schema_renaming M RepB matrix b ->
  source_reflection_step M domain level sb sc n(code_numeral M 2)(zeroM M)b.
Proof.
  intros HD HL HV HM HR.
  apply(source_reflection_step_renaming M domain level sb sc n(zeroM M)(code_numeral M 1)matrix
    (code_numeral M 14)(code_numeral M 3)(code_numeral M 2)(code_numeral M 1)(code_numeral M 2)(zeroM M)b HD HL HV HM HR).
  - apply(proj2(schema_lookup_first M RepB _));reflexivity.
  - apply(proj2(schema_lookup_second M RepB _));reflexivity.
Qed.

Print Assumptions source_reflection_step_renaming.
Print Assumptions source_reflection_step_repA.
Print Assumptions source_reflection_step_repB.
