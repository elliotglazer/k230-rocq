(** Exact connection of canonical SepBody and the carrier-local witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceD0Recipe SourceFiniteCutoffShift SourceLSeparationMatrixShift SourceLSeparationWitnessShift SourceLSeparationCarrierShell
  SourceLDefinableProfile SourceRelativization SchemaRenamingDescriptors SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_L_SepBody_witness_carrier_shift M domain phi body matrix rp rm old out count :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M count) ->
  schema_renaming M SepBody phi body ->source_cutoff_shift_thrice M phi matrix ->
  source_relativization M domain body rp ->source_relativization M domain matrix rm ->
  code_relation M(L_definable_profile_environment rp domain)(E_L_canonical_separation_witness(CEvar 1)(CEvar 0))old ->
  code_relation M(L_definable_profile_environment rm domain)(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
  source_formula_shift M old out.
Proof.
  intros HD HP HBody(first&second&H1&H2&H3)HRP HRM HOld HOut.
  pose proof(source_SepBody_carrier_cutoff M phi body first second matrix count HP HBody H1 H2 H3) as HMatrix.
  pose proof(source_cutoff_relativization_to M 2 domain body matrix rp rm HD HMatrix HRP HRM) as HRelative.
  exact(source_L_separation_witness_carrier_shift M domain rp rm old out HD HRelative HOld HOut).
Qed.
Print Assumptions source_L_SepBody_witness_carrier_shift.
