(** Exact shift of a filtered membership profile under a new witness.
    Predicate codes and set-variable indices may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors NumericalRenamingMaps NumericalRenaming SourceQuantifierRules
  SourceFiniteCutoffShift SourceLiftedPredicateShift SourcePropositionalTemplates
  SourceSeparationSubset SourcePropositionalRenaming.
Unset Implicit Arguments.

Lemma source_shift_map_lookup M i :renaming_lookup M (zeroM M) (zeroM M) (zeroM M)
  (code_numeral M 1) i (succM M i).
Proof.
  apply (proj2 (renaming_lookup_outside M (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1) i (succM M i) (coding_not_lt_zero M i))).
  exact (Arithmetic.succ_as_add M i).
Qed.

Theorem source_filtered_profile_shift M s a phi inserted
    smem amem point all shifted_smem shifted_amem shifted_point shifted_all :
  source_cutoff_shift M 1 phi inserted ->
  sf_relation M SFMember (zeroM M) (succM M s) smem ->
  sf_relation M SFMember (zeroM M) (succM M a) amem ->
  code_relation M (schema_env3 smem amem phi) (source_prop_expression separation_point_template) point ->
  sf_relation M SFAll point (zeroM M) all ->
  sf_relation M SFMember (zeroM M) (succM M (succM M s)) shifted_smem ->
  sf_relation M SFMember (zeroM M) (succM M (succM M a)) shifted_amem ->
  code_relation M (schema_env3 shifted_smem shifted_amem inserted)
    (source_prop_expression separation_point_template) shifted_point ->
  sf_relation M SFAll shifted_point (zeroM M) shifted_all ->
  source_formula_shift M all shifted_all.
Proof.
  intros HInsert HS HA HP HAll HSS HSA HShiftedPoint HShiftedAll.
  destruct (renaming_lift_total M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (rb&rc&rn&HL).
  assert (RSmem:numerical_renaming M smem rb rc rn (code_numeral M 1) shifted_smem).
  { apply (proj2 (numerical_renaming_member M (zeroM M) (succM M s) smem
      rb rc rn (code_numeral M 1) shifted_smem HS)).
    exists (zeroM M),(succM M (succM M s)). split;[exact (proj1 (proj2 HL))|].
    split;[|exact HSS]. exact (proj2 (proj2 HL) s (succM M s) (source_shift_map_lookup M s)). }
  assert (RAmem:numerical_renaming M amem rb rc rn (code_numeral M 1) shifted_amem).
  { apply (proj2 (numerical_renaming_member M (zeroM M) (succM M a) amem
      rb rc rn (code_numeral M 1) shifted_amem HA)).
    exists (zeroM M),(succM M (succM M a)). split;[exact (proj1 (proj2 HL))|].
    split;[|exact HSA]. exact (proj2 (proj2 HL) a (succM M a) (source_shift_map_lookup M a)). }
  pose proof (source_cutoff_is_lifted_shift M phi inserted rb rc rn HInsert HL) as RPhi.
  assert (RPoint:numerical_renaming M point rb rc rn (code_numeral M 1) shifted_point).
  { apply (source_prop_expression_renaming M (schema_env3 smem amem phi)
      (schema_env3 shifted_smem shifted_amem inserted) rb rc rn (code_numeral M 1)
      separation_point_template point shifted_point);[|exact HP|exact HShiftedPoint].
    intros [|[|i]];cbn [schema_env3];assumption. }
  apply (proj2 (numerical_renaming_quantifier M true point all (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) shifted_all HAll)).
  exists rb,rc,rn,shifted_point. split;[exact HL|]. split;assumption.
Qed.

Print Assumptions source_shift_map_lookup.
Print Assumptions source_filtered_profile_shift.

