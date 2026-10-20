(** Actual raw shifts of the shared reflected-level point and existence.
    The matrix/count is internally arbitrary and remains fixed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceFiniteCutoffShift SourceCommonLevelWitness SourceCommonReflectedLevel.
Unset Implicit Arguments.
Theorem source_common_reflected_level_point_shift M start paramCount reflectCount phi beta Y old new:
 source_bounded M phi reflectCount ->
 source_common_reflected_level_point M start paramCount reflectCount phi beta Y old ->
 source_common_reflected_level_point M(succM M start)paramCount reflectCount phi(succM M beta)(succM M Y)new ->
 source_formula_shift M old new.
Proof.
 intros BF HO HN. apply(proj2(numerical_renaming_empty_substitution M old(zeroM M)(zeroM M)(code_numeral M 1)new)).
 apply(source_common_reflected_level_point_substitution M start paramCount reflectCount phi beta Y old
  (succM M start)(succM M beta)(succM M Y)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BF HO HN).
 - apply source_cutoff_shift_base_lookup.
 - apply source_cutoff_shift_base_lookup.
 - intros i HI. rewrite source_common_add_successor. apply source_cutoff_shift_base_lookup.
Qed.
Theorem source_common_reflected_level_recipe_shift M start paramCount reflectCount phi old new:
 source_bounded M phi reflectCount ->
 source_common_reflected_level_recipe M start paramCount reflectCount phi old ->
 source_common_reflected_level_recipe M(succM M start)paramCount reflectCount phi new ->source_formula_shift M old new.
Proof.
 intros BF(matrix&exY&HM&HY&HT)(matrix'&exY'&HM'&HY'&HT').
 destruct(substitution_lift_total M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(b&c&n&HFirst).
 destruct(substitution_lift_total M b c n(code_numeral M 2))as(d&e&l&HSecond).
 apply(proj2(numerical_renaming_empty_substitution M old(zeroM M)(zeroM M)(code_numeral M 1)new)).
 apply(proj2(numerical_substitution_quantifier M false exY old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new HT)).
 exists b,c,n,exY'. split;[exact HFirst|]. split;[|exact HT'].
 apply(proj2(numerical_substitution_quantifier M false matrix exY b c n(code_numeral M 2)exY' HY)).
 exists d,e,l,matrix'. split;[exact HSecond|]. split;[|exact HY'].
 apply(source_common_reflected_level_point_substitution M(succM M(succM M start))paramCount reflectCount phi
  (code_numeral M 1)(zeroM M)matrix(succM M(succM M(succM M start)))
  (code_numeral M 1)(zeroM M)matrix' d e l(code_numeral M 3)BF HM HM').
 - apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l(zeroM M)(zeroM M)HSecond)).
   apply(proj2(substitution_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n(zeroM M)HFirst)). reflexivity.
 - apply(proj2(substitution_lift_head M b c n(code_numeral M 2)d e l(zeroM M)HSecond)). reflexivity.
 - intros i HI. rewrite !source_common_add_successor.
   apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l
    (succM M(addM M i start))(succM M(succM M(addM M i start)))HSecond)).
   apply(proj2(substitution_lift_tail M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n
    (addM M i start)(succM M(addM M i start))HFirst)). apply source_cutoff_shift_base_lookup.
Qed.
Print Assumptions source_common_reflected_level_point_shift.
Print Assumptions source_common_reflected_level_recipe_shift.
