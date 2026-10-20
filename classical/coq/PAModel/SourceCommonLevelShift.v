(** Exact source shifts for common-level assertions and their open matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution
  SourceQuantifierRules SourceFiniteCutoffShift SourceCommonLevelPoint SourceCommonLevelRecipe
  SourceCommonLevelWitness.
Unset Implicit Arguments.

Theorem source_common_level_point_shift M start count d y f g :
  source_common_level_point M start count d y f ->
  source_common_level_point M(succM M start)count(succM M d)(succM M y)g ->source_formula_shift M f g.
Proof.
  intros HF HG. apply(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)(code_numeral M 1)g)).
  apply(source_common_level_point_substitution M start count d y f(succM M start)(succM M d)(succM M y)g
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HF HG).
  - apply source_cutoff_shift_base_lookup.
  - apply source_cutoff_shift_base_lookup.
  - intros i HI. rewrite source_common_add_successor. apply source_cutoff_shift_base_lookup.
Qed.

Theorem source_common_level_shift M start count f g :
  source_common_level_recipe M start count f ->source_common_level_recipe M(succM M start)count g ->
  source_formula_shift M f g.
Proof.
  intros HF HG.
  destruct(source_common_level_recipe_shell M start count f HF) as(matrix&exY&HM&HY&HT).
  destruct(source_common_level_recipe_shell M(succM M start)count g HG) as(matrix'&exY'&HM'&HY'&HT').
  destruct(substitution_lift_total M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(b&c&n&HFirst).
  destruct(substitution_lift_total M b c n(code_numeral M 2)) as(d&e&l&HSecond).
  apply(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)(code_numeral M 1)g)).
  apply(proj2(numerical_substitution_quantifier M false exY f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)g HT)).
  exists b,c,n,exY'. split;[exact HFirst|]. split;[|exact HT'].
  apply(proj2(numerical_substitution_quantifier M false matrix exY b c n(code_numeral M 2)exY' HY)).
  exists d,e,l,matrix'. split;[exact HSecond|]. split;[|exact HY'].
  apply(source_common_level_point_substitution M(succM M(succM M start))count(code_numeral M 1)(zeroM M)matrix
    (succM M(succM M(succM M start)))(code_numeral M 1)(zeroM M)matrix' d e l(code_numeral M 3)HM HM').
  - apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l(zeroM M)(zeroM M)HSecond)).
    apply(proj2(substitution_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n(zeroM M)HFirst)). reflexivity.
  - apply(proj2(substitution_lift_head M b c n(code_numeral M 2)d e l(zeroM M)HSecond)). reflexivity.
  - intros i HI. rewrite !source_common_add_successor.
    apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l
      (succM M(addM M i start))(succM M(succM M(addM M i start)))HSecond)).
    apply(proj2(substitution_lift_tail M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n
      (addM M i start)(succM M(addM M i start))HFirst)). apply source_cutoff_shift_base_lookup.
Qed.
Print Assumptions source_common_level_point_shift.
Print Assumptions source_common_level_shift.
