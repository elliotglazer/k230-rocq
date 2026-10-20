(** Exact source shifts for common-level assertions and their open matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution
  SourceQuantifierRules SourceFiniteCutoffShift SourceCommonLevelPoint SourceCommonLevelRecipe
  SourceCommonLevelWitness SourceCofinalCommonPoint SourceCofinalCommonRecipe SourceCofinalCommonWitness.
Unset Implicit Arguments.

Theorem source_cofinal_common_shift M start count K f g :
  source_cofinal_common_recipe M start count K f ->source_cofinal_common_recipe M(succM M start)count(succM M K)g ->
  source_formula_shift M f g.
Proof.
  intros (matrix&exY&HM&HY&HT)(matrix'&exY'&HM'&HY'&HT').
  destruct(substitution_lift_total M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(b&c&n&HFirst).
  destruct(substitution_lift_total M b c n(code_numeral M 2)) as(d&e&l&HSecond).
  apply(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)(code_numeral M 1)g)).
  apply(proj2(numerical_substitution_quantifier M false exY f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)g HT)).
  exists b,c,n,exY'. split;[exact HFirst|]. split;[|exact HT'].
  apply(proj2(numerical_substitution_quantifier M false matrix exY b c n(code_numeral M 2)exY' HY)).
  exists d,e,l,matrix'. split;[exact HSecond|]. split;[|exact HY'].
  apply(source_cofinal_common_point_substitution M(succM M(succM M start))count(succM M(succM M K))(code_numeral M 1)(zeroM M)matrix
    (succM M(succM M(succM M start)))(succM M(succM M(succM M K)))(code_numeral M 1)(zeroM M)matrix' d e l(code_numeral M 3)HM HM').
  - apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l(succM M K)(succM M(succM M K))HSecond)).
    apply(proj2(substitution_lift_tail M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n K(succM M K)HFirst)).
    apply source_cutoff_shift_base_lookup.
  - apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l(zeroM M)(zeroM M)HSecond)).
    apply(proj2(substitution_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n(zeroM M)HFirst)). reflexivity.
  - apply(proj2(substitution_lift_head M b c n(code_numeral M 2)d e l(zeroM M)HSecond)). reflexivity.
  - intros i HI. rewrite !source_common_add_successor.
    apply(proj2(substitution_lift_tail M b c n(code_numeral M 2)d e l
      (succM M(addM M i start))(succM M(succM M(addM M i start)))HSecond)).
    apply(proj2(substitution_lift_tail M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c n
      (addM M i start)(succM M(addM M i start))HFirst)). apply source_cutoff_shift_base_lookup.
Qed.
Print Assumptions source_cofinal_common_shift.
