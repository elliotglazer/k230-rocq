(** Literal bounds and ordinary shifts of the ExA Separation chart. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionExASubset SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Theorem source_rec_exa_subset_chart_bounded M phi o a N X out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->
 source_rec_exa_subset_chart M phi o a N X out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BX(point&HP&HO). apply(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)).
 exact(source_rec_exa_subset_point_bounded M phi(succM M o)(succM M a)(succM M N)(succM M X)(zeroM M)point(succM M k)
 BP(proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(proj2(coding_lt_succ_cancel M X k)BX)(coding_zero_lt_succ M k)HP).
Qed.
Theorem source_rec_exa_subset_chart_shift M phi o a N X old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_exa_subset_chart M phi o a N X old ->
 source_rec_exa_subset_chart M phi(succM M o)(succM M a)(succM M N)(succM M X)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_exa_subset_chart_substitution M phi o a N X old(succM M o)(succM M a)(succM M N)(succM M X)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M o)(source_rec_shift_lookup M a)(source_rec_shift_lookup M N)(source_rec_shift_lookup M X)).
Qed.
Print Assumptions source_rec_exa_subset_chart_bounded.
Print Assumptions source_rec_exa_subset_chart_shift.
