From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalRenaming NumericalContextRenaming SourceQuantifierRules.
Unset Implicit Arguments.
Theorem source_rec_equal_shift M x y old new:
 sf_relation M SFEqual x y old ->sf_relation M SFEqual(succM M x)(succM M y)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_equal M x y old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new HO)).
 exists(succM M x),(succM M y). repeat split;try assumption;apply context_shift_lookup;reflexivity.
Qed.
Print Assumptions source_rec_equal_shift.
