From PAModel Require Import Model CodeExpressions FiniteCoding FiniteCRT
  SourceBounded SourceQuantifierRules SourceRenamingIdentity.
Unset Implicit Arguments.

Theorem source_closed_shift_self M f :
  source_bounded M f (zeroM M) -> source_formula_shift M f f.
Proof.
  intro HF.
  apply (numerical_renaming_identity_on_bound M f (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) (zeroM M) HF).
  intros i HI. exfalso. exact (coding_not_lt_zero M i HI).
Qed.

Print Assumptions source_closed_shift_self.
