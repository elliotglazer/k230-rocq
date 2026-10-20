(** Actual ordinary source shift of a witness request. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift
  SourceEwMonotone SourceEwSubstitution SourceD0Substitution.
Unset Implicit Arguments.

Theorem source_ew_at_shift M domain phi phi' z ew ew' :
  source_bounded M domain (code_numeral M 1) ->source_cutoff_shift M 1 phi phi' ->
  source_ew_at M domain phi z ew ->source_ew_at M domain phi' (succM M z) ew' ->
  source_formula_shift M ew ew'.
Proof.
  intros HD (ab&ac&an&(u&v&m&(EU&EV&EM)&HL)&HP) HE HE'. subst u v m.
  pose proof (source_ew_at_substitution M domain phi phi' z (succM M z) ew ew'
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) ab ac an HD HL HP
    (source_cutoff_shift_base_lookup M z) HE HE') as HS.
  exact (proj2 (numerical_renaming_empty_substitution M ew (zeroM M) (zeroM M)
    (code_numeral M 1) ew') HS).
Qed.

Print Assumptions source_ew_at_shift.
