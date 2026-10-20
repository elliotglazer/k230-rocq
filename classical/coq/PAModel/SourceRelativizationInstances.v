(** Commutation at the exact shift and outer-binder instantiation interfaces
    used by source_full_rules.  All codes and variable indices are internal. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalRenaming
  NumericalSubstitution NumericalInstantiation SourceQuantifierRules
  SourceRelativization SourceRelativizationRenaming SourceRelativizationSubstitution.
Unset Implicit Arguments.

Theorem source_relativization_shift_exists M domain f r g :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> source_formula_shift M f g ->
  exists s,source_relativization M domain g s /\ source_formula_shift M r s.
Proof.
  intros HD HR HG.
  exact (source_relativization_renaming_exists M f domain (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) g r HD HG HR).
Qed.

Theorem source_relativization_shift M domain f r g s :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> source_formula_shift M f g ->
  source_formula_shift M r s -> source_relativization M domain g s.
Proof.
  intros HD HR HG HS.
  exact (source_relativization_renaming M domain f r (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) g s HD HR HG HS).
Qed.

Theorem source_relativization_instantiation_exists M domain f r t g :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> numerical_instantiation M f t g ->
  exists s,source_relativization M domain g s /\ numerical_instantiation M r t s.
Proof.
  intros HD HR [b [c [HHead HG]]].
  destruct (source_relativization_substitution_exists M f domain b c
    (succM M (zeroM M)) (zeroM M) g r HD HG HR) as [s [HS HSub]].
  exists s. split;[exact HS|]. exists b,c. auto.
Qed.

Theorem source_relativization_instantiation M domain f r t g s :
  source_bounded M domain (code_numeral M 1) ->
  source_relativization M domain f r -> numerical_instantiation M f t g ->
  numerical_instantiation M r t s -> source_relativization M domain g s.
Proof.
  intros HD HR HG HS.
  destruct (source_relativization_instantiation_exists M domain f r t g HD HR HG)
    as [s' [HR' HS']].
  rewrite (numerical_instantiation_functional M r t s s' HS HS'). exact HR'.
Qed.

Print Assumptions source_relativization_shift_exists.
Print Assumptions source_relativization_shift.
Print Assumptions source_relativization_instantiation_exists.
Print Assumptions source_relativization_instantiation.
