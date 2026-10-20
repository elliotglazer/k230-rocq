(** The existing shifted-universal specialization calibration also holds
    for native existentials. It enables introduction using the fresh index0
    without assuming the source matrix is standard or binder-free. *)
From PAModel Require Import Model SetFormulaCodes SourceBounded NumericalRenaming
  NumericalInstantiation SourceQuantifierRules SourceShiftSpecialization.
Unset Implicit Arguments.

Theorem source_shifted_ex_specialization M a ex shifted k :
  source_bounded M a k ->sf_relation M SFEx a (zeroM M) ex ->
  source_formula_shift M ex shifted ->exists ar,
    sf_relation M SFEx ar (zeroM M) shifted /\numerical_instantiation M ar (zeroM M) a.
Proof.
  intros HA HEx HS.
  apply (proj1 (numerical_renaming_quantifier M false a ex (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) shifted HEx)) in HS.
  destruct HS as (rb&rc&rn&ar&HL&HR&HOut). exists ar. split;[exact HOut|].
  exact (source_lifted_shift_specialization M a k rb rc rn ar HA HL HR).
Qed.

Print Assumptions source_shifted_ex_specialization.
