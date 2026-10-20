(** The finite subset-closed shell commutes with ordinary source shift.
    Only parameter slot zero occurs; the two environments' other slots
    may differ arbitrarily. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded ZFCFiniteAxiomTemplates SourceBoundedCalibration SourceNumeralLift SourceFiniteParameters
  SourceFiniteParameterProofs SourceUnaryParameters NumericalRenaming NumericalInstantiation
  SourceDomainInstances SourceQuantifierRules SourceSubsetClosedPoint.
From Undecidability.FOL Require Import Syntax.Bounded Sets.minZF.
Unset Implicit Arguments.

Lemma source_point_subset_closed_bound :bounded 1 (source_point_subset_closed $0).
Proof. apply set_formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem source_point_subset_closed_shift M rho sigma f g :
  sigma 0=succM M (rho 0) ->
  code_relation M rho (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) f ->
  code_relation M sigma (source_parameter_expression source_three_parameter_names
    (source_point_subset_closed $0)) g ->source_formula_shift M f g.
Proof.
  intros HNames HF HG.
  pose proof (source_unary_parameter_instantiation M (source_point_subset_closed $0)
    source_three_parameter_names rho (rho 0) f source_point_subset_closed_bound eq_refl HF) as HIF.
  pose proof (source_unary_parameter_instantiation M (source_point_subset_closed $0)
    source_three_parameter_names sigma (sigma 0) g source_point_subset_closed_bound eq_refl HG) as HIG.
  pose proof (proj2 (source_formula_numeral_bounded M (source_point_subset_closed $0) 1)
    source_point_subset_closed_bound) as HB.
  destruct (numerical_renaming_total M f (zeroM M)(zeroM M)(zeroM M)
    (succM M (zeroM M))) as (shifted&HS).
  pose proof (source_domain_instance_shift M _ (rho 0) f shifted HB HIF HS) as HIShift.
  rewrite <-HNames in HIShift.
  rewrite (numerical_instantiation_functional M _ (sigma 0) shifted g HIShift HIG) in HS.
  exact HS.
Qed.

Print Assumptions source_point_subset_closed_shift.
