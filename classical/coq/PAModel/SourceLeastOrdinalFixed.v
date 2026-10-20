(** Actual ZFR proof certificates for the fixed ordinal/Foundation facts
    used in least_ord. Free variable names may be arbitrary PA-model
    elements. This is not a finite-only surrogate for the varying matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift SourceLeastOrdinalOld
  SourceSetTheoryDescriptors SourceZFRProvability SourceDescriptorProvability
  SourceFiniteParameters SourceFiniteParameterProofs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Inductive source_least_fixed_fact := LeastOrdinalMember | LeastRegularMinimum | LeastSuccessorContainer.
Definition least_old_fixed_formula tag :=
  match tag with
  | LeastOrdinalMember=>old_ordinal_member_law
  | LeastRegularMinimum=>old_regular_minimum_law
  | LeastSuccessorContainer=>old_ordinal_successor_container
  end.
Definition least_fixed_source_formula tag : sf_form := isolated_formula (least_old_fixed_formula tag).
Definition least_fixed_parameter_expression tag :=
  source_parameter_expression source_three_parameter_names (least_fixed_source_formula tag).

Theorem source_zfr_least_fixed_numeral M tag :
  source_zfr_provable M (code_numeral M (sf_encode (least_fixed_source_formula tag))).
Proof.
  apply (finite_old_zfr_proof_lift M old_least_background (least_old_fixed_formula tag)
    old_least_background_zfr).
  destruct tag;cbn [least_old_fixed_formula].
  - apply (OldUndecidability.FOL.Deduction.FullNDFacts.Weak old_ordinal_member_law_proof). intros a HA. destruct HA.
  - exact old_regular_minimum_law_proof.
  - exact old_ordinal_successor_container_proof.
Qed.

Theorem source_zfr_least_fixed_parameters M tag rho out :
  code_relation M rho (least_fixed_parameter_expression tag) out -> source_zfr_provable M out.
Proof.
  intro HG. apply (proj1 (source_zfr_descriptor_provable M out)).
  apply (source_descriptor_three_parameter_proof M ZFRSourceDescriptor
    (least_fixed_source_formula tag) rho out);[|exact HG].
  exact (proj2 (source_zfr_descriptor_provable M
    (code_numeral M (sf_encode (least_fixed_source_formula tag))))
    (source_zfr_least_fixed_numeral M tag)).
Qed.

Print Assumptions source_zfr_least_fixed_numeral.
Print Assumptions source_zfr_least_fixed_parameters.

