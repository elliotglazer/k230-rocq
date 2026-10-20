(** The completed lower consistency comparison for the source ZFc core.
    This excludes Foundation and Choice. No source-schema image family or
    raw Collection/Separation certificate is assumed in these theorems. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  CoreConsistencyReduction CoreSchemaComparison ActualSeparationImages
  ActualReplacementImages.
Unset Implicit Arguments.

Theorem actual_core_marker_images M : core_marker_images M.
Proof.
  apply core_marker_images_from_open_schemas.
  intros marker HM. split.
  - exact (actual_open_separation_images M marker HM).
  - exact (actual_open_replacement_images M marker HM).
Qed.

Theorem actual_source_core_refutation_to_K M :
  source_core_provable M (zeroM M) ->
  numerically_provable M (code_numeral M 1).
Proof.
  apply source_core_refutation_to_K.
  exact (actual_core_marker_images M).
Qed.

Theorem actual_K_consistency_implies_source_core_consistency M :
  (~numerically_provable M (code_numeral M 1)) -> source_core_consistent M.
Proof.
  apply K_consistency_implies_source_core_consistency.
  exact (actual_core_marker_images M).
Qed.

Print Assumptions actual_core_marker_images.
Print Assumptions actual_source_core_refutation_to_K.
Print Assumptions actual_K_consistency_implies_source_core_consistency.
