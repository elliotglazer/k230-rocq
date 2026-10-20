(** The lower core comparison after all fixed axiom images have been
    constructed. Only the two explicit open-schema proof families remain
    assumptions here. This is not the full StandardZFC comparison. *)
From PAModel Require Import Model CodeExpressions NumericalProofs
  NumericalCoreAxioms NumericalQuotation NumericalEquivalence
  BootstrapSpecializations CoreFixedImages CoreConsistencyReduction
  SchemaImageReduction.
Unset Implicit Arguments.

Definition open_core_schema_images M := forall marker,
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  open_separation_images M marker /\ open_replacement_images M marker.

Theorem core_marker_images_from_open_schemas M :
  open_core_schema_images M -> core_marker_images M.
Proof.
  intros H marker HM f q HF HQ.
  destruct HF as [[tag [HT HTag]]|[HSep|HRep]].
  - exact (actual_all_fixed_core_marker_images M tag marker f q HT HM HTag HQ).
  - exact (closed_separation_image_from_open M marker (proj1 (H marker HM)) f q HSep HQ).
  - exact (closed_replacement_image_from_open M marker (proj2 (H marker HM)) f q HRep HQ).
Qed.

Theorem source_core_refutation_from_open_schemas M :
  open_core_schema_images M -> source_core_provable M (zeroM M) ->
  numerically_provable M (code_numeral M 1).
Proof.
  intro H. apply source_core_refutation_to_K.
  exact (core_marker_images_from_open_schemas M H).
Qed.

Theorem K_consistency_implies_core_consistency_from_open_schemas M :
  open_core_schema_images M ->
  (~numerically_provable M (code_numeral M 1)) -> source_core_consistent M.
Proof.
  intro H. apply K_consistency_implies_source_core_consistency.
  exact (core_marker_images_from_open_schemas M H).
Qed.

Print Assumptions core_marker_images_from_open_schemas.
Print Assumptions source_core_refutation_from_open_schemas.
Print Assumptions K_consistency_implies_core_consistency_from_open_schemas.
