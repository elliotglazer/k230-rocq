(** Actual Separation images in arbitrary PA models. For the lower core
    consistency comparison, only the Replacement image family remains. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalQuotation
  NumericalSetClosure NumericalZFCAxioms NumericalEquivalence BootstrapSpecializations
  CoreConsistencyReduction CoreSchemaComparison RawSchemaCoreComparison
  SchemaImageReduction ActualRawSeparationContract OpenSeparationFromRaw.
Unset Implicit Arguments.

Theorem actual_open_separation_images M marker :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  open_separation_images M marker.
Proof.
  intro HM. apply open_separation_images_from_raw_domain.
  - exact (specialized_marker_raw_graph M marker HM).
  - exact (actual_raw_domain_separation_certificates M marker HM).
Qed.

Theorem actual_closed_separation_image M marker axiom q :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  numerical_closed_separation M axiom ->
  numerical_quotation M axiom (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.
Proof.
  intro HM. apply closed_separation_image_from_open.
  exact (actual_open_separation_images M marker HM).
Qed.

Definition remaining_core_replacement_images M := forall marker,
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  open_replacement_images M marker.

Theorem actual_core_marker_images_from_replacement M :
  remaining_core_replacement_images M -> core_marker_images M.
Proof.
  intro HR. apply core_marker_images_from_open_schemas.
  intros marker HM. split.
  - exact (actual_open_separation_images M marker HM).
  - exact (HR marker HM).
Qed.

Theorem actual_core_consistency_from_replacement M :
  remaining_core_replacement_images M ->
  (~numerically_provable M (code_numeral M 1)) -> source_core_consistent M.
Proof.
  intro HR. apply K_consistency_implies_source_core_consistency.
  exact (actual_core_marker_images_from_replacement M HR).
Qed.

Print Assumptions actual_open_separation_images.
Print Assumptions actual_closed_separation_image.
Print Assumptions actual_core_marker_images_from_replacement.
Print Assumptions actual_core_consistency_from_replacement.
