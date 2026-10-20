(** Actual Replacement images in arbitrary PA models. The raw Collection
    theorem is supplied by its checked construction, not by a hypothesis. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalQuotation NumericalSetClosure NumericalZFCAxioms NumericalEquivalence
  BootstrapSpecializations SourceBounded SchemaRenamingDescriptors SetSchemaConstructors
  QuotationHygiene RawQuotientAtomCongruence ActualRawCollection
  RawSchemaCoreComparison SchemaImageReduction RawCollectionReplacement.
Unset Implicit Arguments.

Theorem actual_replacement_quotation M t marker marker_name phi count ra rb rc axiom
    eb ec en base q :
  raw_empty_marker_graph M t marker_name marker ->
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  schema_renaming M RepC phi rc -> sf_replacement_constructor M ra rb rc axiom ->
  quotation_safe M eb ec en base t ->
  numerical_quotation M axiom eb ec en base t q -> numerical_implies M marker q.
Proof.
  intro HM. apply (raw_collection_replacement_quotation M t marker marker_name
    phi count ra rb rc axiom eb ec en base q).
  - exact (actual_raw_collection_template_certificates M t marker_name marker HM).
  - exact HM.
Qed.

Theorem actual_open_replacement_images M marker :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  open_replacement_images M marker.
Proof.
  intro HM.
  pose proof (specialized_marker_raw_graph M marker HM) as HRaw.
  apply (raw_collection_open_replacement_images M marker (code_numeral M 2)).
  - exact (actual_raw_collection_template_certificates M (code_numeral M 1)
      (code_numeral M 2) marker HRaw).
  - exact HRaw.
Qed.

Theorem actual_closed_replacement_image M marker axiom q :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  numerical_closed_replacement M axiom ->
  numerical_quotation M axiom (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.
Proof.
  intro HM. apply closed_replacement_image_from_open.
  exact (actual_open_replacement_images M marker HM).
Qed.

Print Assumptions actual_replacement_quotation.
Print Assumptions actual_open_replacement_images.
Print Assumptions actual_closed_replacement_image.
