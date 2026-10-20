(** The source Replacement schema follows from the exact raw Collection
    certificate family. All parameters and source matrices are internal
    to the PA model. This is a numerical proof construction, not completeness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalQuotation
  NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts
  ContextualProofs ContextualDeduction StableContextSupport
  QuotationPayloads QuotationHygiene QuotationSchemaSkeleton SetFormulaCodes SetSchemaConstructors
  SchemaRenamingDescriptors SourceBounded SchemaImageReduction RawQuotientAtomCongruence
  RawCollectionProfile ReplacementPointwiseSkeleton QuotedReplacementRange.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem raw_collection_replacement_quotation M t marker marker_name phi count ra rb rc axiom
    eb ec en base q :
  raw_collection_template_certificates M t marker -> raw_empty_marker_graph M t marker_name marker ->
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb -> schema_renaming M RepC phi rc ->
  sf_replacement_constructor M ra rb rc axiom -> quotation_safe M eb ec en base t ->
  numerical_quotation M axiom eb ec en base t q -> numerical_implies M marker q.
Proof.
  intros HRaw HM HB RA RB RC HAx HBase HQ result GResult.
  pose proof (proj2 (replacement_quotation_skeleton M ra rb rc axiom eb ec en base t q HAx) HQ) as HS.
  change (exists functionQ rangeQ,
    skeleton_quotation M functionality_skeleton (schema_env3 ra rb rc) eb ec en base t functionQ /\
    skeleton_quotation M replacement_range_skeleton (schema_env3 ra rb rc) eb ec en base t rangeQ /\
    quotation_binary M SFImpl functionQ rangeQ q) in HS.
  destruct HS as (functionQ & rangeQ & HFunction & HRange & GRoot).
  destruct (code_relation_total M (E_sf_functionality (CEvar 0) (CEvar 1))
    (ra .: rb .: fun _=>zeroM M)) as [functionSource GF].
  assert (HFQ:numerical_quotation M functionSource eb ec en base t functionQ).
  { apply (proj1 (skeleton_quotation_correct M functionality_skeleton (schema_env3 ra rb rc)
      functionSource GF eb ec en base t functionQ));exact HFunction. }
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) marker) as [mb [mc [mn CM]]].
  assert (PM:stable_context_support M mb mc mn marker).
  { apply stable_context_support_member;apply (proj2 (context_member_cons M (zeroM M) (zeroM M) (zeroM M)
      marker mb mc mn marker CM));now left. }
  destruct (environment_cons_total M mb mc mn functionQ) as [fb [fc [fn CF]]].
  assert (PF:stable_context_support M fb fc fn functionQ).
  { apply stable_context_support_member;apply (proj2 (context_member_cons M mb mc mn functionQ fb fc fn functionQ CF));now left. }
  assert (PRange:contextually_provable M fb fc fn rangeQ).
  { exact (quoted_replacement_range_from_raw_collection M phi count ra rb rc functionSource functionQ
      eb ec en base t marker marker_name fb fc fn base rangeQ
      HRaw HB RA RB RC GF HFQ HBase PF HM (stable_context_support_cons M mb mc mn functionQ fb fc fn marker CF PM)
      HBase HRange). }
  destruct (contextual_deduction M mb mc mn functionQ fb fc fn rangeQ CF PRange) as [imp [GImp PImp]].
  assert (EImp:imp=q) by exact (code_relation_functional M (E_wim (CEvar 0) (CEvar 1))
    (functionQ .: rangeQ .: fun _=>zeroM M) imp q GImp GRoot).
  subst imp.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M) marker mb mc mn q CM PImp)
    as [final [GFinal PFinal]].
  assert (EFinal:final=result) by exact (code_relation_functional M (E_wim (CEvar 0) (CEvar 1))
    (marker .: q .: fun _=>zeroM M) final result GFinal GResult).
  subst final.
  exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) result) PFinal).
Qed.

Theorem raw_collection_open_replacement_images M marker marker_name :
  raw_collection_template_certificates M (code_numeral M 1) marker ->
  raw_empty_marker_graph M (code_numeral M 1) marker_name marker -> open_replacement_images M marker.
Proof.
  intros HRaw HM phi count ra rb rc axiom HB RA RB RC HAx eb ec en base q HBase HQ.
  exact (raw_collection_replacement_quotation M (code_numeral M 1) marker marker_name
    phi count ra rb rc axiom eb ec en base q HRaw HM HB RA RB RC HAx HBase HQ).
Qed.

Print Assumptions raw_collection_replacement_quotation.
Print Assumptions raw_collection_open_replacement_images.
