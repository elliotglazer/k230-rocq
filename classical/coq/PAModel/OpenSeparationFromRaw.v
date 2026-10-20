(** Conditional final open-image adapter. A deterministic high outer name
    avoids the marker's bound names; the resulting whole source quotation
    is then rebased to the caller's requested allocation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalQuotation
  QuotationHygiene QuotationRebase NumericalEquivalence FreshNames SchemaImageReduction
  RawQuotientAtomCongruence RawSeparationContract SeparationAllocation
  QuotedSeparationInterface SeparationOpenAtFresh.
Unset Implicit Arguments.

Theorem open_separation_images_from_raw_domain M marker :
  raw_empty_marker_graph M (code_numeral M 1) (code_numeral M 2) marker ->
  raw_domain_separation_certificates M marker -> open_separation_images M marker.
Proof.
  intros HMarker HRaw phi count body axiom HB HRen HConstruct eb ec en fresh q HSafe HQuote.
  set (high:=separation_witness_name M fresh marker q).
  destruct (separation_witness_bounds M fresh marker q) as [HBase [HMarkerHigh HCodeHigh]].
  assert (HFreshHigh : coding_lt M fresh high).
  { apply (coding_lt_trans M fresh (separation_base M fresh));[|exact HBase].
    apply (coding_lt_trans M fresh (succM M fresh));[apply coding_lt_succ|].
    apply (coding_lt_trans M (succM M fresh) (succM M (succM M fresh)));apply coding_lt_succ. }
  pose proof (separation_safe_above M eb ec en fresh high _ HSafe HFreshHigh) as HHighSafe.
  destruct (numerical_quotation_total M axiom eb ec en high (code_numeral M 1)) as [highq HHighQuote].
  destruct (separation_open_quoted_image_data M phi (succM M count) body axiom eb ec en high highq
    HB HRen HConstruct HHighSafe HHighQuote)
    as [theta [left [right [mb [mc [mn [HM [HTheta [HFa [HFc [HL [HR HG]]]]]]]]]]]].
  assert (HHighProof : numerical_implies M marker highq).
  { exact (quoted_separation_at_fresh M marker HMarker HRaw phi (succM M count)
      eb ec en high mb mc mn theta left right highq HB HHighSafe HM HTheta
      (formula_above_is_fresh M marker high HMarkerHigh) HL HR HG). }
  pose proof (numerical_quotation_rebase_safe M axiom eb ec en fresh high (code_numeral M 1)
    q highq HSafe HHighSafe HQuote HHighQuote) as HRebase.
  exact (numerical_implies_trans M marker highq q HHighProof (proj2 HRebase)).
Qed.

Print Assumptions open_separation_images_from_raw_domain.
