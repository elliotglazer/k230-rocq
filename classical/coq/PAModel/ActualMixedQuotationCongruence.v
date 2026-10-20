(** The actual finite raw certificates discharge all atom-law premises of
    the arbitrary-source mixed quotation induction. *)
From PAModel Require Import Model StableContextSupport MixedQuotationCongruence
  RawQuotientAtomCongruence ActualRawAtomLaws.
Unset Implicit Arguments.

Theorem actual_mixed_quotation_congruence M cb cc cn t marker marker_name :
  raw_empty_marker_graph M t marker_name marker ->
  stable_context_support M cb cc cn marker ->
  forall source,mixed_quotation_property M t cb cc cn source.
Proof.
  intros HE HM. apply (raw_laws_mixed_quotation_congruence M cb cc cn t marker marker_name HE HM).
  exact (actual_raw_quotient_atom_laws M t marker_name marker HE).
Qed.

Print Assumptions actual_mixed_quotation_congruence.
