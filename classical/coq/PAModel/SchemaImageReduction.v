(** The remaining open-matrix obligations for the two source schemas.
    This module proves their closure for arbitrary internal parameter
    counts. It does not supply the open Separation or Replacement proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SourceBounded FixedSourceBounds SchemaRenamingDescriptors SetSchemaConstructors
  NumericalSetClosure NumericalZFCAxioms NumericalQuotation QuotationHygiene
  QuotationPrefixImplication NumericalEquivalence.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition open_separation_images M marker := forall phi count body axiom,
  source_bounded M phi (succM M count) -> schema_renaming M SepBody phi body ->
  sf_separation_constructor M body axiom ->
  forall b c len fresh q, quotation_safe M b c len fresh (code_numeral M 1) ->
    numerical_quotation M axiom b c len fresh (code_numeral M 1) q ->
    numerical_implies M marker q.

Definition open_replacement_images M marker := forall phi count a b c axiom,
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi a -> schema_renaming M RepB phi b ->
  schema_renaming M RepC phi c -> sf_replacement_constructor M a b c axiom ->
  forall eb ec len fresh q, quotation_safe M eb ec len fresh (code_numeral M 1) ->
    numerical_quotation M axiom eb ec len fresh (code_numeral M 1) q ->
    numerical_implies M marker q.

Lemma canonical_schema_quotation_safe M :
  quotation_safe M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 4) (code_numeral M 1).
Proof.
  split.
  - apply (proj2 (fixed_source_numeral_lt_iff M 1 4));lia.
  - apply environment_below_empty.
    apply (proj2 (fixed_source_numeral_lt_iff M 0 4));lia.
Qed.

Theorem closed_separation_image_from_open M marker :
  open_separation_images M marker -> forall axiom q,
  numerical_closed_separation M axiom ->
  numerical_quotation M axiom (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.
Proof.
  intros HOpen axiom q [_ [phi [count [HBound [body [open [HRen [HC HP]]]]]]]] HQ.
  apply (numerical_quotation_prefix_implication M open (code_numeral M 1) marker
    (HOpen phi count body open HBound HRen HC)
    count axiom (zeroM M) (zeroM M) (zeroM M) (code_numeral M 4) q HP).
  - apply canonical_schema_quotation_safe.
  - exact HQ.
Qed.

Theorem closed_replacement_image_from_open M marker :
  open_replacement_images M marker -> forall axiom q,
  numerical_closed_replacement M axiom ->
  numerical_quotation M axiom (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.
Proof.
  intros HOpen axiom q [_ [phi [count [HBound [a [b [c [open [HA [HB [HC [HF HP]]]]]]]]]]]] HQ.
  apply (numerical_quotation_prefix_implication M open (code_numeral M 1) marker
    (HOpen phi count a b c open HBound HA HB HC HF)
    count axiom (zeroM M) (zeroM M) (zeroM M) (code_numeral M 4) q HP).
  - apply canonical_schema_quotation_safe.
  - exact HQ.
Qed.

Print Assumptions closed_separation_image_from_open.
Print Assumptions closed_replacement_image_from_open.
