(** Uniform equality/membership logical-row images. There is no assumed
    axiom-image family or standardness restriction on raw names/codes. *)
From PAModel Require Import Model CodeExpressions NumericalRenaming SetFormulaCodes
  SourceZFCProvability SourceZFCRenaming FiniteSourceEquality SourceZFCFiniteEquality
  RawSourceImage RawEqualityRows ThreeNameRenaming.
Unset Implicit Arguments.

Theorem source_zfc_raw_equality_row M row env raw out :
  code_relation M env (raw_equality_row_expression row) raw -> raw_source_image M raw out ->
  source_zfc_provable M out.
Proof.
  intros HR HO.
  destruct (three_name_renaming_total M (env 0) (env 1) (env 2) (zeroM M))
    as (p&q&H0&H1&H2).
  exact (source_zfc_provable_renaming M
    (code_numeral M (sf_encode (finite_equality_matrix row))) p q (code_numeral M 3) (zeroM M) out
    (source_zfc_finite_equality_matrix M row)
    (raw_equality_row_renaming M row env raw out p q (code_numeral M 3) (zeroM M) HR HO H0 H1 H2)).
Qed.

Print Assumptions source_zfc_raw_equality_row.
