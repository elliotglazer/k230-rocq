(** All eight machine logical rows have actual internally finite source
    ZFC proofs.  This module introduces no K-core image premise. *)
From PAModel Require Import Model CodeExpressions ProofTemplates RawSourceImage SourceZFCProvability
  FiniteSourceEquality RawEqualityRows ActualRawEqualityRows SourceZFCBasicClosure
  RawLogicalRow1 RawLogicalRow2 RawLogicalRow4 RawLogicalRow6.
Unset Implicit Arguments.

Theorem source_zfc_raw_logical_row M row env raw out :
  code_relation M env (row_expression row) raw ->raw_source_image M raw out ->
  source_zfc_provable M out.
Proof.
  destruct row;cbn [row_expression];intros HR HO.
  - exact (source_zfc_raw_row1 M env raw out HR HO).
  - exact (source_zfc_raw_row2 M env raw out HR HO).
  - exact (source_zfc_raw_equality_row M FER3 env raw out HR HO).
  - exact (source_zfc_raw_row4 M env raw out HR HO).
  - exact (source_zfc_raw_equality_row M FER5 env raw out HR HO).
  - exact (source_zfc_raw_row6 M env raw out HR HO).
  - exact (source_zfc_raw_equality_row M FER7 env raw out HR HO).
  - exact (source_zfc_raw_row8 M env raw out HR HO).
Qed.

Print Assumptions source_zfc_raw_logical_row.
