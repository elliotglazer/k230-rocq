(** Whole internal raw-proof transfer to a closed source theory extending
    ZFC. All logical images and proof operations are actual. The only raw
    nonlogical input is a visible family of K-bundle source proofs. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalTheories ProofTemplates
  SetFormulaCodes NumericalZFCAxioms NumericalSourceFull SourceAxiomContexts SourceDescriptorProvability
  SourceZFCProvability SourceZFCBasicClosure SourceZFCNoSelf SourceDescriptorClosure
  RawSourceImage RawSourceImageInversion RawSourceProofTransfer ActualRawLogicalRows.
Unset Implicit Arguments.

Definition source_descriptor_extends_zfc M T :=forall f,
  numerical_zfc_source_axiom M f ->theory_axiom M T f.

Theorem source_zfc_provable_in_descriptor M T f :
  source_descriptor_extends_zfc M T ->source_zfc_provable M f ->source_descriptor_provable M T f.
Proof.
  intros HE (b&c&n&HC&HP). exists b,c,n. split;[|exact HP].
  split;[exact (source_zfc_context_closed M b c n HC)|]. intros g HG. exact (HE g (HC g HG)).
Qed.

Definition source_descriptor_raw_bundle_images M T :=forall a b c u raw out,
  c<>a ->c<>b ->code_relation M (code_parameters a b c u) code_bundle raw ->
  raw_source_image M raw out ->source_descriptor_provable M T out.

Theorem source_descriptor_raw_axiom_images M T :
  source_descriptor_extends_zfc M T ->source_descriptor_raw_bundle_images M T ->
  raw_axiom_images M (source_descriptor_provable M T).
Proof.
  intros HE HK raw out [ER|[a [b [c [u HRows]]]]] HO.
  - subst raw. apply (source_zfc_provable_in_descriptor M T out HE).
    exact (source_zfc_provable_truth M out (raw_source_zero_inv M out HO)).
  - destruct HRows as [H1|[H2|[H3|[H4|[H5|[H6|[H7|[H8|[HCA [HCB HB]]]]]]]]]].
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR1 (code_parameters a b c u) raw out H1 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR2 (code_parameters a b c u) raw out H2 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR3 (code_parameters a b c u) raw out H3 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR4 (code_parameters a b c u) raw out H4 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR5 (code_parameters a b c u) raw out H5 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR6 (code_parameters a b c u) raw out H6 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR7 (code_parameters a b c u) raw out H7 HO)).
    + exact (source_zfc_provable_in_descriptor M T out HE
        (source_zfc_raw_logical_row M LR8 (code_parameters a b c u) raw out H8 HO)).
    + exact (HK a b c u raw out HCA HCB HB HO).
Qed.

Theorem source_descriptor_raw_named_generalization M T :
  raw_named_generalization_closure M (source_descriptor_provable M T).
Proof.
  intros s x b c v out HP HM HR HA.
  exact (source_descriptor_provable_all M T v out
    (source_descriptor_provable_renaming M T s b c _ _ v HP HR) HA).
Qed.

Theorem raw_source_descriptor_proof_transfer M T :
  source_descriptor_extends_zfc M T ->source_descriptor_raw_bundle_images M T ->
  forall raw out,numerically_provable M raw ->raw_source_image M raw out ->
    source_descriptor_provable M T out.
Proof.
  intros HE HK raw out HP HO.
  refine (raw_source_proof_transfer M (source_descriptor_provable M T) _ _ _ _ _ raw HP out HO).
  - exact (source_descriptor_provable_definable M T).
  - intros s HS. exact (source_zfc_provable_in_descriptor M T s HE (source_zfc_provable_truth M s HS)).
  - intros a b h PA PH HH. exact (source_descriptor_provable_mp M T a b h PA PH HH).
  - exact (source_descriptor_raw_named_generalization M T).
  - exact (source_descriptor_raw_axiom_images M T HE HK).
Qed.

Theorem raw_source_descriptor_refutation_transfer M T :
  source_descriptor_extends_zfc M T ->source_descriptor_raw_bundle_images M T ->
  numerically_provable M (code_numeral M 1) ->source_descriptor_provable M T (zeroM M).
Proof.
  intros HE HK HP. destruct (raw_source_image_total M (code_numeral M 1)) as (out&HO).
  pose proof (raw_source_descriptor_proof_transfer M T HE HK (code_numeral M 1) out HP HO) as PO.
  destruct (sf_relation_total M SFImpl out (zeroM M)) as (neg&HN).
  apply (source_descriptor_provable_mp M T out (zeroM M) neg PO);[|exact HN].
  apply (source_zfc_provable_in_descriptor M T neg HE).
  exact (source_zfc_no_self M (zeroM M) out neg (raw_one_source_member M out HO) HN).
Qed.

Print Assumptions source_descriptor_raw_axiom_images.
Print Assumptions source_descriptor_raw_named_generalization.
Print Assumptions raw_source_descriptor_proof_transfer.
Print Assumptions raw_source_descriptor_refutation_transfer.
