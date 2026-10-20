(** Exact remaining mathematical obligations after both WF schemas.
    This is a conditional assembly theorem, not the completed comparison. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceKZFCForwardAfterWF SourceKZFCForwardSchemas SourceLFixed SourceLNonempty
  SourceNumeralLift NumericalWFNonempty SourceRelativization SourceSetTheoryDescriptors SourceDescriptorProvability
  SourceDescriptorRelativeTransfer SourceZFCProvability SourceZFRProvability NativeKBundleRelativeImages.
Unset Implicit Arguments.

Theorem actual_L_descriptor_images_from_schemas M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor ZFRSourceDescriptor
    (source_L_domain_code M).
Proof.
  intros LS LR f HA HB.
  destruct (L_axiom_images_from_uniform_schemas M LS LR f
    (proj1 (ZFCSourceDescriptor_axiom M f) HA)) as (rf&HR&PR).
  exists rf. split;[exact HR|].
  exact (proj2 (source_zfr_descriptor_provable M rf) PR).
Qed.

Theorem zfc_consistency_implies_K_remaining M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  native_K_relative_images M ZFRSourceDescriptor (source_L_domain_code M) ->
  source_zfc_consistent M -> numerical_k_consistent M.
Proof.
  intros LS LR HK.
  apply (zfc_consistency_implies_raw_K_via_native_L_images M
    (source_L_domain_code M) (source_L_nonempty_code M)).
  - apply numerical_L_domain_bounded.
  - exact (source_formula_ex_numeral M source_L_domain).
  - apply numerical_L_nonempty_zfr.
  - exact (actual_L_descriptor_images_from_schemas M LS LR).
  - exact HK.
Qed.

Theorem numerical_K_ZFC_consistency_remaining M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  native_K_relative_images M ZFRSourceDescriptor (source_L_domain_code M) ->
  (numerical_k_consistent M <-> source_zfc_consistent M).
Proof.
  intros LS LR HK. split.
  - exact (K_consistency_implies_zfc_after_WF M LS LR).
  - exact (zfc_consistency_implies_K_remaining M LS LR HK).
Qed.

Print Assumptions actual_L_descriptor_images_from_schemas.
Print Assumptions zfc_consistency_implies_K_remaining.
Print Assumptions numerical_K_ZFC_consistency_remaining.
