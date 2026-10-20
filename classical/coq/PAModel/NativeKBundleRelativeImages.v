(** The exact remaining K-upper premise is the L (or other domain) image
    of this literal native finite bundle. Its holes, binder maps, bounds
    and universal closures are explicit syntax graphs. No successful-proof
    test occurs in any axiom descriptor. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalTheories SetFormulaCodes SourceBounded
  SourceBoundedCalibration NumericalSetClosure SourceRelativization SourceDescriptorProvability
  SourceDescriptorRelativeTransfer SourceSetTheoryDescriptors SourceZFCProvability SourceZFRProvability
  RawKSourceDescriptor RawKRelativeTransfer SourceZFCPrograms NativeKBundle NativeKBundleNormalization
  SourceRelativeClosedNormalization.
Unset Implicit Arguments.

Definition native_K_relative_images M T domain :=forall a b c u native bound closed,
  c<>a ->c<>b ->native_named_evaluation M (code_parameters a b c u) native_K_bundle_template native ->
  source_bounded M native bound ->all_prefix M bound native closed ->
  exists relative,source_relativization M domain closed relative /\source_descriptor_provable M T relative.

Theorem closed_raw_K_relative_images_from_native M T domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor T domain ->
  native_K_relative_images M T domain ->closed_raw_K_relative_images M T domain.
Proof.
  intros HD HE PE HZ HNative closed_raw
    (a&b&c&u&raw&source&bound&HCA&HCB&HR&HS&HB&HP).
  destruct (native_named_evaluation_total M (code_parameters a b c u) native_K_bundle_template)
    as (native&HN).
  destruct (native_named_evaluation_bounded M (code_parameters a b c u) native_K_bundle_template native HN)
    as (nativebound&HNB).
  destruct (all_prefix_total M nativebound native) as (closed_native&HNP).
  destruct (HNative a b c u native nativebound closed_native HCA HCB HN HNB HNP)
    as (relative_native&HRN&PN).
  pose proof (native_K_bundle_normalization M (code_parameters a b c u) raw source native HR HS HN)
    as [_ HNativeToSource].
  destruct (sf_relation_total M SFImpl native source) as (imp&HImp).
  destruct (source_relativization_total M domain closed_raw) as (relative_raw&HRR).
  exists relative_raw. split;[exact HRR|].
  exact (source_relative_closed_normalization M T domain ex native source bound nativebound
    closed_native closed_raw relative_native relative_raw imp HD HE PE HZ
    (all_prefix_closes M nativebound native closed_native HNB HNP)
    (all_prefix_closes M bound source closed_raw HB HP) HNP HP HImp (HNativeToSource imp HImp)
    HRN PN HRR).
Qed.

Theorem raw_K_relative_refutation_from_native M T domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor T domain ->
  native_K_relative_images M T domain ->
  numerically_provable M (code_numeral M 1) ->source_descriptor_provable M T (zeroM M).
Proof.
  intros HD HE PE HZ HK.
  exact (raw_K_relative_refutation_transfer M T domain ex HD HE PE HZ
    (closed_raw_K_relative_images_from_native M T domain ex HD HE PE HZ HK)).
Qed.

Corollary zfc_consistency_implies_raw_K_via_native_L_images M domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_zfr_provable M ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor ZFRSourceDescriptor domain ->
  native_K_relative_images M ZFRSourceDescriptor domain ->
  source_zfc_consistent M ->numerical_k_consistent M.
Proof.
  intros HD HE PE HZ HK.
  exact (zfc_consistency_implies_raw_K_via_L_images M domain ex HD HE PE HZ
    (closed_raw_K_relative_images_from_native M ZFRSourceDescriptor domain ex HD HE
      (proj2 (source_zfr_descriptor_provable M ex) PE) HZ HK)).
Qed.

Print Assumptions closed_raw_K_relative_images_from_native.
Print Assumptions raw_K_relative_refutation_from_native.
Print Assumptions zfc_consistency_implies_raw_K_via_native_L_images.
