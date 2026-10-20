(** The exact remaining interpretation boundary after actual raw-proof
    compilation.  Ordinary source relativization owns all bounded domain
    tables. The still-unproved uniform closed-bundle image family is explicit. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalTheories SetFormulaCodes
  SourceBounded NumericalZFCAxioms SourceRelativization SourceDescriptorProvability
  SourceDescriptorRelativeTransfer SourceSetTheoryDescriptors SourceZFRProvability SourceZFCProvability
  RawKSourceDescriptor.
Unset Implicit Arguments.

Definition closed_raw_K_relative_images M T domain :=forall f,
  closed_raw_K_bundle M f ->exists rf,
    source_relativization M domain f rf /\source_descriptor_provable M T rf.

Theorem RawKSourceDescriptor_relative_images M T domain :
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor T domain ->
  closed_raw_K_relative_images M T domain ->
  source_descriptor_relative_axiom_images M RawKSourceDescriptor T domain.
Proof.
  intros HZ HK f HA HB. apply RawKSourceDescriptor_axiom in HA.
  destruct HA as [HZFC|HBundle].
  - apply (HZ f);[apply ZFCSourceDescriptor_axiom;exact HZFC|exact HB].
  - exact (HK f HBundle).
Qed.

Theorem raw_K_relative_refutation_transfer M T domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_descriptor_provable M T ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor T domain ->
  closed_raw_K_relative_images M T domain ->
  numerically_provable M (code_numeral M 1) ->source_descriptor_provable M T (zeroM M).
Proof.
  intros HD HE PE HZ HK HP.
  exact (source_descriptor_relative_refutation_transfer M RawKSourceDescriptor T domain ex
    HD HE PE (RawKSourceDescriptor_relative_images M T domain HZ HK)
    (raw_K_source_refutation_transfer M HP)).
Qed.

Theorem raw_K_L_refutation_to_zfr M domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_zfr_provable M ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor ZFRSourceDescriptor domain ->
  closed_raw_K_relative_images M ZFRSourceDescriptor domain ->
  numerically_provable M (code_numeral M 1) ->source_zfr_provable M (zeroM M).
Proof.
  intros HD HE PE HZ HK HP. apply source_zfr_descriptor_provable.
  exact (raw_K_relative_refutation_transfer M ZFRSourceDescriptor domain ex HD HE
    (proj2 (source_zfr_descriptor_provable M ex) PE) HZ HK HP).
Qed.

Corollary zfc_consistency_implies_raw_K_via_L_images M domain ex :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->source_zfr_provable M ex ->
  source_descriptor_relative_axiom_images M ZFCSourceDescriptor ZFRSourceDescriptor domain ->
  closed_raw_K_relative_images M ZFRSourceDescriptor domain ->
  source_zfc_consistent M ->numerical_k_consistent M.
Proof.
  intros HD HE PE HZ HK HC HP. apply HC,source_zfr_provable_in_zfc.
  exact (raw_K_L_refutation_to_zfr M domain ex HD HE PE HZ HK HP).
Qed.

Print Assumptions RawKSourceDescriptor_relative_images.
Print Assumptions raw_K_relative_refutation_transfer.
Print Assumptions raw_K_L_refutation_to_zfr.
Print Assumptions zfc_consistency_implies_raw_K_via_L_images.
