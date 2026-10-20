(** Conditional final assembly after the complete native K boundary.
    The canonical image family and the two L schemas are still premises. *)
From PAModel Require Import Model SourceKZFCComparisonRemaining NativeCanonicalLConsumer
  SourceKZFCForwardSchemas SourceZFCProvability NumericalProofs.
Unset Implicit Arguments.

Theorem numerical_K_ZFC_consistency_from_canonical M :
  L_separation_image_obligation M ->L_replacement_image_obligation M ->
  canonical_kprime_L_images M ->(numerical_k_consistent M <->source_zfc_consistent M).
Proof.
  intros HS HR HK. exact(numerical_K_ZFC_consistency_remaining M HS HR
    (native_K_L_images_from_canonical M HK)).
Qed.

Print Assumptions numerical_K_ZFC_consistency_from_canonical.
