(** Uniform L Separation and the genuine canonical K-in-L interpretation
    are discharged. Only the exact L Replacement image family remains. *)
From PAModel Require Import Model NumericalLSeparation SourceActualCanonicalNativeL
 SourceKZFCWithoutSeparation SourceKZFCForwardSchemas SourceZFCProvability.
Unset Implicit Arguments.

Theorem numerical_K_ZFC_consistency_from_L_replacement M :
 L_replacement_image_obligation M ->
 (numerical_k_consistent M <-> source_zfc_consistent M).
Proof.
 intro HR.
 exact (numerical_K_ZFC_consistency_without_separation M HR
   (source_actual_canonical_kprime_L_images M (actual_L_separation_images M) HR)).
Qed.

Theorem k_zfc_comparison_sentence_from_L_replacement M rho :
 L_replacement_image_obligation M -> holds M rho k_zfc_comparison_sentence.
Proof.
 intro HR. apply (proj2 (k_zfc_comparison_sentence_correct M rho)).
 exact (numerical_K_ZFC_consistency_from_L_replacement M HR).
Qed.

Print Assumptions numerical_K_ZFC_consistency_from_L_replacement.
Print Assumptions k_zfc_comparison_sentence_from_L_replacement.
