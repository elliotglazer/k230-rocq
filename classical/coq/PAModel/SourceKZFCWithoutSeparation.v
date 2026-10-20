(** The actual Separation image is now discharged in the final K/ZFC comparison.
    The remaining two mathematical image families are stated explicitly. *)
From PAModel Require Import Model NumericalLSeparation SourceKZFCFromCanonical
 SourceKZFCForwardSchemas SourceZFCProvability NumericalProofs NativeCanonicalLConsumer.
Unset Implicit Arguments.
Theorem numerical_K_ZFC_consistency_without_separation M :
 L_replacement_image_obligation M ->canonical_kprime_L_images M ->
 (numerical_k_consistent M <->source_zfc_consistent M).
Proof.
 intros HR HK. exact(numerical_K_ZFC_consistency_from_canonical M(actual_L_separation_images M)HR HK).
Qed.
Print Assumptions numerical_K_ZFC_consistency_without_separation.
