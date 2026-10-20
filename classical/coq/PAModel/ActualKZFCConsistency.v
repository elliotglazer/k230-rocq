(** Unconditional consistency comparison for the exact numerical K230
    proof predicate and source ZFC proof predicate in every PA model.
    The whole internal schema families, including nonstandard formula and
    proof codes, are discharged by the uniform source constructions. *)
From PAModel Require Import Model NumericalLSeparation NumericalLReplacementFromSeparation
 SourceKZFCForwardSchemas SourceKZFCFromLReplacement SourceZFCProvability.
Unset Implicit Arguments.

Theorem actual_L_replacement_images M : L_replacement_image_obligation M.
Proof.
 exact (L_replacement_images_from_separation M (actual_L_separation_images M)).
Qed.

Theorem numerical_K_ZFC_consistency M :
 numerical_k_consistent M <-> source_zfc_consistent M.
Proof.
 exact (numerical_K_ZFC_consistency_from_L_replacement M (actual_L_replacement_images M)).
Qed.

Theorem k_zfc_comparison_sentence_valid M rho :
 holds M rho k_zfc_comparison_sentence.
Proof.
 exact (k_zfc_comparison_sentence_from_L_replacement M rho (actual_L_replacement_images M)).
Qed.

Print Assumptions actual_L_replacement_images.
Print Assumptions numerical_K_ZFC_consistency.
Print Assumptions k_zfc_comparison_sentence_valid.
