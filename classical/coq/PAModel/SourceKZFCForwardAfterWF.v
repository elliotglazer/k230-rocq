(** Both uniform WF schema images are actual proofs. Only the two uniform
    L schema-image families remain as premises of the forward comparison. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  CoreConsistencyReduction SourceZFCProvability SourceKZFCForwardSchemas
  SourceKZFCForwardAfterSeparation NumericalWFReplacement NumericalZFRAxioms
  SourceRelativization NumericalWFFoundation.
Unset Implicit Arguments.

Theorem actual_wf_replacement_image_obligation M : wf_replacement_image_obligation M.
Proof. exact (numerical_WF_replacement_image M). Qed.

Theorem actual_wf_axiom_images M :
  forall f,numerical_zfr_source_axiom M f -> exists rf,
    source_relativization M (source_wf_domain_code M) f rf /\ source_core_provable M rf.
Proof.
  exact (wf_axiom_images_from_uniform_schemas M
    (actual_wf_separation_image_obligation M) (actual_wf_replacement_image_obligation M)).
Qed.

Theorem source_zfc_refutation_to_K_after_WF M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  source_zfc_provable M (zeroM M) -> numerically_provable M (code_numeral M 1).
Proof.
  exact (source_zfc_refutation_to_K_from_uniform_schemas M
    (actual_wf_separation_image_obligation M) (actual_wf_replacement_image_obligation M)).
Qed.

Corollary K_consistency_implies_zfc_after_WF M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  numerical_k_consistent M -> source_zfc_consistent M.
Proof.
  exact (K_consistency_implies_zfc_from_uniform_schemas M
    (actual_wf_separation_image_obligation M) (actual_wf_replacement_image_obligation M)).
Qed.

Print Assumptions actual_wf_replacement_image_obligation.
Print Assumptions actual_wf_axiom_images.
Print Assumptions source_zfc_refutation_to_K_after_WF.
Print Assumptions K_consistency_implies_zfc_after_WF.
