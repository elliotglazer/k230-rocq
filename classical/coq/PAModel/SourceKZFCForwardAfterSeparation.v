(** The uniform WF Separation image is supplied here by its actual proof.
    The three remaining schema families are explicit theorem premises. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  CoreConsistencyReduction SourceZFCProvability SourceKZFCForwardSchemas NumericalWFSeparation.
Unset Implicit Arguments.

Theorem actual_wf_separation_image_obligation M : wf_separation_image_obligation M.
Proof. exact (numerical_WF_separation_image M). Qed.

Theorem source_zfc_refutation_to_K_after_WF_separation M :
  wf_replacement_image_obligation M -> L_separation_image_obligation M ->
  L_replacement_image_obligation M -> source_zfc_provable M (zeroM M) ->
  numerically_provable M (code_numeral M 1).
Proof.
  exact (source_zfc_refutation_to_K_from_uniform_schemas M (actual_wf_separation_image_obligation M)).
Qed.

Corollary K_consistency_implies_zfc_after_WF_separation M :
  wf_replacement_image_obligation M -> L_separation_image_obligation M ->
  L_replacement_image_obligation M -> numerical_k_consistent M -> source_zfc_consistent M.
Proof.
  exact (K_consistency_implies_zfc_from_uniform_schemas M (actual_wf_separation_image_obligation M)).
Qed.

Print Assumptions actual_wf_separation_image_obligation.
Print Assumptions source_zfc_refutation_to_K_after_WF_separation.
Print Assumptions K_consistency_implies_zfc_after_WF_separation.
