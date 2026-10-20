(** Actual ZFR hierarchy element/subset law with arbitrary internal names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceHierarchyTransitiveOld
  SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_hierarchy_element_subset_law :=isolated_formula old_hierarchy_element_subset_law.
Definition source_hierarchy_element_subset_expression :=source_parameter_expression(source_finite_parameter_names 3)source_hierarchy_element_subset_law.

Theorem source_zfr_hierarchy_element_subset M rho out :
  code_relation M rho source_hierarchy_element_subset_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_element_subset_law 3 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_element_subset_law
      old_L_background_valid old_hierarchy_element_subset_proof).
  - exact HO.
Qed.

Print Assumptions source_zfr_hierarchy_element_subset.
