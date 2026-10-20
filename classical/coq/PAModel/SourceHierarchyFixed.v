(** Actual ZFR hierarchy deductions specialized to arbitrary internal names.
    The varying reflection matrix does not occur in these finite laws. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchyOld SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift
  SourceFiniteParameters SourceFiniteNameParameters SourceZFRProvability
  SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_hierarchy_exists_law :=isolated_formula old_hierarchy_exists_law.
Definition source_hierarchy_subset_law :=isolated_formula old_hierarchy_subset_law.
Definition source_hierarchy_exists_expression :=
  source_parameter_expression(source_finite_parameter_names 4) source_hierarchy_exists_law.
Definition source_hierarchy_subset_expression :=
  source_parameter_expression(source_finite_parameter_names 4) source_hierarchy_subset_law.

Theorem source_zfr_hierarchy_exists M rho out :
  code_relation M rho source_hierarchy_exists_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_exists_law 4 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_exists_law
      old_L_background_valid old_hierarchy_exists_proof).
  - exact HO.
Qed.

Theorem source_zfr_hierarchy_subset M rho out :
  code_relation M rho source_hierarchy_subset_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_subset_law 4 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_subset_law
      old_L_background_valid old_hierarchy_subset_proof).
  - exact HO.
Qed.

Print Assumptions source_zfr_hierarchy_exists.
Print Assumptions source_zfr_hierarchy_subset.
