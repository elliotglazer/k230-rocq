(** Fixed hierarchy witness facts as actual ZFR proofs at internal names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchyWitnessOld SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift
  SourceFiniteParameters SourceFiniteNameParameters SourceZFRProvability
  SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_hierarchy_unique_law :=isolated_formula old_hierarchy_unique_law.
Definition source_hierarchy_above_law :=isolated_formula old_hierarchy_above_law.
Definition source_hierarchy_unique_expression :=
  source_parameter_expression(source_finite_parameter_names 4) source_hierarchy_unique_law.
Definition source_hierarchy_above_expression :=
  source_parameter_expression(source_finite_parameter_names 4) source_hierarchy_above_law.

Theorem source_zfr_hierarchy_unique M rho out :
  code_relation M rho source_hierarchy_unique_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_unique_law 4 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_unique_law
      old_L_background_valid old_hierarchy_unique_proof).
  - exact HO.
Qed.

Theorem source_zfr_hierarchy_above M rho out :
  code_relation M rho source_hierarchy_above_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_above_law 4 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_above_law
      old_L_background_valid old_hierarchy_above_proof).
  - exact HO.
Qed.

Print Assumptions source_zfr_hierarchy_unique.
Print Assumptions source_zfr_hierarchy_above.
