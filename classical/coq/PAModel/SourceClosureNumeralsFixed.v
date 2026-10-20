(** Actual ZFR closure/numeral certificates at arbitrary PA-model variable
    names. All original finite set-theoretic assumptions are discharged. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceClosureNumeralsOld
  SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_closure_empty_law :=isolated_formula old_closure_empty_law.
Definition source_closure_successor_law :=isolated_formula old_closure_successor_law.
Definition source_empty_exists_law :=isolated_formula old_empty_exists_law.
Definition source_successor_exists_law :=isolated_formula old_successor_exists_law.
Definition source_closure_empty_expression :=source_parameter_expression (source_finite_parameter_names 3) source_closure_empty_law.
Definition source_closure_successor_expression :=source_parameter_expression (source_finite_parameter_names 3) source_closure_successor_law.
Definition source_successor_exists_expression :=source_parameter_expression (source_finite_parameter_names 1) source_successor_exists_law.

Theorem source_zfr_closure_empty M rho out :code_relation M rho source_closure_empty_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply (proj1 (source_zfr_descriptor_provable M out)).
  apply (source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_closure_empty_law 3 rho out).
  - apply (proj2 (source_zfr_descriptor_provable M _)).
    exact (finite_old_zfr_proof_lift M old_L_background old_closure_empty_law old_L_background_valid old_closure_empty_proof).
  - exact HO.
Qed.

Theorem source_zfr_closure_successor M rho out :code_relation M rho source_closure_successor_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply (proj1 (source_zfr_descriptor_provable M out)).
  apply (source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_closure_successor_law 3 rho out).
  - apply (proj2 (source_zfr_descriptor_provable M _)).
    exact (finite_old_zfr_proof_lift M old_L_background old_closure_successor_law old_L_background_valid old_closure_successor_proof).
  - exact HO.
Qed.

Theorem source_zfr_empty_exists M :source_zfr_provable M (code_numeral M (sf_encode source_empty_exists_law)).
Proof.
  exact (finite_old_zfr_proof_lift M old_L_background old_empty_exists_law old_L_background_valid old_empty_exists_proof).
Qed.

Theorem source_zfr_successor_exists_numeral M :source_zfr_provable M
  (code_numeral M (sf_encode source_successor_exists_law)).
Proof.
  exact (finite_old_zfr_proof_lift M old_L_background old_successor_exists_law old_L_background_valid old_successor_exists_proof).
Qed.

Theorem source_zfr_successor_exists M rho out :code_relation M rho source_successor_exists_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply (proj1 (source_zfr_descriptor_provable M out)).
  apply (source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_successor_exists_law 1 rho out).
  - apply (proj2 (source_zfr_descriptor_provable M _)).
    exact (finite_old_zfr_proof_lift M old_L_background old_successor_exists_law old_L_background_valid old_successor_exists_proof).
  - exact HO.
Qed.

Print Assumptions source_zfr_closure_empty.
Print Assumptions source_zfr_closure_successor.
Print Assumptions source_zfr_empty_exists.
Print Assumptions source_zfr_successor_exists.
Print Assumptions source_zfr_successor_exists_numeral.
