(** Actual source ordinal maxima at arbitrary PA-model names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceOrdinalMaxOld
  SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_ordinal_max_law :=isolated_formula old_ordinal_max_law.
Definition source_ordinal_max_expression :=source_parameter_expression(source_finite_parameter_names 2)source_ordinal_max_law.

Theorem source_zfr_ordinal_max M rho out :code_relation M rho source_ordinal_max_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_ordinal_max_law 2 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_ordinal_max_law old_L_background_valid old_ordinal_max_proof).
  - exact HO.
Qed.

Print Assumptions source_zfr_ordinal_max.
