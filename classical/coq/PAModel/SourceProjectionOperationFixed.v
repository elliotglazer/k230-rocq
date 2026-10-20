(** Actual Op4 projection and extension-existence source proofs at
    arbitrary PA-model-valued free names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceProjectionOperationOld SourceLFixed SourceLNonempty
 OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_projection_operation_law:sf_form:=isolated_formula old_projection_operation_law.
Definition source_projection_operation_expression:=source_parameter_expression(source_finite_parameter_names 5)source_projection_operation_law.
Definition source_projection_extension_exists:sf_form:=isolated_formula old_projection_extension_exists.
Definition source_projection_extension_expression:=source_parameter_expression(source_finite_parameter_names 2)source_projection_extension_exists.
Theorem source_zfr_projection_operation M rho out:
 code_relation M rho source_projection_operation_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_projection_operation_law 5 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)). exact(finite_old_zfr_proof_lift M old_L_background old_projection_operation_law
  old_L_background_valid old_projection_operation_proof).
Qed.
Theorem source_zfr_projection_extension M rho out:
 code_relation M rho source_projection_extension_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_projection_extension_exists 2 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)). exact(finite_old_zfr_proof_lift M old_L_background old_projection_extension_exists
  old_L_background_valid old_projection_extension_exists_proof).
Qed.
Print Assumptions source_zfr_projection_operation.
Print Assumptions source_zfr_projection_extension.
