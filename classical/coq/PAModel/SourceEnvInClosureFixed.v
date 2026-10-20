(** Actual finite environment-extension-in-C certificate at arbitrary
    PA-model variable names. The finite old ZFR background is discharged. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceEnvInClosureOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_env_in_closure_extension_law:=isolated_formula old_env_in_closure_extension_law.
Definition source_env_in_closure_extension_expression:=source_parameter_expression
 (source_finite_parameter_names 5)source_env_in_closure_extension_law.
Theorem source_zfr_env_in_closure_extension M rho out:
 code_relation M rho source_env_in_closure_extension_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_env_in_closure_extension_law 5 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_env_in_closure_extension_law
    old_L_background_valid old_env_in_closure_extension_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_env_in_closure_extension.
