(** Actual L-level constructibility at arbitrary model-valued names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 OldZFRProofLift SourceLFixed SourceLNonempty SourceLLevelOld SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition source_L_level_law:=isolated_formula old_L_level_law.
Definition source_L_level_expression:=source_parameter_expression(source_finite_parameter_names 2)source_L_level_law.
Theorem source_zfr_L_level M rho out:code_relation M rho source_L_level_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_L_level_law 2 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_L_level_law old_L_background_valid old_L_level_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_L_level.
