(** Actual finite zero-clause extension proof at nine arbitrary names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge SourceRecursionZeroExtensionOld
 SourceLFixed SourceLNonempty OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition source_rec_zero_extension_law:=isolated_formula old_recursion_zero_extension_law.
Definition source_rec_zero_extension_expression:=source_parameter_expression(source_finite_parameter_names 9)source_rec_zero_extension_law.
Theorem source_zfr_rec_zero_extension_named M rho out:
 code_relation M rho source_rec_zero_extension_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_rec_zero_extension_law 9 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)).
 exact(finite_old_zfr_proof_lift M old_L_background old_recursion_zero_extension_law
  old_L_background_valid old_recursion_zero_extension_proof).
Qed.
Print Assumptions source_zfr_rec_zero_extension_named.
