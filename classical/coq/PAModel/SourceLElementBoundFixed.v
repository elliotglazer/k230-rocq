(** The genuine fixed ZFR certificate at arbitrary model-valued set names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceLElementBoundOld SourceLBoundOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition source_L_element_bound_law:=isolated_formula old_L_element_bound_law.
Definition source_L_element_bound_expression:=source_parameter_expression(source_finite_parameter_names 1)source_L_element_bound_law.
Theorem source_zfr_L_element_bound M rho out:
 code_relation M rho source_L_element_bound_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_L_element_bound_law 1 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_bound_background old_L_element_bound_law old_L_bound_background_valid old_L_element_bound_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_L_element_bound.
