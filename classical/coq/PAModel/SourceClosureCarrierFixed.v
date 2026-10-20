(** Actual closure-carrier membership proof at arbitrary internal names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge SourceClosureCarrierOld
 SourceLFixed SourceLNonempty OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition source_closure_carrier_law:=isolated_formula old_closure_carrier_law.
Definition source_closure_carrier_expression:=source_parameter_expression(source_finite_parameter_names 3)source_closure_carrier_law.
Theorem source_zfr_closure_carrier M rho out:
 code_relation M rho source_closure_carrier_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_closure_carrier_law 3 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)).
 exact(finite_old_zfr_proof_lift M old_L_background old_closure_carrier_law old_L_background_valid old_closure_carrier_proof).
Qed.
Print Assumptions source_zfr_closure_carrier.
