(** Actual finite source proofs for environment-domain construction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceEnvFDomainOld
 OldNamedSyntaxBridge OldZFRProofLift SourceLFixed SourceLNonempty SourceZFRProvability
 SourceFiniteParameters SourceFiniteNameParameters SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_env_domain_fixed_law(extension:bool):=isolated_formula
 (if extension then old_env_domain_extension_law else old_env_domain_empty_law).
Theorem source_zfr_env_domain_fixed M extension:source_zfr_provable M(code_numeral M(sf_encode(source_env_domain_fixed_law extension))).
Proof.
 destruct extension.
 - exact(finite_old_zfr_proof_lift M old_L_background old_env_domain_extension_law old_L_background_valid old_env_domain_extension_proof).
 - exact(finite_old_zfr_proof_lift M old_L_background old_env_domain_empty_law old_L_background_valid old_env_domain_empty_proof).
Qed.
Theorem source_zfr_env_domain_fixed_named M extension rho out:
 code_relation M rho(source_parameter_expression(source_finite_parameter_names 5)(source_env_domain_fixed_law extension))out ->
 source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_env_domain_fixed_law extension)5 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_env_domain_fixed M extension))HG).
Qed.
Print Assumptions source_zfr_env_domain_fixed.
Print Assumptions source_zfr_env_domain_fixed_named.
