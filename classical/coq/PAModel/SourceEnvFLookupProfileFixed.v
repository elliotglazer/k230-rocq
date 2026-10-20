(** Actual head/tail lookup-profile proofs at arbitrary internal names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 SourceEnvFLookupProfileOld SourceLFixed SourceLNonempty OldZFRProofLift SourceZFRProvability
 SourceFiniteParameters SourceFiniteNameParameters SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_env_lookup_profile_law head:=isolated_formula(old_env_lookup_profile_law head).
Definition source_env_lookup_profile_graph M head rho out:=code_relation M rho
 (source_parameter_expression(source_finite_parameter_names 6)(source_env_lookup_profile_law head))out.
Theorem source_zfr_env_lookup_profile_fixed M head:source_zfr_provable M(code_numeral M(sf_encode(source_env_lookup_profile_law head))).
Proof. exact(finite_old_zfr_proof_lift M old_L_background(old_env_lookup_profile_law head)
 old_L_background_valid(old_env_lookup_profile_proof head)). Qed.
Theorem source_zfr_env_lookup_profile_named M head rho out:
 source_env_lookup_profile_graph M head rho out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_env_lookup_profile_law head)6 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_env_lookup_profile_fixed M head))HG).
Qed.
Theorem source_zfr_env_lookup_profile_total M head rho:exists out,
 source_env_lookup_profile_graph M head rho out /\source_zfr_provable M out.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 6)(source_env_lookup_profile_law head))rho)as(out&HO).
 exists out. split;[exact HO|exact(source_zfr_env_lookup_profile_named M head rho out HO)].
Qed.
Print Assumptions source_zfr_env_lookup_profile_fixed.
Print Assumptions source_zfr_env_lookup_profile_named.
Print Assumptions source_zfr_env_lookup_profile_total.
