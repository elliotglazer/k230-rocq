(** Genuine pair/union profile deduction at arbitrary internal names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 SourcePairUnionProfileOld SourceLFixed SourceLNonempty OldZFRProofLift SourceZFRProvability
 SourceFiniteParameters SourceFiniteNameParameters SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_pair_union_profile_law:=isolated_formula old_pair_union_profile_law.
Definition source_pair_union_profile_graph M rho out:=code_relation M rho
 (source_parameter_expression(source_finite_parameter_names 4)source_pair_union_profile_law)out.
Theorem source_zfr_pair_union_profile_fixed M:source_zfr_provable M(code_numeral M(sf_encode source_pair_union_profile_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_pair_union_profile_law
 old_L_background_valid old_pair_union_profile_proof). Qed.
Theorem source_zfr_pair_union_profile_named M rho out:
 source_pair_union_profile_graph M rho out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_pair_union_profile_law 4 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_pair_union_profile_fixed M))HG).
Qed.
Print Assumptions source_zfr_pair_union_profile_fixed.
Print Assumptions source_zfr_pair_union_profile_named.
