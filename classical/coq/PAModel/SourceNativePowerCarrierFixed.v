(** Actual fixed Power Set selector law at arbitrary PA-model names.
    The reflection antecedent remains an ordinary formula, not an axiom. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge
 SourceNativePowerCarrierOld OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition source_native_cp_theta:=isolated_formula old_native_cp_theta.
Definition source_native_cp_subset_expression:=source_parameter_expression(source_finite_parameter_names 4)
 (isolated_formula old_native_cp_subset_law).
Theorem source_zfr_native_cp_subset_named M rho out:
 code_relation M rho source_native_cp_subset_expression out->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(isolated_formula old_native_cp_subset_law)4 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)).
 exact(finite_old_zfr_proof_lift M old_native_cp_background old_native_cp_subset_law
  old_native_cp_background_valid old_native_cp_subset_proof).
Qed.
Print Assumptions source_zfr_native_cp_subset_named.
