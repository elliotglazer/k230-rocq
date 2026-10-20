(** Actual ZFR difference and environment-extension closure certificates. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceClosureBinaryOld
  SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_closure_binary_law k :=isolated_formula(old_closure_binary_law k).
Definition source_closure_binary_expression k :=source_parameter_expression(source_finite_parameter_names 5)(source_closure_binary_law k).

Theorem source_zfr_closure_binary M k rho out : (k<8)%nat ->
  code_relation M rho(source_closure_binary_expression k)out ->source_zfr_provable M out.
Proof.
  intros HK HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_closure_binary_law k)5 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background(old_closure_binary_law k)
      old_L_background_valid(old_closure_binary_proof k HK)).
  - exact HO.
Qed.

Theorem source_zfr_closure_difference M rho out :
  code_relation M rho(source_closure_binary_expression 2)out ->source_zfr_provable M out.
Proof. apply(source_zfr_closure_binary M 2 rho out). lia. Qed.

Theorem source_zfr_closure_extension M rho out :
  code_relation M rho(source_closure_binary_expression 3)out ->source_zfr_provable M out.
Proof. apply(source_zfr_closure_binary M 3 rho out). lia. Qed.

Print Assumptions source_zfr_closure_binary.
Print Assumptions source_zfr_closure_difference.
Print Assumptions source_zfr_closure_extension.
