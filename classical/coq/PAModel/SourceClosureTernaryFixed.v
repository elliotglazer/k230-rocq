(** Actual ZFR closure certificates for atomic and quantified representation branches. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceClosureTernaryOld
  SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.

Definition source_closure_ternary_law k :=isolated_formula(old_closure_ternary_law k).
Definition source_closure_ternary_expression k :=source_parameter_expression(source_finite_parameter_names 6)(source_closure_ternary_law k).

Theorem source_zfr_closure_ternary M k rho out : (k<8)%nat ->
  code_relation M rho(source_closure_ternary_expression k)out ->source_zfr_provable M out.
Proof.
  intros HK HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_closure_ternary_law k)6 rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background(old_closure_ternary_law k)
      old_L_background_valid(old_closure_ternary_proof k HK)).
  - exact HO.
Qed.

Print Assumptions source_zfr_closure_ternary.
