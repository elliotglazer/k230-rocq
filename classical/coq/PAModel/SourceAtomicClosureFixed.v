(** Actual source proofs of closure under ternary operations. All six free
    names range independently over the arbitrary PA model. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceAtomicClosureOld SourceLFixed SourceLNonempty
 OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_atomic_closure_ternary_law k:=isolated_formula(old_atomic_closure_ternary_law k).
Definition source_atomic_closure_ternary_expression k:=source_parameter_expression(source_finite_parameter_names 6)(source_atomic_closure_ternary_law k).
Theorem source_zfr_atomic_closure_ternary M k rho out:(k<8)%nat->
 code_relation M rho(source_atomic_closure_ternary_expression k)out->source_zfr_provable M out.
Proof.
 intros HK HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_atomic_closure_ternary_law k)6 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background(old_atomic_closure_ternary_law k)
    old_L_background_valid(old_atomic_closure_ternary_proof k HK)).
 - exact HO.
Qed.
Theorem source_zfr_atomic_closure_operation M(member:bool)rho out:
 code_relation M rho(source_atomic_closure_ternary_expression(if member then 6 else 7))out->source_zfr_provable M out.
Proof. apply(source_zfr_atomic_closure_ternary M(if member then 6 else 7)rho out). destruct member;lia. Qed.
Print Assumptions source_zfr_atomic_closure_ternary.
Print Assumptions source_zfr_atomic_closure_operation.
