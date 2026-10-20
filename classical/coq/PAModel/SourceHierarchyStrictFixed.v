(** Lift the actual fixed strict hierarchy proof at arbitrary model names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceHierarchyStrictOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters
 SourceFiniteNameParameters SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_hierarchy_strict_law:=isolated_formula old_hierarchy_strict_law.
Definition source_hierarchy_strict_expression:=
 source_parameter_expression(source_finite_parameter_names 4)source_hierarchy_strict_law.
Theorem source_zfr_hierarchy_strict M rho out:
 code_relation M rho source_hierarchy_strict_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_hierarchy_strict_law 4 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_hierarchy_strict_law
    old_L_background_valid old_hierarchy_strict_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_hierarchy_strict.
