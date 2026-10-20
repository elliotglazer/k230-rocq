(** Actual arbitrary-name finite prerequisites for uniform local definability.
    The old ZFR background is completely discharged. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceLocalDefinabilityOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_local_def_exists_law:=isolated_formula old_local_def_exists_law.
Definition source_local_def_exists_expression:=source_parameter_expression
 (source_finite_parameter_names 1)source_local_def_exists_law.
Theorem source_zfr_local_def_exists M rho out:
 code_relation M rho source_local_def_exists_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_local_def_exists_law 1 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_local_def_exists_law
    old_L_background_valid old_local_def_exists_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_local_def_exists.
Definition source_local_def_unpack_law:=isolated_formula old_local_def_unpack_law.
Definition source_local_def_unpack_expression:=source_parameter_expression
 (source_finite_parameter_names 2)source_local_def_unpack_law.
Theorem source_zfr_local_def_unpack M rho out:
 code_relation M rho source_local_def_unpack_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_local_def_unpack_law 2 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_local_def_unpack_law
    old_L_background_valid old_local_def_unpack_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_local_def_unpack.
Definition source_local_L_def_member_law:=isolated_formula old_local_L_def_member_law.
Definition source_local_L_def_member_expression:=source_parameter_expression
 (source_finite_parameter_names 4)source_local_L_def_member_law.
Theorem source_zfr_local_L_def_member M rho out:
 code_relation M rho source_local_L_def_member_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_local_L_def_member_law 4 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_local_L_def_member_law
    old_L_background_valid old_local_L_def_member_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_local_L_def_member.
Definition source_local_selection_operation_law:=isolated_formula old_local_selection_operation_law.
Definition source_local_selection_operation_expression:=source_parameter_expression
 (source_finite_parameter_names 5)source_local_selection_operation_law.
Theorem source_zfr_local_selection_operation M rho out:
 code_relation M rho source_local_selection_operation_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_local_selection_operation_law 5 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_local_selection_operation_law
    old_L_background_valid old_local_selection_operation_proof).
 - exact HO.
Qed.
Print Assumptions source_zfr_local_selection_operation.
