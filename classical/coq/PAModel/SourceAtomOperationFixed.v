(** Genuine ZFR source certificates for atomic closure operations, at
 arbitrary internal names for all seven roles. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceAtomOperationOld SourceLFixed SourceLNonempty
 OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_atom_operation_law member:sf_form:=isolated_formula(old_atom_operation_law member).
Definition source_atom_operation_expression member:=source_parameter_expression(source_finite_parameter_names 7)(source_atom_operation_law member).
Theorem source_zfr_atom_operation M member rho out:
 code_relation M rho(source_atom_operation_expression member)out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_atom_operation_law member)7 rho out);[|exact HO].
 apply(proj2(source_zfr_descriptor_provable M _)).
 exact(finite_old_zfr_proof_lift M old_L_background(old_atom_operation_law member)
  old_L_background_valid(old_atom_operation_proof member)).
Qed.
Print Assumptions source_zfr_atom_operation.
