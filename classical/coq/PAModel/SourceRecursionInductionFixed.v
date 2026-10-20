(** Actual finite STot/SInd use proofs at arbitrary internal source names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge SourceRecursionInductionOld
 SourceLFixed SourceLNonempty OldZFRProofLift SourceZFRProvability SourceFiniteParameters SourceFiniteNameParameters
 SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_rec_induction_law induction:=isolated_formula(old_recursion_induction_law induction).
Theorem source_zfr_rec_induction_fixed M induction:source_zfr_provable M(code_numeral M(sf_encode(source_rec_induction_law induction))).
Proof. exact(finite_old_zfr_proof_lift M old_L_background(old_recursion_induction_law induction)old_L_background_valid(old_recursion_induction_proof induction)). Qed.
Theorem source_zfr_rec_induction_named M induction rho out:
 code_relation M rho(source_parameter_expression(source_finite_parameter_names 3)(source_rec_induction_law induction))out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor(source_rec_induction_law induction)3 rho out
  (proj2(source_zfr_descriptor_provable M _)(source_zfr_rec_induction_fixed M induction))HG).
Qed.
Print Assumptions source_zfr_rec_induction_fixed.
Print Assumptions source_zfr_rec_induction_named.
