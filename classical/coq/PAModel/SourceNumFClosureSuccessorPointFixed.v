(** The actually proved fixed closure-successor point certificate. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumFClosureSuccessorPointOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
Unset Implicit Arguments.
Definition source_numf_closure_successor_point :=isolated_formula old_numf_closure_successor_point.
Theorem source_zfr_numf_closure_successor_point M :source_zfr_provable M
 (code_numeral M(sf_encode source_numf_closure_successor_point)).
Proof.
 exact(finite_old_zfr_proof_lift M old_L_background old_numf_closure_successor_point
 old_L_background_valid old_numf_closure_successor_point_proof).
Qed.
Print Assumptions source_zfr_numf_closure_successor_point.
