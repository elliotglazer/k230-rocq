(** Actual fixed ZFR certificates used in the internal NumF comparison inductions. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumFComparisonOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
Unset Implicit Arguments.
Definition source_numf_empty_unique_law :=isolated_formula old_numf_empty_unique.
Theorem source_zfr_numf_empty_unique_fixed M :source_zfr_provable M(code_numeral M(sf_encode source_numf_empty_unique_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_numf_empty_unique old_L_background_valid old_numf_empty_unique_proof). Qed.
Definition source_numf_successor_square_law :=isolated_formula old_numf_successor_square.
Theorem source_zfr_numf_successor_square_fixed M :source_zfr_provable M(code_numeral M(sf_encode source_numf_successor_square_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_numf_successor_square old_L_background_valid old_numf_successor_square_proof). Qed.
Definition source_numf_successor_member_law :=isolated_formula old_numf_successor_member.
Theorem source_zfr_numf_successor_member_fixed M :source_zfr_provable M(code_numeral M(sf_encode source_numf_successor_member_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_numf_successor_member old_L_background_valid old_numf_successor_member_proof). Qed.
Definition source_numf_successor_upper_law :=isolated_formula old_numf_successor_upper.
Theorem source_zfr_numf_successor_upper_fixed M :source_zfr_provable M(code_numeral M(sf_encode source_numf_successor_upper_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_numf_successor_upper old_L_background_valid old_numf_successor_upper_proof). Qed.
Definition source_numf_member_unequal_law :=isolated_formula old_numf_member_unequal.
Theorem source_zfr_numf_member_unequal_fixed M :source_zfr_provable M(code_numeral M(sf_encode source_numf_member_unequal_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_numf_member_unequal old_L_background_valid old_numf_member_unequal_proof). Qed.
Print Assumptions source_zfr_numf_empty_unique_fixed.
Print Assumptions source_zfr_numf_successor_square_fixed.
Print Assumptions source_zfr_numf_successor_member_fixed.
Print Assumptions source_zfr_numf_successor_upper_fixed.
Print Assumptions source_zfr_numf_member_unequal_fixed.
