(** Actual unconditional source proof of existence of an ordinal. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceOrdinalExistsOld SourceOrdinalPredicate SourceLFixed SourceLNonempty
 OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
Unset Implicit Arguments.
Definition source_ordinal_exists_code M :=code_numeral M(sf_make SFEx(sf_encode source_ordinal_predicate)0).
Theorem source_ordinal_exists_graph M :sf_relation M SFEx(source_ordinal_predicate_code M)(zeroM M)(source_ordinal_exists_code M).
Proof. exact(sf_make_numeral M SFEx(sf_encode source_ordinal_predicate)0). Qed.
Theorem source_zfr_ordinal_exists M :source_zfr_provable M(source_ordinal_exists_code M).
Proof.
 exact(finite_old_zfr_proof_lift M old_L_background old_ordinal_exists old_L_background_valid old_ordinal_exists_proof).
Qed.
Print Assumptions source_ordinal_exists_graph.
Print Assumptions source_zfr_ordinal_exists.
