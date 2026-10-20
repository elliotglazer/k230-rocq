(** Actual fixed membership-irreflexivity certificates and exact source graphs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift SourceNumFDistinctOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
Unset Implicit Arguments.
Definition numf_distinct_member M(reverse:bool):=code_numeral M(sf_make SFMember(if reverse then 1 else 0)(if reverse then 0 else 1)).
Theorem source_zfr_numf_distinct_fixed M reverse:source_zfr_provable M
 (code_numeral M(sf_encode(isolated_formula(old_numf_distinct_fact reverse)))).
Proof. exact(finite_old_zfr_proof_lift M old_L_background(old_numf_distinct_fact reverse)old_L_background_valid(old_numf_distinct_fact_proof reverse)). Qed.
Theorem source_numf_distinct_fact_shell M reverse:exists neg fact,
 sf_relation M SFImpl(code_numeral M(sf_make SFEqual 0 1))(zeroM M)neg /\
 sf_relation M SFImpl(numf_distinct_member M reverse)neg fact /\source_zfr_provable M fact.
Proof.
 set(e:=sf_make SFEqual 0 1). set(m:=sf_make SFMember(if reverse then 1 else 0)(if reverse then 0 else 1)).
 set(n:=sf_make SFImpl e 0). set(o:=sf_make SFImpl m n).
 exists(code_numeral M n),(code_numeral M o).
 split;[exact(sf_make_numeral M SFImpl e 0)|]. split;[exact(sf_make_numeral M SFImpl m n)|].
 pose proof(source_zfr_numf_distinct_fixed M reverse)as P. destruct reverse;exact P.
Qed.
Print Assumptions source_zfr_numf_distinct_fixed.
Print Assumptions source_numf_distinct_fact_shell.
