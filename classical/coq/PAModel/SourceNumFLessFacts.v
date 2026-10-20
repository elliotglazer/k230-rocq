(** Actual fixed predecessor-comparison facts, with exact source graphs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift SourceNumFLessFactsOld
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability SourceNumFUniqueSyntax.
From Undecidability.FOL Require Import Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_numf_less_fact_law equal :=isolated_formula(old_numf_less_fact equal).
Definition numf_comparison_atom M (equal:bool) :=code_numeral M(sf_make(if equal then SFEqual else SFMember)1 0).
Theorem source_zfr_numf_less_fact M equal :source_zfr_provable M(code_numeral M(sf_encode(source_numf_less_fact_law equal))).
Proof. exact(finite_old_zfr_proof_lift M old_L_background(old_numf_less_fact equal)old_L_background_valid(old_numf_less_fact_proof equal)). Qed.
Lemma numf_less_fact_shape equal :source_numf_less_fact_law equal=
 ((if equal then $1 ≡' $0 else $1 ∈' $0)→numf_successor02→$1 ∈' $2).
Proof. rewrite numf_successor02_shape. destruct equal;reflexivity. Qed.
Theorem source_numf_less_fact_shell M equal :exists inner law,
 sf_relation M SFImpl(code_numeral M(sf_encode numf_successor02))(code_numeral M(sf_make SFMember 1 2))inner /\
 sf_relation M SFImpl(numf_comparison_atom M equal)inner law /\source_zfr_provable M law.
Proof.
 set(a:=sf_encode numf_successor02). set(e:=sf_make SFMember 1 2).
 set(r:=sf_make(if equal then SFEqual else SFMember)1 0).
 set(i:=sf_make SFImpl a e). set(o:=sf_make SFImpl r i).
 exists(code_numeral M i),(code_numeral M o).
 split;[exact(sf_make_numeral M SFImpl a e)|]. split;[exact(sf_make_numeral M SFImpl r i)|].
 pose proof(source_zfr_numf_less_fact M equal)as P. rewrite numf_less_fact_shape in P. destruct equal;exact P.
Qed.
Print Assumptions source_zfr_numf_less_fact.
Print Assumptions source_numf_less_fact_shell.
