(** Actual source ZFR certificate for an ordinal upper bound of a set of
    ordinals, with its exact numerical constructor expression. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceNumeralLift OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift
  SourceLeastOrdinalOld SourceOrdinalUnionOld SourceOrdinalPredicate SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Definition ordinal_range_upper_source :sf_form :=
  (∀ ($0 ∈' $1 → source_ordinal_predicate)) →
  ∃ (source_ordinal_predicate ∧ ∀ ($0 ∈' $2 → ∀ ($0 ∈' $1 → $0 ∈' $2))).
Lemma ordinal_range_upper_old_calibration :
  isolated_formula old_ordinal_range_upper=ordinal_range_upper_source.
Proof. reflexivity. Qed.
Local Opaque source_ordinal_predicate.

Definition E_ordinal_range_upper := E_sf_ex (E_sf SFAnd (CEvar 0)
  (E_sf_all (E_sf SFImpl (E_sf_mem 0 2)
    (E_sf_all (E_sf SFImpl (E_sf_mem 0 1) (E_sf_mem 0 2)))))).
Definition E_ordinal_range_upper_law := E_sf SFImpl
  (E_sf_all (E_sf SFImpl (E_sf_mem 0 1) (CEvar 0))) E_ordinal_range_upper.
Definition source_ordinal_upper_graph M upper :=
  code_relation M (fun _=>source_ordinal_predicate_code M) E_ordinal_range_upper upper.
Definition source_ordinal_upper_law_graph M law :=
  code_relation M (fun _=>source_ordinal_predicate_code M) E_ordinal_range_upper_law law.

Theorem source_zfr_ordinal_upper_numeral M :
  source_zfr_provable M (code_numeral M (sf_encode ordinal_range_upper_source)).
Proof.
  rewrite <-ordinal_range_upper_old_calibration.
  exact (finite_old_zfr_proof_lift M old_least_background old_ordinal_range_upper
    old_least_background_zfr old_ordinal_range_upper_proof).
Qed.

Theorem source_ordinal_upper_numeral_graph M :
  source_ordinal_upper_law_graph M (code_numeral M (sf_encode ordinal_range_upper_source)).
Proof.
  pose proof (code_relation_numeral M (fun _=>sf_encode source_ordinal_predicate)
    E_ordinal_range_upper_law) as HG.
  assert (EE:code_value (fun _=>sf_encode source_ordinal_predicate) E_ordinal_range_upper_law=
    sf_encode ordinal_range_upper_source).
  { unfold E_ordinal_range_upper_law,E_ordinal_range_upper,ordinal_range_upper_source,
      E_sf_all,E_sf_ex,E_sf_mem.
    repeat rewrite sf_make_value. reflexivity. }
  rewrite EE in HG. exact HG.
Qed.

Theorem source_zfr_ordinal_upper_law M law :
  source_ordinal_upper_law_graph M law ->source_zfr_provable M law.
Proof.
  intro HG.
  pose proof (code_relation_functional M _ _ law (code_numeral M (sf_encode ordinal_range_upper_source))
    HG (source_ordinal_upper_numeral_graph M)) as E. subst law.
  exact (source_zfr_ordinal_upper_numeral M).
Qed.

Print Assumptions ordinal_range_upper_old_calibration.
Print Assumptions source_zfr_ordinal_upper_numeral.
Print Assumptions source_ordinal_upper_numeral_graph.
Print Assumptions source_zfr_ordinal_upper_law.
