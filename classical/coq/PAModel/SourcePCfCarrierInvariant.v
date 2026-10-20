(** PA-definable proof production for equality transport of an internally
    finite PCf conjunction. Every piece law is an actual ZFR deduction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing SetFormulaCodes SourceBounded NumericalContexts SourceHierarchySyntax
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionFormula SourcePieceConjunctionBounds
  SourcePCfCarrierProgram SourcePropositionalTemplates SourceFunctionalityShells
  SourceConditionalIdentity SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceWitnessProofComposition.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_pcf_carrier_equality_at M domain level n:=forall sb sc d X Y equal old new map law k,
  source_piece_table_valid M sb sc n ->coding_lt M d k ->coding_lt M X k ->coding_lt M Y k ->
  sf_relation M SFEqual X Y equal ->source_piece_conjunction M domain level sb sc n d X old ->
  source_piece_conjunction M domain level sb sc n d Y new ->sf_relation M SFImpl old new map ->
  sf_relation M SFImpl equal map law ->source_zfr_provable M law.
Definition source_pcf_carrier_equality_formula:form:=
  ∀∀∀∀∀∀∀∀∀∀∀(source_piece_table_valid_formula $10 $9 $11 →
    Peano.sless $8 $0 →Peano.sless $7 $0 →Peano.sless $6 $0 →sf_formula SFEqual $7 $6 $5 →
    source_piece_conjunction_formula $12 $13 $10 $9 $11 $8 $7 $4 →
    source_piece_conjunction_formula $12 $13 $10 $9 $11 $8 $6 $3 →
    sf_formula SFImpl $4 $3 $2 →sf_formula SFImpl $5 $2 $1 →source_zfr_provable_formula $1).
Local Opaque holds source_piece_table_valid_formula Peano.sless sf_formula source_piece_conjunction_formula source_zfr_provable_formula.
Lemma source_pcf_carrier_equality_definable M domain level:
  Definable1 M(source_pcf_carrier_equality_at M domain level).
Proof.
  exists source_pcf_carrier_equality_formula,(domain.:level.:fun _=>zeroM M). intro n.
  unfold source_pcf_carrier_equality_formula,source_pcf_carrier_equality_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_piece_table_valid_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite source_piece_conjunction_formula_correct.
  setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Definition source_pcf_carrier_environment{A}(equal previousLeft previousRight pieceLeft pieceRight:A)i:=
  match i with 0=>equal|1=>previousLeft|2=>previousRight|3=>pieceLeft|4=>pieceRight|_=>equal end.


Print Assumptions source_pcf_carrier_equality_definable.
