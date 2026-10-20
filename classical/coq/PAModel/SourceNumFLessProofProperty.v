(** Genuine PA formula for the internal numeral membership comparison invariant. *)
From PAModel Require Import Model FiniteCoding FiniteCRTFormula NumericalProofs SourceDefinabilityBounds SourceNumFLessRecipe SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_numf_less_proof_at M l :=forall k p q x y out,
 coding_lt M k l ->source_numf M k p ->source_numf M l q ->source_numf_less_recipe M p q x y out ->source_zfr_provable M out.
Definition source_numf_less_proof_formula :form :=∀∀∀∀∀∀(
 Peano.sless $5 $6 →source_numf_formula $5 $4 →source_numf_formula $6 $3 →
 source_numf_less_recipe_formula $4 $3 $2 $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds Peano.sless source_numf_formula source_numf_less_recipe_formula source_zfr_provable_formula.
Theorem source_numf_less_proof_definable M :Definable1 M(source_numf_less_proof_at M).
Proof.
 exists source_numf_less_proof_formula,(fun _=>zeroM M). intro l.
 unfold source_numf_less_proof_formula,source_numf_less_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all. repeat setoid_rewrite NumericalProofs.holds_imp.
 setoid_rewrite less_formula_correct. setoid_rewrite source_numf_formula_correct.
 setoid_rewrite source_numf_less_recipe_formula_correct. setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Print Assumptions source_numf_less_proof_definable.
