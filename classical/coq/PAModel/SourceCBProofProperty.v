(** The exact PA-definable induction invariant for internally arbitrary
    tuple lengths. Its conclusion is an actual numerical ZFR proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRTFormula CodeExpressions NumericalProofs SourceBounded
  NumericalInstantiation SetFormulaCodes SourceCBGoal SourceCBBase SourceHierarchySyntax SourceLFixed
  SourceOrdinalPredicate SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Definition source_cb_proof_at M domain level ordinal count :=forall phi n g og goal implication,
  source_bounded M phi(addM M count(succM M n)) ->coding_lt M g(succM M n) ->
  numerical_instantiation M ordinal g og ->source_cb_goal M domain level ordinal count phi goal ->
  sf_relation M SFImpl og goal implication ->source_descriptor_provable M ZFRSourceDescriptor implication.

Definition source_cb_proof_formula :form:=
  ∀∀∀∀∀∀(source_bounded_accept_formula $5 ($6 ⊕ σ $4) →Peano.sless $3(σ $4) →
    numerical_instantiation_formula $9 $3 $2 →source_cb_goal_formula $7 $8 $9 $6 $5 $1 →
    sf_formula SFImpl $2 $1 $0 →source_descriptor_provable_formula ZFRSourceDescriptor $0).
Local Opaque holds source_bounded_accept_formula Peano.sless numerical_instantiation_formula
  source_cb_goal_formula sf_formula source_descriptor_provable_formula.

Theorem source_cb_proof_definable M domain level ordinal:
  Definable1 M(source_cb_proof_at M domain level ordinal).
Proof.
  exists source_cb_proof_formula,(domain.:level.:ordinal.:fun _=>zeroM M). intro count.
  unfold source_cb_proof_formula,source_cb_proof_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite source_cb_goal_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite source_descriptor_provable_formula_correct. reflexivity.
Qed.

Theorem source_cb_proof_zero M level:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_cb_proof_at M(source_L_domain_code M)level(source_ordinal_predicate_code M)(zeroM M).
Proof.
  intros HL phi n g og goal implication HB HG HOrd HGoal HImp.
  rewrite coding_add_zero in HB.
  apply(proj2(source_zfr_descriptor_provable M implication)).
  exact(source_zfr_cb_zero M level phi g og goal implication n HL HB HG HOrd HGoal HImp).
Qed.

Print Assumptions source_cb_proof_definable.
Print Assumptions source_cb_proof_zero.
