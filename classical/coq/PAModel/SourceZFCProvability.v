(** Concrete source-side arithmetic provability. This uses the eight-tag
    natural-deduction calculus, not the four-tag NumericalTheory calculus.
    The final comparison sentence is defined here but is not proved true. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalContexts
  NumericalSourceFull NumericalZFCAxioms ClosedSourceQuotation SentenceBounds NumericalTheories TheoryProofInduction.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_zfc_context M b c n :=
  forall f, context_member M b c n f -> numerical_zfc_source_axiom M f.
Definition source_zfc_context_formula (b c n : term) : form :=
  ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 → numerical_zfc_source_axiom_formula $0).
Local Opaque holds context_member_formula numerical_zfc_source_axiom_formula.
Lemma source_zfc_context_formula_correct M rho b c n :
  holds M rho (source_zfc_context_formula b c n) <->
  source_zfc_context M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold source_zfc_context_formula,source_zfc_context.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite numerical_zfc_source_axiom_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition source_zfc_provable M f := exists b c n,
  source_zfc_context M b c n /\ source_full_prv M b c n f.
Definition source_zfc_provable_formula (f : term) : form :=
  ∃∃∃ (source_zfc_context_formula $2 $1 $0 ∧ source_full_prv_formula $2 $1 $0 (f`[↑]`[↑]`[↑])).
Local Opaque source_zfc_context_formula source_full_prv_formula.
Lemma source_zfc_provable_formula_correct M rho f :
  holds M rho (source_zfc_provable_formula f) <->
  source_zfc_provable M (evalM M rho f).
Proof.
  unfold source_zfc_provable_formula,source_zfc_provable.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_zfc_context_formula_correct.
  setoid_rewrite source_full_prv_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_zfc_context_closed M b c n : source_zfc_context M b c n ->
  context_bounded M b c n (zeroM M).
Proof.
  intros H f Hf. exact (numerical_zfc_source_axiom_closed M f (H f Hf)).
Qed.

Definition source_zfc_consistent M := ~source_zfc_provable M (zeroM M).
Definition numerical_k_consistent M := ~numerically_provable M (code_numeral M 1).
Theorem numerical_k_consistency_is_K230 M :
  numerical_k_consistent M <-> theory_consistent M K230Theory.
Proof.
  unfold numerical_k_consistent,theory_consistent. rewrite K230Theory_provable. reflexivity.
Qed.
Definition source_zfc_consistency_formula : form := ¬source_zfc_provable_formula zero.
Definition numerical_k_consistency_formula : form := ¬numerically_provable_formula (num 1).
Definition k_zfc_comparison_sentence : form :=
  (numerical_k_consistency_formula → source_zfc_consistency_formula) ∧
  (source_zfc_consistency_formula → numerical_k_consistency_formula).

Local Opaque source_zfc_provable_formula numerically_provable_formula.
Lemma source_zfc_consistency_formula_correct M rho :
  holds M rho source_zfc_consistency_formula <-> source_zfc_consistent M.
Proof.
  unfold source_zfc_consistency_formula,source_zfc_consistent.
  change ((holds M rho (source_zfc_provable_formula zero) -> False) <->
    (source_zfc_provable M (zeroM M) -> False)).
  now rewrite source_zfc_provable_formula_correct.
Qed.
Lemma numerical_k_consistency_formula_correct M rho :
  holds M rho numerical_k_consistency_formula <-> numerical_k_consistent M.
Proof.
  unfold numerical_k_consistency_formula,numerical_k_consistent.
  change ((holds M rho (numerically_provable_formula (num 1)) -> False) <->
    (numerically_provable M (code_numeral M 1) -> False)).
  now rewrite numerically_provable_formula_correct.
Qed.
Local Opaque numerical_k_consistency_formula source_zfc_consistency_formula.
Theorem k_zfc_comparison_sentence_correct M rho :
  holds M rho k_zfc_comparison_sentence <->
  (numerical_k_consistent M <-> source_zfc_consistent M).
Proof.
  unfold k_zfc_comparison_sentence. rewrite holds_and.
  repeat setoid_rewrite holds_imp.
  rewrite !source_zfc_consistency_formula_correct, !numerical_k_consistency_formula_correct.
  reflexivity.
Qed.

Local Transparent numerical_k_consistency_formula source_zfc_consistency_formula.
Theorem source_zfc_provable_formula_bound : bounded 1 (source_zfc_provable_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Theorem k_zfc_comparison_sentence_closed : bounded 0 k_zfc_comparison_sentence.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_zfc_provable_formula_correct.
Print Assumptions source_zfc_context_closed.
Print Assumptions numerical_k_consistency_is_K230.
Print Assumptions k_zfc_comparison_sentence_correct.
Print Assumptions source_zfc_provable_formula_bound.
Print Assumptions k_zfc_comparison_sentence_closed.



