(** Source-core provability and the exact remaining axiom-image interface.
    The consistency implication below is conditional on that unproved family. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalContexts
  NumericalSourceFull NumericalCoreAxioms SupportedTheoryTransfer BootstrapSpecializations
  NumericalQuotation NumericalEquivalence.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_core_context M b c n :=
  forall f, context_member M b c n f -> numerical_zfc_core_source_axiom M f.
Definition source_core_context_formula (b c n : term) : form :=
  ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 → numerical_zfc_core_source_axiom_formula $0).
Local Opaque holds context_member_formula numerical_zfc_core_source_axiom_formula.
Lemma source_core_context_formula_correct M rho b c n :
  holds M rho (source_core_context_formula b c n) <->
  source_core_context M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold source_core_context_formula,source_core_context.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite numerical_zfc_core_source_axiom_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition source_core_provable M f := exists b c n,
  source_core_context M b c n /\ source_full_prv M b c n f.
Definition source_core_provable_formula (f : term) : form :=
  ∃∃∃ (source_core_context_formula $2 $1 $0 ∧ source_full_prv_formula $2 $1 $0 (f`[↑]`[↑]`[↑])).
Local Opaque source_core_context_formula source_full_prv_formula.
Lemma source_core_provable_formula_correct M rho f :
  holds M rho (source_core_provable_formula f) <->
  source_core_provable M (evalM M rho f).
Proof.
  unfold source_core_provable_formula,source_core_provable.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_core_context_formula_correct.
  setoid_rewrite source_full_prv_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_core_context_closed M b c n : source_core_context M b c n ->
  context_bounded M b c n (zeroM M).
Proof.
  intros H f Hf. exact (numerical_zfc_core_source_axiom_closed M f (H f Hf)).
Qed.


Definition core_marker_images M := forall marker,
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  forall f q,numerical_zfc_core_source_axiom M f ->
    numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) q -> numerical_implies M marker q.
Definition source_core_consistent M := ~source_core_provable M (zeroM M).

Theorem source_core_refutation_to_K M : core_marker_images M ->
  source_core_provable M (zeroM M) -> numerically_provable M (code_numeral M 1).
Proof.
  intros HI [b [c [n [HC HP]]]].
  apply (source_theory_contradiction_transfer M b c n (source_core_context_closed M b c n HC)).
  - intros marker HM f q HF HQ. exact (HI marker HM f q (HC f HF) HQ).
  - exact HP.
Qed.
Corollary K_consistency_implies_source_core_consistency M : core_marker_images M ->
  (~numerically_provable M (code_numeral M 1)) -> source_core_consistent M.
Proof. intros HI HK HP. exact (HK (source_core_refutation_to_K M HI HP)). Qed.

Print Assumptions source_core_provable_formula_correct.
Print Assumptions source_core_refutation_to_K.
Print Assumptions K_consistency_implies_source_core_consistency.
