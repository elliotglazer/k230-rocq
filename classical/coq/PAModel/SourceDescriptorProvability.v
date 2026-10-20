(** A unary arithmetic axiom descriptor together with the internally coded
    source natural-deduction calculus. No NumericalTheory proof rules occur. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalTheories NumericalContexts NumericalSourceFull SourceAxiomContexts.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_descriptor_provable M T f := exists b c n,
  source_axiom_context M T b c n /\ source_full_prv M b c n f.
Definition source_descriptor_provable_formula T (f:term) : form :=
  ∃∃∃ (source_axiom_context_formula T $2 $1 $0 ∧
    source_full_prv_formula $2 $1 $0 (f`[↑]`[↑]`[↑])).
Local Opaque holds source_axiom_context_formula source_full_prv_formula.

Theorem source_descriptor_provable_formula_correct M T rho f :
  holds M rho (source_descriptor_provable_formula T f) <->
  source_descriptor_provable M T (evalM M rho f).
Proof.
  unfold source_descriptor_provable_formula,source_descriptor_provable.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_axiom_context_formula_correct.
  setoid_rewrite source_full_prv_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition source_descriptor_consistent M T :=
  ~source_descriptor_provable M T (zeroM M).

Print Assumptions source_descriptor_provable_formula_correct.
