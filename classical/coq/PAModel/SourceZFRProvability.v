(** Source provability for core plus exact fixed Foundation. The context is
    internally finite, and proofs use the existing full source calculus. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalTheories NumericalContexts NumericalSourceFull SourceBounded
  NumericalZFRAxioms SourceAxiomContexts SourceDescriptorProvability SourceSetTheoryDescriptors
  CoreConsistencyReduction SourceZFCProvability NumericalCoreAxioms NumericalZFCAxioms.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_zfr_context M b c n := forall f,
  context_member M b c n f -> numerical_zfr_source_axiom M f.
Definition source_zfr_context_formula (b c n:term) : form :=
  ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 → numerical_zfr_source_axiom_formula $0).
Local Opaque holds context_member_formula numerical_zfr_source_axiom_formula.

Theorem source_zfr_context_formula_correct M rho b c n :
  holds M rho (source_zfr_context_formula b c n) <->
  source_zfr_context M (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold source_zfr_context_formula,source_zfr_context.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite numerical_zfr_source_axiom_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_zfr_context_closed M b c n : source_zfr_context M b c n ->
  context_bounded M b c n (zeroM M).
Proof. intros H f HF. exact (numerical_zfr_source_axiom_closed M f (H f HF)). Qed.

Definition source_zfr_provable M f := exists b c n,
  source_zfr_context M b c n /\ source_full_prv M b c n f.
Definition source_zfr_provable_formula (f:term) : form :=
  ∃∃∃ (source_zfr_context_formula $2 $1 $0 ∧ source_full_prv_formula $2 $1 $0 (f`[↑]`[↑]`[↑])).
Local Opaque source_zfr_context_formula source_full_prv_formula.

Theorem source_zfr_provable_formula_correct M rho f :
  holds M rho (source_zfr_provable_formula f) <-> source_zfr_provable M (evalM M rho f).
Proof.
  unfold source_zfr_provable_formula,source_zfr_provable.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_zfr_context_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_zfr_descriptor_context M b c n :
  source_axiom_context M ZFRSourceDescriptor b c n <-> source_zfr_context M b c n.
Proof.
  split.
  - intros [_ H] f HF. apply ZFRSourceDescriptor_axiom. exact (H f HF).
  - intro H. split;[exact (source_zfr_context_closed M b c n H)|].
    intros f HF. apply ZFRSourceDescriptor_axiom. exact (H f HF).
Qed.

Theorem source_zfr_descriptor_provable M f :
  source_descriptor_provable M ZFRSourceDescriptor f <-> source_zfr_provable M f.
Proof.
  unfold source_descriptor_provable,source_zfr_provable.
  setoid_rewrite source_zfr_descriptor_context. reflexivity.
Qed.

Theorem source_core_context_in_zfr M b c n :
  source_core_context M b c n -> source_zfr_context M b c n.
Proof. intros H f HF. apply numerical_core_source_axiom_in_zfr. exact (H f HF). Qed.
Theorem source_zfr_context_in_zfc M b c n :
  source_zfr_context M b c n -> source_zfc_context M b c n.
Proof. intros H f HF. apply numerical_zfr_source_axiom_in_zfc. exact (H f HF). Qed.
Theorem source_core_provable_in_zfr M f : source_core_provable M f -> source_zfr_provable M f.
Proof.
  intros (b & c & n & HC & HP). exists b,c,n. split;[|exact HP].
  exact (source_core_context_in_zfr M b c n HC).
Qed.
Theorem source_zfr_provable_in_zfc M f : source_zfr_provable M f -> source_zfc_provable M f.
Proof.
  intros (b & c & n & HC & HP). exists b,c,n. split;[|exact HP].
  exact (source_zfr_context_in_zfc M b c n HC).
Qed.

Definition source_zfr_consistent M := ~source_zfr_provable M (zeroM M).

Print Assumptions source_zfr_context_formula_correct.
Print Assumptions source_zfr_context_closed.
Print Assumptions source_zfr_provable_formula_correct.
Print Assumptions source_zfr_descriptor_provable.
Print Assumptions source_core_provable_in_zfr.
Print Assumptions source_zfr_provable_in_zfc.
