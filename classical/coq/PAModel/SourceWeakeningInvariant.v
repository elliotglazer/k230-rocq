(** An arithmetic induction predicate for proof weakening. It keeps the
    original derivation, so every intermediate source formula stays valid. *)
From PAModel Require Import Model CodeExpressions NumericalProofs NumericalContexts NumericalTraces
  SourceSequents SourceQuantifierRules NumericalSourceFull SourceContextTransport.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_weakening_sequents M r := forall b c n f u v l,
  source_sequent M b c n f r -> context_included M b c n u v l ->
  source_context_finite_bound M u v l -> source_full_prv M u v l f.
Definition source_weakening_branches M r := forall b c n a d f u v l,
  source_branches M b c n a d f r -> context_included M b c n u v l ->
  source_context_finite_bound M u v l -> source_full_branches M u v l a d f.
Definition source_weakening_invariant M r :=
  source_full_row M r /\ source_weakening_sequents M r /\ source_weakening_branches M r.

Definition source_weakening_sequents_formula : form :=
  ∀∀∀∀∀∀∀ (source_sequent_formula $6 $5 $4 $3 $7 →
    context_included_formula $6 $5 $4 $2 $1 $0 →
    source_context_finite_bound_formula $2 $1 $0 → source_full_prv_formula $2 $1 $0 $3).
Definition source_weakening_branches_formula : form :=
  ∀∀∀∀∀∀∀∀∀ (source_branches_formula $8 $7 $6 $5 $4 $3 $9 →
    context_included_formula $8 $7 $6 $2 $1 $0 →
    source_context_finite_bound_formula $2 $1 $0 → source_full_branches_formula $2 $1 $0 $5 $4 $3).
Definition source_weakening_invariant_formula : form :=
  trace_derives_formula source_full_rules $0 ∧
  (source_weakening_sequents_formula ∧ source_weakening_branches_formula).
Local Opaque holds source_sequent_formula source_branches_formula context_included_formula
  source_context_finite_bound_formula source_full_prv_formula source_full_branches_formula
  trace_derives_formula.

Theorem source_weakening_sequents_formula_correct M r :
  holds M (r .: fun _=>zeroM M) source_weakening_sequents_formula <->
  source_weakening_sequents M r.
Proof.
  unfold source_weakening_sequents_formula,source_weakening_sequents.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_sequent_formula_correct.
  setoid_rewrite context_included_formula_correct.
  setoid_rewrite source_context_finite_bound_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_weakening_branches_formula_correct M r :
  holds M (r .: fun _=>zeroM M) source_weakening_branches_formula <->
  source_weakening_branches M r.
Proof.
  unfold source_weakening_branches_formula,source_weakening_branches.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_branches_formula_correct.
  setoid_rewrite context_included_formula_correct.
  setoid_rewrite source_context_finite_bound_formula_correct.
  setoid_rewrite source_full_branches_formula_correct. reflexivity.
Qed.

Theorem source_weakening_invariant_definable M : Definable1 M (source_weakening_invariant M).
Proof.
  exists source_weakening_invariant_formula,(fun _=>zeroM M). intro r. symmetry.
  unfold source_weakening_invariant_formula,source_weakening_invariant,source_full_row.
  repeat rewrite holds_and. rewrite trace_derives_formula_correct.
  rewrite source_weakening_sequents_formula_correct,source_weakening_branches_formula_correct.
  reflexivity.
Qed.

Lemma source_weakening_original_sequent M r b c n f :
  source_weakening_invariant M r -> source_sequent M b c n f r -> source_full_prv M b c n f.
Proof. intros [HR _] HS. exists r. auto. Qed.

Lemma source_weakening_original_branches M r b c n a d f :
  source_weakening_invariant M r -> source_branches M b c n a d f r -> source_full_branches M b c n a d f.
Proof. intros [HR _] HS. exists r. auto. Qed.

Print Assumptions source_weakening_sequents_formula_correct.
Print Assumptions source_weakening_branches_formula_correct.
Print Assumptions source_weakening_invariant_definable.
