(** A larger internal free-variable bound preserves source well-formedness.
    The structural induction ranges over arbitrary PA-model formula codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs SourceBounded SetFormulaCodes SetCodeDescent.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_bound_monotone_at M f := forall k l,
  source_bounded M f k -> coding_lt M k (succM M l) -> source_bounded M f l.
Definition source_bound_monotone_formula : form :=
  ∀∀ (source_bounded_accept_formula $2 $1 → Peano.sless $1 (σ $0) →
    source_bounded_accept_formula $2 $0).

Local Opaque holds source_bounded_accept_formula Peano.sless.
Lemma source_bound_monotone_definable M : Definable1 M (source_bound_monotone_at M).
Proof.
  exists source_bound_monotone_formula,(fun _ => zeroM M). intro f.
  unfold source_bound_monotone_formula,source_bound_monotone_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite less_formula_correct. reflexivity.
Qed.

Lemma source_bound_lt_le M a k l : coding_lt M a k -> coding_lt M k (succM M l) -> coding_lt M a l.
Proof.
  intros Ha Hkl. apply (proj1 (coding_lt_succ_cases M k l)) in Hkl.
  destruct Hkl as [Hkl | E].
  - exact (coding_lt_trans M a k l Ha Hkl).
  - now subst l.
Qed.

Theorem source_bounded_monotone M f : source_bound_monotone_at M f.
Proof.
  revert f. apply (sf_code_induction M (source_bound_monotone_at M)).
  - apply source_bound_monotone_definable.
  - intros k l _ _. apply source_bounded_accept_falsity.
  - intros f Hbad k l Hf _. exfalso. exact (source_bounded_reject_invalid M f k Hbad Hf).
  - intros a b f Hf k l Hb Hkl.
    apply (proj2 (source_bounded_accept_atom M SFMember a b f l (or_introl eq_refl) Hf)).
    apply (proj1 (source_bounded_accept_atom M SFMember a b f k (or_introl eq_refl) Hf)) in Hb.
    destruct Hb as [Ha Hb]. split; eapply source_bound_lt_le; eassumption.
  - intros a b f Hf k l Hb Hkl.
    apply (proj2 (source_bounded_accept_atom M SFEqual a b f l (or_intror eq_refl) Hf)).
    apply (proj1 (source_bounded_accept_atom M SFEqual a b f k (or_intror eq_refl) Hf)) in Hb.
    destruct Hb as [Ha Hb]. split; eapply source_bound_lt_le; eassumption.
  - intros h a b f Hh Hf IHa IHb k l Hb Hkl.
    apply (proj1 (source_bounded_accept_binary M h a b f k Hh Hf)) in Hb.
    apply (proj2 (source_bounded_accept_binary M h a b f l Hh Hf)).
    destruct Hb as [Ha Hb]. split; [exact (IHa k l Ha Hkl)|exact (IHb k l Hb Hkl)].
  - intros h a f Hh Hf IH k l Hb Hkl.
    apply (proj2 (source_bounded_accept_unary M h a f l Hh Hf)).
    apply (IH (succM M k) (succM M l)).
    + exact (proj1 (source_bounded_accept_unary M h a f k Hh Hf) Hb).
    + exact (proj2 (coding_lt_succ_cancel M k (succM M l)) Hkl).
Qed.

Print Assumptions source_bound_monotone_definable.
Print Assumptions source_bounded_monotone.
