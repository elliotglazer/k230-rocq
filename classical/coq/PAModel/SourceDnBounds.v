(** PA induction for the free-index bound of arbitrary internal Dn counts. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SourceBounded SourceDnStep SourceDn NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_dn_bound_property M count := forall body out n,
  source_dn M count body out ->
  source_bounded M body (addM M count (succM M (succM M n))) ->
  source_bounded M out (succM M (succM M n)).
Definition source_dn_bound_formula : form :=
  ∀∀∀ (source_dn_formula $3 $2 $1 →
    source_bounded_accept_formula $2 ($3 ⊕ σ (σ $0)) → source_bounded_accept_formula $1 (σ (σ $0))).
Local Opaque holds source_dn_formula source_bounded_accept_formula.
Lemma source_dn_bound_definable M : Definable1 M (source_dn_bound_property M).
Proof.
  exists source_dn_bound_formula,(fun _=>zeroM M). intro count.
  unfold source_dn_bound_formula,source_dn_bound_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_dn_formula_correct. setoid_rewrite source_bounded_accept_formula_correct.
  reflexivity.
Qed.

Theorem source_dn_bounded M count : source_dn_bound_property M count.
Proof.
  revert count. apply (definable_induction M (source_dn_bound_property M) (source_dn_bound_definable M)).
  - intros body out n HD HB. apply source_dn_zero in HD. subst out.
    rewrite coding_add_zero in HB. exact HB.
  - intros count IH body out n HD HB.
    apply source_dn_succ in HD. destruct HD as [previous [HP HS]].
    apply (source_dn_successor_bounded M previous out n);[|exact HS].
    apply (IH body previous (succM M n) HP).
    change (source_bounded M body (addM M count (succM M (succM M (succM M n))))).
    assert (E:addM M (succM M count) (succM M (succM M n)) =
      addM M count (succM M (succM M (succM M n)))).
    { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count (succM M (succM M (succM M n)))),
        Arithmetic.add_succ,(Arithmetic.add_comm M (succM M (succM M n)) count). reflexivity. }
    rewrite <-E. exact HB.
Qed.

Print Assumptions source_dn_bounded.
