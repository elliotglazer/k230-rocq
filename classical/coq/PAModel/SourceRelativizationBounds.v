(** A domain with only variable zero preserves every source free-index
    bound under the actual internal relativization computation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma sr_domain_bound_succ M d k :
  source_bounded M d (code_numeral M 1) -> source_bounded M d (succM M k).
Proof.
  intro HD. apply (source_bounded_monotone M d (code_numeral M 1) (succM M k) HD).
  change (coding_lt M (succM M (zeroM M)) (succM M (succM M k))).
  apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M k))).
  apply coding_zero_lt_succ.
Qed.

Lemma sr_quantifier_preserves_bound M universal d w v k :
  source_bounded M d (code_numeral M 1) -> source_bounded M w (succM M k) ->
  sr_quantifier M universal d w v -> source_bounded M v k.
Proof.
  intros HD HW [mid [HM HV]]. destruct universal.
  - apply (proj2 (source_bounded_accept_unary M SFAll mid v k (or_introl eq_refl) HV)).
    apply (proj2 (source_bounded_accept_binary M SFImpl d w mid (succM M k)
      (or_intror (or_intror eq_refl)) HM)).
    split;[now apply sr_domain_bound_succ|exact HW].
  - apply (proj2 (source_bounded_accept_unary M SFEx mid v k (or_intror eq_refl) HV)).
    apply (proj2 (source_bounded_accept_binary M SFAnd d w mid (succM M k)
      (or_introl eq_refl) HM)).
    split;[now apply sr_domain_bound_succ|exact HW].
Qed.

Definition sr_bounded_at M f := forall d k v,
  source_bounded M d (code_numeral M 1) -> source_bounded M f k ->
  source_relativization M d f v -> source_bounded M v k.
Definition sr_bound_formula : form :=
  ∀∀∀ (source_bounded_accept_formula $2 (num 1) →
    source_bounded_accept_formula $3 $1 → source_relativization_formula $2 $3 $0 →
    source_bounded_accept_formula $0 $1).
Local Opaque holds source_bounded_accept_formula source_relativization_formula.
Lemma sr_bounded_at_definable M : Definable1 M (sr_bounded_at M).
Proof.
  exists sr_bound_formula,(fun _=>zeroM M). intro f.
  unfold sr_bound_formula,sr_bounded_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite source_relativization_formula_correct. reflexivity.
Qed.

Theorem source_relativization_preserves_bound M f : sr_bounded_at M f.
Proof.
  revert f. apply (sf_code_induction M (sr_bounded_at M)).
  - apply sr_bounded_at_definable.
  - intros d k v HD HF HR.
    rewrite (source_relativization_invalid_inv M d (zeroM M) v (or_introl eq_refl) HR).
    apply source_bounded_accept_falsity.
  - intros f Hbad d k v HD HF HR. exfalso. exact (source_bounded_reject_invalid M f k Hbad HF).
  - intros a b f Hshape d k v HD HF HR.
    rewrite (source_relativization_atom_inv M d false a b f v Hshape HR). exact HF.
  - intros a b f Hshape d k v HD HF HR.
    rewrite (source_relativization_atom_inv M d true a b f v Hshape HR). exact HF.
  - intros h a b f Hh Hshape IHa IHb d k v HD HF HR.
    destruct (proj1 (source_bounded_accept_binary M h a b f k Hh Hshape) HF) as [HA HB].
    destruct (source_relativization_binary_inv M d h a b f v Hh Hshape HR)
      as [x [y [HX [HY HOut]]]].
    apply (proj2 (source_bounded_accept_binary M h x y v k Hh HOut)).
    split;[exact (IHa d k x HD HA HX)|exact (IHb d k y HD HB HY)].
  - intros h a f Hh Hshape IH d k v HD HF HR.
    pose proof (proj1 (source_bounded_accept_unary M h a f k Hh Hshape) HF) as HA.
    destruct Hh as [Hh|Hh];subst h.
    + destruct (source_relativization_quantifier_inv M d true a f v Hshape HR) as [w [HW HOut]].
      exact (sr_quantifier_preserves_bound M true d w v k HD (IH d (succM M k) w HD HA HW) HOut).
    + destruct (source_relativization_quantifier_inv M d false a f v Hshape HR) as [w [HW HOut]].
      exact (sr_quantifier_preserves_bound M false d w v k HD (IH d (succM M k) w HD HA HW) HOut).
Qed.

Print Assumptions sr_quantifier_preserves_bound.
Print Assumptions source_relativization_preserves_bound.
