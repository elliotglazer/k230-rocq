(** The moving carrier adds no names beyond the supplied bound, provided
    the carrier itself is below that bound. This includes every nested
    quantifier, whose matrix and carrier bounds both rise by one. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent SourceBounded SourceRelativizationRules SourceRelativization
  SourceSetRelativizationRules SourceSetRelativization SourceSetRelativizationFunctionality.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma ssr_quantifier_preserves_bound M universal name w v k :
  coding_lt M name k ->source_bounded M w (succM M k) ->
  ssr_quantifier M universal name w v ->source_bounded M v k.
Proof.
  intros HName HW(guard&mid&HG&HM&HV).
  assert(HGuard:source_bounded M guard (succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember (zeroM M)(succM M name) guard
      (succM M k)(or_introl eq_refl) HG)).
    split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M name k) HName)]. }
  destruct universal.
  - apply(proj2(source_bounded_accept_unary M SFAll mid v k (or_introl eq_refl) HV)).
    apply(proj2(source_bounded_accept_binary M SFImpl guard w mid (succM M k)
      (or_intror(or_intror eq_refl)) HM)). split;assumption.
  - apply(proj2(source_bounded_accept_unary M SFEx mid v k (or_intror eq_refl) HV)).
    apply(proj2(source_bounded_accept_binary M SFAnd guard w mid (succM M k)
      (or_introl eq_refl) HM)). split;assumption.
Qed.

Definition ssr_bounded_at M f :=forall name k v,coding_lt M name k ->
  source_bounded M f k ->source_set_relativization M name f v ->source_bounded M v k.
Definition ssr_bound_formula :form :=
  ∀∀∀(Peano.sless $2 $1 →source_bounded_accept_formula $3 $1 →
    source_set_relativization_formula $2 $3 $0 →source_bounded_accept_formula $0 $1).
Local Opaque holds source_bounded_accept_formula source_set_relativization_formula.
Lemma ssr_bounded_at_definable M :Definable1 M (ssr_bounded_at M).
Proof.
  exists ssr_bound_formula,(fun _=>zeroM M). intro f.
  unfold ssr_bound_formula,ssr_bounded_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite source_set_relativization_formula_correct. reflexivity.
Qed.

Theorem source_set_relativization_preserves_bound M f :ssr_bounded_at M f.
Proof.
  revert f. apply(sf_code_induction M (ssr_bounded_at M)).
  - apply ssr_bounded_at_definable.
  - intros name k v HName HF HR.
    rewrite(source_set_relativization_invalid_inv M name (zeroM M) v (or_introl eq_refl) HR).
    apply source_bounded_accept_falsity.
  - intros f HBad name k v HName HF HR.
    exfalso. exact(source_bounded_reject_invalid M f k HBad HF).
  - intros a b f HShape name k v HName HF HR.
    rewrite(source_set_relativization_atom_inv M name false a b f v HShape HR). exact HF.
  - intros a b f HShape name k v HName HF HR.
    rewrite(source_set_relativization_atom_inv M name true a b f v HShape HR). exact HF.
  - intros h a b f Hh HShape IHa IHb name k v HName HF HR.
    destruct(proj1(source_bounded_accept_binary M h a b f k Hh HShape) HF) as[HA HB].
    destruct(source_set_relativization_binary_inv M name h a b f v Hh HShape HR)
      as(x&y&HX&HY&HOut).
    apply(proj2(source_bounded_accept_binary M h x y v k Hh HOut)).
    split;[exact(IHa name k x HName HA HX)|exact(IHb name k y HName HB HY)].
  - intros h a f Hh HShape IH name k v HName HF HR.
    pose proof(proj1(source_bounded_accept_unary M h a f k Hh HShape) HF) as HA.
    pose proof(proj2(coding_lt_succ_cancel M name k) HName) as HName'.
    destruct Hh as[Hh|Hh];subst h.
    + destruct(source_set_relativization_quantifier_inv M name true a f v HShape HR) as(w&HW&HOut).
      exact(ssr_quantifier_preserves_bound M true name w v k HName
        (IH (succM M name)(succM M k) w HName' HA HW) HOut).
    + destruct(source_set_relativization_quantifier_inv M name false a f v HShape HR) as(w&HW&HOut).
      exact(ssr_quantifier_preserves_bound M false name w v k HName
        (IH (succM M name)(succM M k) w HName' HA HW) HOut).
Qed.

Print Assumptions ssr_quantifier_preserves_bound.
Print Assumptions source_set_relativization_preserves_bound.
