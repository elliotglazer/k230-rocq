(** Every image of the raw syntax is a well-formed source formula.
    Bounds and syntax codes are arbitrary elements of the PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions CodeDescent NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded
  SourceBoundMonotone SourceRenamingBounds NumericalRenaming
  RawBinderRenaming RawSourceImage RawSourceImageInversion.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma raw_binder_maps_bound M x b c k : raw_binder_renaming M x b c ->
  renaming_maps_bound M b c (succM M x) (succM M (zeroM M)) k (succM M k).
Proof.
  intros H i j Hi Hj. apply (proj1 (H i j)) in Hj.
  destruct Hj as [[_ ->]|[_ ->]].
  - apply coding_zero_lt_succ.
  - exact (proj2 (coding_lt_succ_cancel M i k) Hi).
Qed.

Definition raw_source_bounded_property M f :=
  forall s,raw_source_image M f s -> exists k,source_bounded M s k.
Definition raw_source_bounded_property_formula : form :=
  ∀ (raw_source_image_formula $1 $0 → ∃ source_bounded_accept_formula $1 $0).
Local Opaque holds raw_source_image_formula source_bounded_accept_formula.
Lemma raw_source_bounded_property_definable M :
  Definable1 M (raw_source_bounded_property M).
Proof.
  exists raw_source_bounded_property_formula,(fun _=>zeroM M). intro f.
  unfold raw_source_bounded_property_formula,raw_source_bounded_property.
  setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite holds_ex.
  setoid_rewrite raw_source_image_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.

Theorem raw_source_image_bounded M f : raw_source_bounded_property M f.
Proof.
  revert f. apply (named_formula_code_induction M (raw_source_bounded_property M)).
  - apply raw_source_bounded_property_definable.
  - intros s HS. exists (zeroM M).
    apply (proj2 (source_bounded_accept_binary M SFImpl (zeroM M) (zeroM M) s
      (zeroM M) ltac:(unfold sf_binary;auto) (raw_source_zero_inv M s HS))).
    split;apply source_bounded_accept_falsity.
  - intros a b f HF s HS. exists (succM M (addM M a b)).
    apply (proj2 (source_bounded_accept_atom M SFMember a b s _ (or_introl eq_refl)
      (raw_source_member_inv M a b f s HF HS))).
    split;[apply coding_le_add|rewrite (add_comm M a b);apply coding_le_add].
  - intros a b f HF s HS. exists (succM M (addM M a b)).
    apply (proj2 (source_bounded_accept_atom M SFEqual a b s _ (or_intror eq_refl)
      (raw_source_equal_inv M a b f s HF HS))).
    split;[apply coding_le_add|rewrite (add_comm M a b);apply coding_le_add].
  - intros a b f HN HF IHa IHb s HS.
    destruct (raw_source_implication_inv M a b f s HN HF HS) as (u&v&HU&HV&HUV).
    destruct (IHa u HU) as [k Hk],(IHb v HV) as [l Hl].
    exists (addM M k l).
    apply (proj2 (source_bounded_accept_binary M SFImpl u v s _
      ltac:(unfold sf_binary;auto) HUV)). split.
    + exact (source_bounded_monotone M u k (addM M k l) Hk (coding_le_add M k l)).
    + apply (source_bounded_monotone M v l (addM M k l) Hl).
      rewrite (add_comm M k l). apply coding_le_add.
  - intros x g f HF IH s HS.
    destruct (raw_source_universal_inv M x g f s HF HS) as (u&b&c&v&HU&HB&HR&HV).
    destruct (IH u HU) as [k Hk]. exists k.
    apply (proj2 (source_bounded_accept_unary M SFAll v s k (or_introl eq_refl) HV)).
    exact (numerical_renaming_preserves_bound M u b c (succM M x)
      (succM M (zeroM M)) v k (succM M k) Hk HR (raw_binder_maps_bound M x b c k HB)).
Qed.

Print Assumptions raw_binder_maps_bound.
Print Assumptions raw_source_image_bounded.
