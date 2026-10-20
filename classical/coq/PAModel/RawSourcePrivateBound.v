(** The decoded matrix's own raw code is a private name. This is the
    internal-code counterpart of KDecodeFresh.D_private_fresh: every free
    source index of the genuine image lies strictly below the raw code. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent
  NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded SourceBoundMonotone
  SourceRenamingBounds NumericalRenaming RawBinderRenaming RawSourceImage RawSourceImageInversion
  RawSourceImageBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition raw_source_private_bound_at M raw :=forall source,
  raw_source_image M raw source ->source_bounded M source raw.
Definition raw_source_private_bound_formula :form :=
  ∀(raw_source_image_formula $1 $0 →source_bounded_accept_formula $0 $1).
Local Opaque holds raw_source_image_formula source_bounded_accept_formula.

Lemma raw_source_private_bound_definable M :Definable1 M (raw_source_private_bound_at M).
Proof.
  exists raw_source_private_bound_formula,(fun _=>zeroM M). intro raw.
  unfold raw_source_private_bound_at,raw_source_private_bound_formula.
  rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite raw_source_image_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.

Theorem raw_source_image_private_bound M raw :raw_source_private_bound_at M raw.
Proof.
  revert raw. apply (named_formula_code_induction M (raw_source_private_bound_at M)).
  - apply raw_source_private_bound_definable.
  - intros source HS.
    apply (proj2 (source_bounded_accept_binary M SFImpl (zeroM M) (zeroM M) source (zeroM M)
      ltac:(unfold sf_binary;auto) (raw_source_zero_inv M source HS))).
    split;apply source_bounded_accept_falsity.
  - intros a b raw HR source HS.
    apply (proj2 (source_bounded_accept_atom M SFMember a b source raw (or_introl eq_refl)
      (raw_source_member_inv M a b raw source HR HS))).
    exact (tagged_pair_positive_descent M a b raw 1 ltac:(discriminate) HR).
  - intros a b raw HR source HS.
    apply (proj2 (source_bounded_accept_atom M SFEqual a b source raw (or_intror eq_refl)
      (raw_source_equal_inv M a b raw source HR HS))).
    exact (tagged_pair_positive_descent M a b raw 3 ltac:(discriminate) HR).
  - intros a b raw HNZ HR IHa IHb source HS.
    destruct (raw_source_implication_inv M a b raw source HNZ HR HS) as (sa&sb&HSA&HSB&HImpl).
    destruct (tagged_pair_zero_descent M a b raw HNZ (proj1 (implication_graph_tagged M a b raw) HR))
      as [HA HB].
    apply (proj2 (source_bounded_accept_binary M SFImpl sa sb source raw ltac:(unfold sf_binary;auto) HImpl)).
    split.
    + apply (source_bounded_monotone M sa a raw (IHa sa HSA)).
      exact (coding_lt_trans M a raw (succM M raw) HA (coding_lt_succ M raw)).
    + apply (source_bounded_monotone M sb b raw (IHb sb HSB)).
      exact (coding_lt_trans M b raw (succM M raw) HB (coding_lt_succ M raw)).
  - intros x body raw HR IH source HS.
    destruct (raw_source_universal_inv M x body raw source HR HS)
      as (matrix&rb&rc&closed&HM&HMap&HRename&HAll).
    pose proof (proj2 (tagged_pair_positive_descent M x body raw 2 ltac:(discriminate)
      (proj1 (universal_graph_tagged M x body raw) HR))) as HBodyRaw.
    apply (source_bounded_monotone M source body raw).
    + apply (proj2 (source_bounded_accept_unary M SFAll closed source body (or_introl eq_refl) HAll)).
      exact (numerical_renaming_preserves_bound M matrix rb rc (succM M x) (succM M (zeroM M)) closed
        body (succM M body) (IH matrix HM) HRename (raw_binder_maps_bound M x rb rc body HMap)).
    + exact (coding_lt_trans M body raw (succM M raw) HBodyRaw (coding_lt_succ M raw)).
Qed.

Print Assumptions raw_source_image_private_bound.
