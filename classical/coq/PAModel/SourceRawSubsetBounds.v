(** Raw subset source bounds at arbitrary model-valued set names. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceRawSubset.
Unset Implicit Arguments.

Theorem source_raw_subset_bounded M x y subset k :coding_lt M x k ->coding_lt M y k ->
  source_raw_subset_graph M x y subset ->source_bounded M subset k.
Proof.
  intros HX HY (left&right&point&HL&HR&HP&HA).
  apply (proj2 (source_bounded_accept_unary M SFAll point subset k (or_introl eq_refl) HA)).
  apply (proj2 (source_bounded_accept_binary M SFImpl left right point (succM M k)
    (or_intror (or_intror eq_refl)) HP)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (succM M x) left
      (succM M k) (or_introl eq_refl) HL)).
    split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M x k) HX)].
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (succM M y) right
      (succM M k) (or_introl eq_refl) HR)).
    split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M y k) HY)].
Qed.

Print Assumptions source_raw_subset_bounded.
