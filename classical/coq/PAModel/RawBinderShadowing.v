(** A named universal has no free occurrence of its own binder.  On its
    actual source image, closing that name again is exactly ordinary shift.
    This accounts for repeated named binders without a freshness premise. *)
From PAModel Require Import Model FiniteCoding NumericalRenamingMaps NumericalRenaming
  NumericalContextRenaming SourceQuantifierRules SetFormulaCodes SourceBounded RawBinderRenaming SourceRenamingDiamond.
Unset Implicit Arguments.

Theorem raw_binder_quantified_shadowing M x f closed quantified out k rb rc qb qc :
  source_bounded M f k -> raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x) (succM M (zeroM M)) closed ->
  sf_relation M SFAll closed (zeroM M) quantified ->
  raw_binder_renaming M x qb qc ->
  numerical_renaming M quantified qb qc (succM M x) (succM M (zeroM M)) out ->
  source_formula_shift M quantified out.
Proof.
  intros HF HM HR HQ HM' HOut.
  apply (proj1 (numerical_renaming_quantifier M true closed quantified qb qc
    (succM M x) (succM M (zeroM M)) out HQ)) in HOut.
  destruct HOut as (ub&uc&un&matrix&HL&HMatrix&HSOut).
  destruct (renaming_lift_total M (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as (tb&tc&tn&HT).
  apply (proj2 (numerical_renaming_quantifier M true closed quantified (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) out HQ)).
  exists tb,tc,tn,matrix. split;[exact HT|]. split;[|exact HSOut].
  apply (numerical_source_renaming_diamond M f k
    rb rc (succM M x) (succM M (zeroM M))
    rb rc (succM M x) (succM M (zeroM M))
    ub uc un (succM M (zeroM M)) tb tc tn (succM M (zeroM M))
    closed closed matrix HF HR HR HMatrix).
  intros i j l m HI HJ HJM HL'.
  assert (EL:l=j).
  { exact (renaming_lookup_functional M rb rc (succM M x) (succM M (zeroM M)) i l j HL' HJ). }
  subst l. apply (proj1 (HM i j)) in HJ.
  destruct HJ as [[-> ->]|[HIX ->]].
  - apply (proj1 (renaming_lift_head M qb qc (succM M x) (succM M (zeroM M))
      ub uc un m HL)) in HJM. subst m.
    exact (proj2 (renaming_lift_head M _ _ _ _ tb tc tn (zeroM M) HT) eq_refl).
  - destruct (renaming_lift_tail_inv M qb qc (succM M x) (succM M (zeroM M))
      ub uc un i m HL HJM) as (v&HV&EM).
    assert (EV:v=succM M i).
    { apply (proj1 (HM' i v)) in HV. destruct HV as [[E _]|[_ E]];[contradiction|exact E]. }
    subst v m. apply (proj2 (renaming_lift_tail M _ _ _ _ tb tc tn i (succM M i) HT)).
    apply (proj2 (context_shift_lookup M i (succM M i))). reflexivity.
Qed.

Print Assumptions raw_binder_quantified_shadowing.
