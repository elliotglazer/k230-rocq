(** Binding the decoded matrix's private code-name is vacuous. The
    resulting source matrix is exactly the ordinary de Bruijn shift. *)
From PAModel Require Import Model FiniteCoding FiniteCRT NumericalRenamingMaps NumericalRenaming
  NumericalContextRenaming SourceBounded SourceRenamingIdentity SourceRenamingDiamond
  SourceShiftSpecialization SourceQuantifierRules RawBinderRenaming RawSourceImage RawSourcePrivateBound.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem raw_binder_above_bound_is_shift M f private bound rb rc closed :
  source_bounded M f bound ->coding_lt M bound (succM M private) ->
  raw_binder_renaming M private rb rc ->
  numerical_renaming M f rb rc (succM M private) (succM M (zeroM M)) closed ->
  source_formula_shift M f closed.
Proof.
  intros HF HB HM HR.
  assert (HI:numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (zeroM M) f).
  { apply (numerical_renaming_identity_on_bound M f _ _ _ _ bound HF).
    intros i _. apply source_empty_renaming_lookup. }
  apply (numerical_source_renaming_diamond M f bound
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    rb rc (succM M private) (succM M (zeroM M))
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) f f closed HF HI HI HR).
  intros i j l m HIB HJ HJM HL.
  assert (EJ:j=i).
  { exact (renaming_lookup_functional M _ _ _ _ i j i HJ (source_empty_renaming_lookup M i)). }
  assert (EL:l=i).
  { exact (renaming_lookup_functional M _ _ _ _ i l i HL (source_empty_renaming_lookup M i)). }
  subst j l. apply (proj1 (HM i m)) in HJM. destruct HJM as [[E _]|[_ ->]].
  - subst i. exfalso.
    apply (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) private private);[|reflexivity].
    apply (proj1 (coding_lt_succ_cases M bound private)) in HB. destruct HB as [HB| ->].
    + exact (coding_lt_trans M private bound private HIB HB).
    + exact HIB.
  - apply (proj2 (context_shift_lookup M i (succM M i))). reflexivity.
Qed.

Corollary raw_source_private_binder_shift M raw source rb rc closed :
  raw_source_image M raw source ->raw_binder_renaming M raw rb rc ->
  numerical_renaming M source rb rc (succM M raw) (succM M (zeroM M)) closed ->
  source_formula_shift M source closed.
Proof.
  intros HS HM HR. exact (raw_binder_above_bound_is_shift M source raw raw rb rc closed
    (raw_source_image_private_bound M raw source HS) (coding_lt_succ M raw) HM HR).
Qed.

Print Assumptions raw_binder_above_bound_is_shift.
Print Assumptions raw_source_private_binder_shift.
