(** Reopening a closed named binder at its original name restores the
    entire source matrix, including arbitrary internally finite syntax. *)
From PAModel Require Import Model FiniteCoding NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution
  SourceBounded SourceRenamingIdentity SourceRenamingSquare SourceShiftSpecialization
  RawBinderRenaming RawBinderInstantiation.
Unset Implicit Arguments.

Theorem raw_binder_self_instantiation M x f closed k rb rc :
  source_bounded M f k -> raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x) (succM M (zeroM M)) closed ->
  numerical_instantiation M closed x f.
Proof.
  intros HF HM HR.
  destruct (substitution_singleton_total M x) as (sb&sc&HH&_).
  assert (HI:numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (zeroM M) f).
  { apply (numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
    intros i _. apply source_empty_renaming_lookup. }
  exists sb,sc. split;[exact HH|].
  apply (numerical_source_renaming_square M f k
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    rb rc (succM M x) (succM M (zeroM M))
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    sb sc (succM M (zeroM M)) (zeroM M) f closed f HF
    (proj1 (numerical_renaming_empty_substitution M f _ _ _ f) HI) HR HI).
  intros i j l m HIbound HSub HT HClose.
  assert (EJ:j=i).
  { exact (substitution_lookup_functional M _ _ _ _ i j i HSub (source_empty_substitution_lookup M i)). }
  subst j.
  assert (EM:m=i).
  { exact (renaming_lookup_functional M _ _ _ _ i m i HT (source_empty_renaming_lookup M i)). }
  subst m.
  destruct (substitution_lookup_total M sb sc (succM M (zeroM M)) (zeroM M) l) as (out&HOut).
  assert (E:out=i).
  { destruct (raw_binder_instantiation_lookup M x x rb rc sb sc i l out HM HH HClose HOut)
      as [[-> E]|[_ E]];exact E. }
  now subst out.
Qed.

Print Assumptions raw_binder_self_instantiation.
