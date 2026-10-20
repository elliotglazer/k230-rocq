(** Closing a named free variable and then reopening it at the same name
    restores every internally coded source formula, including formulas
    containing their own de Bruijn binders. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts SourceSequents NumericalSourceFull
  NumericalRenamingMaps NumericalRenaming SourceRenamingBounds SourceRenamingIdentity
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource RenamingSubstitution
  NumericalInstantiation SourceTraceBounds SourceShiftSpecialization SourceRenamingSquare
  RawBinderRenaming.
Unset Implicit Arguments.

Theorem source_named_self_instantiation M f x rb rc body k :
  source_bounded M f k ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  numerical_instantiation M body x f.
Proof.
  intros HF HM HR.
  destruct (substitution_singleton_total M x) as (sb&sc&HS&_).
  assert (HI:numerical_renaming M f (zeroM M)(zeroM M)(zeroM M)(zeroM M) f).
  { apply (numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
    intros i _. apply source_empty_renaming_lookup. }
  exists sb,sc. split;[exact HS|].
  apply (numerical_source_renaming_square M f k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    rb rc (succM M x)(succM M (zeroM M))
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    sb sc (succM M (zeroM M))(zeroM M) f body f HF
    (proj1 (numerical_renaming_empty_substitution M f _ _ _ f) HI) HR HI).
  intros i j l m HBound HJ HId HMap.
  assert (EJ:j=i).
  { exact (substitution_lookup_functional M _ _ _ _ i j i HJ (source_empty_substitution_lookup M i)). }
  subst j.
  assert (EM:m=i).
  { exact (renaming_lookup_functional M _ _ _ _ i m i HId (source_empty_renaming_lookup M i)). }
  subst m. apply (proj1 (HM i l)) in HMap.
  destruct HMap as [[-> ->]|[_ ->]];[exact HS|apply substitution_singleton_tail].
Qed.

Theorem source_named_closure_bounded M f x rb rc body k :
  source_bounded M f k ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  source_bounded M body (succM M k).
Proof.
  intros HF HM HR.
  apply (numerical_renaming_preserves_bound M f rb rc (succM M x)
    (succM M (zeroM M)) body k (succM M k) HF HR).
  intros i j HI HJ. apply (proj1 (HM i j)) in HJ.
  destruct HJ as [[_ ->]|[_ ->]];[apply coding_zero_lt_succ|].
  exact (proj2 (coding_lt_succ_cancel M i k) HI).
Qed.

Theorem source_full_named_self_exists_intro M b c n f x rb rc body exf :
  raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  sf_relation M SFEx body (zeroM M) exf ->source_full_prv M b c n f ->
  source_full_prv M b c n exf.
Proof.
  intros HM HR HE HP.
  destruct (source_full_prv_wellformed M b c n f HP) as (k&HF&HC).
  apply (full_source_ExI M b c n body exf x f).
  - exists k. split;[|exact HC].
    apply (proj2 (source_bounded_accept_unary M SFEx body exf k (or_intror eq_refl) HE)).
    exact (source_named_closure_bounded M f x rb rc body k HF HM HR).
  - exact HP.
  - exact HE.
  - exact (source_named_self_instantiation M f x rb rc body k HF HM HR).
Qed.

Theorem source_full_named_self_all_elim M b c n f x rb rc body allf k :
  source_bounded M f k ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) body ->
  sf_relation M SFAll body (zeroM M) allf ->source_full_prv M b c n allf ->
  source_full_prv M b c n f.
Proof.
  intros HF HM HR HA HP.
  apply (full_source_AllE M b c n body allf x f);[|exact HP|exact HA|].
  - destruct (source_full_prv_wellformed M b c n allf HP) as (l&_&HC).
    exists (addM M k l). split.
    + exact (source_bounded_monotone M f k (addM M k l) HF (coding_le_add M k l)).
    + apply (context_bounded_monotone M b c n l (addM M k l) HC).
      rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact (source_named_self_instantiation M f x rb rc body k HF HM HR).
Qed.

Print Assumptions source_named_self_instantiation.
Print Assumptions source_full_named_self_exists_intro.
Print Assumptions source_full_named_self_all_elim.
