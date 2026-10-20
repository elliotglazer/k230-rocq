(** An actual finite-prefix swap of source indices0 and1, together with
    its calibration as specialization after two lifted shifts. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalEnvironments
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  NumericalInstantiation SubstitutionSource RenamingSubstitution NumericalContextRenaming
  SourceBounded SourceRenamingIdentity SourceRenamingSquare SourceShiftSpecialization.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition source_swap_map M b c :=
  renaming_lookup M b c (code_numeral M 2) (zeroM M) (zeroM M) (code_numeral M 1) /\
  renaming_lookup M b c (code_numeral M 2) (zeroM M) (code_numeral M 1) (zeroM M).

Theorem source_swap_map_total M : exists b c,source_swap_map M b c.
Proof.
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) (zeroM M)) as (b1&c1&n1&H1).
  destruct (environment_cons_total M b1 c1 n1 (code_numeral M 1)) as (b&c&n&H2).
  assert (EN:n=code_numeral M 2) by (rewrite (proj1 H2),(proj1 H1);reflexivity).
  exists b,c. unfold source_swap_map. rewrite <-EN. split.
  - apply (proj2 (renaming_lookup_inside M b c n (zeroM M) (zeroM M) _
      ltac:(rewrite EN;apply coding_zero_lt_succ))).
    apply (proj1 (environment_lookup_inside M b c n (zeroM M) _
      ltac:(rewrite EN;apply coding_zero_lt_succ))).
    exact (proj2 (environment_cons_head M b1 c1 n1 _ b c n _ H2) eq_refl).
  - apply (proj2 (renaming_lookup_inside M b c n (zeroM M) (code_numeral M 1) _
      ltac:(rewrite EN;apply coding_lt_succ))).
    apply (proj1 (environment_lookup_inside M b c n (code_numeral M 1) _
      ltac:(rewrite EN;apply coding_lt_succ))).
    apply (proj2 (environment_cons_tail M b1 c1 n1 _ b c n (zeroM M) (zeroM M) H2)).
    exact (proj2 (environment_cons_head M _ _ _ _ b1 c1 n1 _ H1) eq_refl).
Qed.

Lemma source_swap_tail M b c i :
  renaming_lookup M b c (code_numeral M 2) (zeroM M) (succM M (succM M i)) (succM M (succM M i)).
Proof.
  assert (HN:~coding_lt M (succM M (succM M i)) (code_numeral M 2)).
  { intro H. apply (coding_not_lt_zero M i).
    exact (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (succM M (zeroM M))) H)). }
  apply (proj2 (renaming_lookup_outside M b c (code_numeral M 2) (zeroM M) _ _ HN)).
  symmetry. apply coding_add_zero_r.
Qed.

Theorem source_twice_lifted_shift_swap_instance M f k b c d e n p q l shifted swapped sb sc :
  source_bounded M f k ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) b c n ->
  renaming_lift M b c n (succM M (zeroM M)) d e l ->
  numerical_renaming M f d e l (succM M (zeroM M)) shifted ->
  source_swap_map M p q -> numerical_renaming M f p q (code_numeral M 2) (zeroM M) swapped ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) (zeroM M) (code_numeral M 1) ->
  numerical_substitution M shifted sb sc (succM M (zeroM M)) (zeroM M) swapped.
Proof.
  intros HF HL1 HL2 HR [HSwap0 HSwap1] HSwap HHead.
  assert (HI:numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (zeroM M) f).
  { apply (numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
    intros i _. apply source_empty_renaming_lookup. }
  apply (numerical_source_renaming_square M f k
    (zeroM M) (zeroM M) (zeroM M) (zeroM M) d e l (succM M (zeroM M))
    p q (code_numeral M 2) (zeroM M) sb sc (succM M (zeroM M)) (zeroM M)
    f shifted swapped HF (proj1 (numerical_renaming_empty_substitution M f _ _ _ f) HI) HR HSwap).
  intros i j r m HIbound HSub HSM HRI.
  assert (EJ:j=i).
  { exact (substitution_lookup_functional M _ _ _ _ i j i HSub (source_empty_substitution_lookup M i)). }
  subst j.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (renaming_lift_head M b c n _ d e l r HL2)) in HRI. subst r.
    assert (EM:m=code_numeral M 1) by (eapply renaming_lookup_functional;[exact HSM|exact HSwap0]).
    now subst m.
  - destruct (renaming_lift_tail_inv M b c n _ d e l i' r HL2 HRI) as (r'&HR'&ER).
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [E|[i'' E]];subst i'.
    + apply (proj1 (renaming_lift_head M _ _ _ _ b c n r' HL1)) in HR'. subst r' r.
      assert (EM:m=zeroM M) by (eapply renaming_lookup_functional;[exact HSM|exact HSwap1]).
      subst m. apply substitution_singleton_tail.
    + destruct (renaming_lift_tail_inv M _ _ _ _ b c n i'' r' HL1 HR') as (r''&HR''&ER').
      apply context_shift_lookup in HR''. subst r'' r' r.
      assert (EM:m=succM M (succM M i'')).
      { eapply renaming_lookup_functional;[exact HSM|apply source_swap_tail]. }
      subst m. apply substitution_singleton_tail.
Qed.

Print Assumptions source_swap_map_total.
Print Assumptions source_twice_lifted_shift_swap_instance.
