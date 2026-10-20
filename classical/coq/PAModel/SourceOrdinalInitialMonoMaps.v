(** The initial monotonicity context has one fewer carrier parameter. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceOrdinalMonotoneMaps
  SourceSubstitutionComposition SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition source_oc_initial_mono_matrix M right phi row :=
  numerical_renaming M phi(code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)
    (code_numeral M 2)(code_numeral M 2) row.

Lemma source_oc_initial_mono_first M right :renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 2)
  (zeroM M)(code_numeral M(source_oc_mono_first right)).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_zero_lt_succ M(code_numeral M 1)))).
  exact(proj1(renaming_lookup_inside M _ _ _ _ _ _(coding_zero_lt_succ M(code_numeral M 1)))
    (source_oc_mono_first_lookup M right)).
Qed.
Lemma source_oc_initial_mono_second M right :renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 2)
  (code_numeral M 1)(code_numeral M 2).
Proof.
  apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_lt_succ M(code_numeral M 1)))).
  exact(proj1(renaming_lookup_inside M _ _ _ _ _ _(coding_lt_succ M(code_numeral M 1)))
    (source_oc_mono_second_lookup M right)).
Qed.
Lemma source_oc_initial_mono_tail M right i :renaming_lookup M
  (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 2)
  (succM M(succM M i))(succM M(succM M(succM M(succM M i)))).
Proof.
  assert(HX:~coding_lt M(succM M(succM M i))(code_numeral M 2)).
  { intro H. exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))
      (proj1(coding_lt_succ_cancel M(succM M i)(code_numeral M 1)) H))). }
  apply(proj2(renaming_lookup_outside M _ _ _ _ _ _ HX)).
  change(succM M(succM M(succM M(succM M i)))=addM M(succM M(succM M i))(code_numeral M 2)).
  cbn[code_numeral]. now rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_oc_initial_mono_matrix_shift M right phi row row' k :
  source_bounded M phi k ->source_oc_initial_mono_matrix M right phi row ->
  source_cutoff_shift M 3 row row' ->source_oc_mono_matrix M right phi row'.
Proof.
  intros HB HR (b&c&n&HM&HS).
  pose proof(proj1(numerical_renaming_substitution M phi _ _ _ (code_numeral M 2) row) HR) as HRow.
  rewrite descriptor_numeral_add in HRow.
  apply(proj2(numerical_renaming_substitution M phi _ _ _ (code_numeral M 3) row')).
  rewrite descriptor_numeral_add.
  apply(numerical_substitution_composition M phi k
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 4)
    b c n(code_numeral M 4)
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 5)
    row row' HB HRow HS).
  intros i j v HI HFirst HSecond.
  pose proof(renaming_substitution_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 2) i j) as HC.
  rewrite descriptor_numeral_add in HC. apply(proj2 HC) in HFirst.
  pose proof(renaming_substitution_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 3) i v) as HC'.
  rewrite descriptor_numeral_add in HC'. apply(proj1 HC').
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i)
    as [E|[idx E]];subst i.
  - pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HFirst(source_oc_initial_mono_first M right)) as E. subst j.
    assert(HFix:substitution_lookup M b c n(code_numeral M 4)
      (code_numeral M(source_oc_mono_first right))(code_numeral M(source_oc_mono_first right))).
    { destruct right;[exact(source_cutoff_shift_map_fixed_lookup M 3 b c n HM 0)|
        exact(source_cutoff_shift_map_fixed_lookup M 3 b c n HM 1)]. }
    pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond HFix) as E. subst v.
    exact(source_oc_mono_first_lookup M right).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) idx)
      as [E|[tail E]];subst idx.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HFirst(source_oc_initial_mono_second M right)) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond
        (source_cutoff_shift_map_fixed_lookup M 3 b c n HM 2)) as E. subst v.
      exact(source_oc_mono_second_lookup M right).
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HFirst(source_oc_initial_mono_tail M right tail)) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond
        (source_cutoff_shift_map_tail_lookup M 3 b c n(succM M tail) HM)) as E. subst v.
      exact(source_oc_mono_tail_lookup M right tail).
Qed.

Print Assumptions source_oc_initial_mono_matrix_shift.
