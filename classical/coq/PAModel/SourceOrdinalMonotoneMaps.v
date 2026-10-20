(** Exact arbitrary-matrix normalization for the three quantified names
    in ordinal-collection monotonicity. The parameter tail is preserved. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SchemaConstructorBounds SchemaRenamingDescriptors SourceBounded NumericalRenamingMaps
  NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceSubstitutionComposition SourceRoleReopening SourceTripleSpecialization.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_oc_mono_dividend (right:bool) := if right then 16 else 9.
Definition source_oc_mono_first (right:bool) := if right then 0 else 1.
Definition source_oc_mono_matrix M right phi row :=
  numerical_renaming M phi (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 3) row.

Lemma source_oc_mono_first_lookup M right :renaming_lookup M
  (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3) (code_numeral M 2)
  (code_numeral M 3) (zeroM M) (code_numeral M (source_oc_mono_first right)).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
  destruct right;cbn [source_oc_mono_dividend source_oc_mono_first].
  - apply (descriptor_beta_certificate M 16 3 0 0 4);lia.
  - apply (descriptor_beta_certificate M 9 3 0 1 2);lia.
Qed.
Lemma source_oc_mono_second_lookup M right :renaming_lookup M
  (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3) (code_numeral M 2)
  (code_numeral M 3) (code_numeral M 1) (code_numeral M 2).
Proof.
  apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
  destruct right;cbn [source_oc_mono_dividend].
  - apply (descriptor_beta_certificate M 16 3 1 2 2);lia.
  - apply (descriptor_beta_certificate M 9 3 1 2 1);lia.
Qed.
Lemma source_oc_mono_tail_lookup M right i :renaming_lookup M
  (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3) (code_numeral M 2)
  (code_numeral M 3) (succM M (succM M i))
  (succM M (succM M (succM M (succM M (succM M i))))).
Proof.
  assert (HX:~coding_lt M (succM M (succM M i)) (code_numeral M 2)).
  { intro H. exact (coding_not_lt_zero M i (proj1 (coding_lt_succ_cancel M i (zeroM M))
      (proj1 (coding_lt_succ_cancel M (succM M i) (code_numeral M 1)) H))). }
  apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ HX)).
  change (succM M (succM M (succM M (succM M (succM M i))))=
    addM M (succM M (succM M i)) (succM M (succM M (succM M (zeroM M))))).
  now rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_oc_mono_matrix_specialization M right phi row u d v tb tc sb sc desired k :
  source_bounded M phi k ->source_oc_mono_matrix M right phi row ->source_triple_prefix M u d v tb tc ->
  source_role_reopening M v (if right then u else d) sb sc ->
  numerical_substitution M phi sb sc (code_numeral M 2) (code_numeral M 2) desired ->
  numerical_substitution M row tb tc (code_numeral M 3) (zeroM M) desired.
Proof.
  intros HB HR HTriple HRole HDesired.
  pose proof (proj1 (numerical_renaming_substitution M phi (code_numeral M (source_oc_mono_dividend right))
    (code_numeral M 3) (code_numeral M 2) (code_numeral M 3) row) HR) as HRow.
  rewrite descriptor_numeral_add in HRow.
  destruct (numerical_substitution_total M row tb tc (code_numeral M 3) (zeroM M)) as (actual&HA).
  assert (HCombined:numerical_substitution M phi sb sc (code_numeral M 2) (code_numeral M 2) actual).
  { apply (numerical_substitution_composition M phi k (code_numeral M (source_oc_mono_dividend right))
      (code_numeral M 3) (code_numeral M 2) (code_numeral M 5)
      tb tc (code_numeral M 3) (zeroM M) sb sc (code_numeral M 2) (code_numeral M 2)
      row actual HB HRow HA).
    intros i j w HI HJ HW.
    assert (HJ':renaming_lookup M (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3)
      (code_numeral M 2) (code_numeral M 3) i j).
    { apply (proj2 (renaming_substitution_lookup M _ _ _ _ i j)). now rewrite descriptor_numeral_add. }
    assert (HConvert:forall idx val,substitution_lookup M sb sc (code_numeral M 2) (zeroM M) idx val ->
      coding_lt M idx (code_numeral M 2) ->substitution_lookup M sb sc (code_numeral M 2)
        (code_numeral M 2) idx val).
    { intros idx val HL HBound. apply (proj2 (substitution_lookup_inside M sb sc _ _ _ _ HBound)).
      exact (proj1 (substitution_lookup_inside M sb sc _ _ _ _ HBound) HL). }
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
    - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ' (source_oc_mono_first_lookup M right)) as EJ.
      subst j. assert (EW:w=if right then u else d).
      { destruct right;cbn [source_oc_mono_first] in HW|-*;
          eapply substitution_lookup_functional;[exact HW|exact (proj1 HTriple)|exact HW|exact (proj1 (proj2 HTriple))]. }
      subst w. apply HConvert;[exact (proj1 HRole)|schema_small_index].
    - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ' (source_oc_mono_second_lookup M right)) as EJ.
        subst j. pose proof (substitution_lookup_functional M tb tc (code_numeral M 3) (zeroM M)
          _ w v HW (proj2 (proj2 HTriple))) as EW. subst w.
        apply HConvert;[exact (proj2 HRole)|schema_small_index].
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ' (source_oc_mono_tail_lookup M right idx')) as EJ.
        subst j. pose proof (substitution_lookup_functional M tb tc (code_numeral M 3) (zeroM M)
          _ w (succM M (succM M idx')) HW (source_triple_prefix_tail M tb tc (succM M (succM M idx')))) as EW.
        subst w. right. split.
        * intro H. exact (coding_not_lt_zero M idx' (proj1 (coding_lt_succ_cancel M idx' (zeroM M))
            (proj1 (coding_lt_succ_cancel M (succM M idx') (code_numeral M 1)) H))).
        * exists idx'. split;change (succM M (succM M idx')=addM M (succM M (succM M (zeroM M))) idx');
            now rewrite !Arithmetic.add_succ,Arithmetic.add_zero. }
  pose proof (numerical_substitution_functional M phi sb sc (code_numeral M 2) (code_numeral M 2)
    actual desired HCombined HDesired) as E. now subst actual.
Qed.

Print Assumptions source_oc_mono_matrix_specialization.
