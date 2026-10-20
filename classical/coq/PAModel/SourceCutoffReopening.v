(** An inserted role-preserving parameter followed by reopening is the
    original predicate under the same prefix and one-higher parameter tail. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded SourceFiniteCutoffShift SourceTraceMatrixAlignment SourceTraceValueAlignment
  SourceSubstitutionComposition NumericalSubstitutionMaps NumericalSubstitution
  NumericalRenaming RenamingSubstitution SchemaRenamingDescriptors SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_two_reopening M phi phi' rb rc value k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  numerical_substitution M phi' rb rc (code_numeral M 2)(code_numeral M 2) value ->
  numerical_renaming M phi rb rc (code_numeral M 2)(code_numeral M 1) value.
Proof.
  intros HP (b&c&n&HM&HS) HV.
  apply (proj2 (numerical_renaming_substitution M phi rb rc (code_numeral M 2)(code_numeral M 1) value)).
  rewrite descriptor_numeral_add.
  apply (numerical_substitution_composition M phi k b c n (code_numeral M 3)
    rb rc (code_numeral M 2)(code_numeral M 2)
    rb rc (code_numeral M 2)(code_numeral M 3) phi' value HP HS HV).
  intros i j v _ HI HJ.
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (substitution_lookup_functional M b c n (code_numeral M 3)(zeroM M) j
      (zeroM M) HI (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 0)) as E. subst j.
    apply (proj2 (substitution_lookup_inside M rb rc (code_numeral M 2)(code_numeral M 3)
      (zeroM M) v (coding_zero_lt_succ M (code_numeral M 1)))).
    exact (proj1 (substitution_lookup_inside M rb rc (code_numeral M 2)(code_numeral M 2)
      (zeroM M) v (coding_zero_lt_succ M (code_numeral M 1))) HJ).
  - destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (substitution_lookup_functional M b c n (code_numeral M 3)(code_numeral M 1) j
        (code_numeral M 1) HI (source_cutoff_shift_map_fixed_lookup M 2 b c n HM 1)) as E. subst j.
      apply (proj2 (substitution_lookup_inside M rb rc (code_numeral M 2)(code_numeral M 3)
        (code_numeral M 1) v (coding_lt_succ M (code_numeral M 1)))).
      exact (proj1 (substitution_lookup_inside M rb rc (code_numeral M 2)(code_numeral M 2)
        (code_numeral M 1) v (coding_lt_succ M (code_numeral M 1))) HJ).
    + pose proof (substitution_lookup_functional M b c n (code_numeral M 3) _ j
        (succM M (succM M (succM M i''))) HI (source_cutoff_shift_map_tail M 2 b c n i'' HM)) as E. subst j.
      assert (HIdentity:substitution_lookup M rb rc (code_numeral M 2)(code_numeral M 2)
        (succM M (succM M (succM M i'')))(succM M (succM M (succM M i'')))).
      { apply (proj2 (substitution_lookup_outside M rb rc (code_numeral M 2)(code_numeral M 2)
          _ _ (source_two_succ_not_lt_two M (succM M i'')))).
        exists (succM M i''). split;cbn [code_numeral];now rewrite !Arithmetic.add_succ,Arithmetic.add_zero. }
      pose proof (substitution_lookup_functional M _ _ _ _ _ v _ HJ HIdentity) as E. subst v.
      apply (proj2 (substitution_lookup_outside M rb rc (code_numeral M 2)(code_numeral M 3)
        _ _ (source_two_succ_not_lt_two M i''))).
      exists i''. split;cbn [code_numeral];now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Print Assumptions source_cutoff_two_reopening.
