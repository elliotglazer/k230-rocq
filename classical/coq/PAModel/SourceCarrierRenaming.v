(** The exact low-index action needed to move the bounding carrier away
    from the distinguished output role. These are numerical map premises. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded SourceRenamingIdentity SourceRenamingWellformedness SourceRenamingBounds
  SourceRenamingDiamond SourceNativeKShifts SourceShiftSpecialization NumericalRenamingMaps
  NumericalRenaming NumericalContextRenaming SourceQuantifierRules SourceRoleReopening
  SourceTraceValueAlignment SourceTraceMatrixAlignment RenamingSubstitution NumericalSubstitutionMaps.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition carrier_positive_fixes M fresh b c n :=forall i,
  i<>zeroM M ->coding_lt M i fresh ->renaming_lookup M b c n (zeroM M) i i.

Theorem source_valid_identity M f k :source_bounded M f k ->
  numerical_renaming M f (zeroM M)(zeroM M)(zeroM M)(zeroM M) f.
Proof.
  intro HF. apply (numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
  intros i _. apply source_empty_renaming_lookup.
Qed.

Theorem source_native_upshift_carrier_fixed M f g k fresh b c n u v l :
  source_bounded M f k ->coding_lt M k fresh ->source_native_k_upshift M f g ->
  carrier_positive_fixes M fresh b c n ->
  renaming_lift M b c n (zeroM M) u v l ->
  numerical_renaming M g u v l (zeroM M) g.
Proof.
  intros HF HK HG HFix HL.
  destruct (source_renaming_range_bound M (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1) k)
    as [kg HRange].
  pose proof (numerical_renaming_preserves_bound M f _ _ _ _ g k kg HF HG HRange) as HGB.
  apply (numerical_source_renaming_diamond M f k
    (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)
    (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) u v l (zeroM M) g g g
    HF HG HG (source_valid_identity M g kg HGB)).
  intros i j p q HI HJ HQ HP.
  pose proof (renaming_lookup_functional M _ _ _ _ _ j p HJ HP) as E. subst p.
  pose proof (renaming_lookup_functional M _ _ _ _ _ q j HQ (source_empty_renaming_lookup M j)) as E. subst q.
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j (zeroM M) HJ (source_native_k_upshift_zero M)) as E.
    subst j. exact (proj2 (renaming_lift_head M b c n (zeroM M) u v l (zeroM M) HL) eq_refl).
  - assert (HJ':renaming_lookup M (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)
        (succM M i')(succM M (succM M i'))).
    { apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _
        ltac:(intro H;exact (coding_not_lt_zero M i' (proj1 (coding_lt_succ_cancel M i' (zeroM M)) H))))).
      cbn [code_numeral]. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. }
    pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ HJ') as E. subst j.
    apply (proj2 (renaming_lift_tail M b c n (zeroM M) u v l (succM M i')(succM M i') HL)).
    apply HFix.
    + intro E. pose proof (coding_zero_lt_succ M i') as H. rewrite E in H. exact (coding_not_lt_zero M (zeroM M) H).
    + exact (coding_lt_trans M _ k fresh HI HK).
Qed.

Theorem source_reopened_carrier_to_shift M phi value shifted k fresh ab ac b c n u v l :
  source_bounded M phi k ->coding_lt M k fresh ->
  source_role_reopening M (code_numeral M 2)(succM M fresh) ab ac ->
  numerical_renaming M phi ab ac (code_numeral M 2)(code_numeral M 1) value ->
  source_formula_shift M phi shifted ->
  renaming_lookup M b c n (zeroM M) fresh (zeroM M) ->
  carrier_positive_fixes M fresh b c n ->renaming_lift M b c n (zeroM M) u v l ->
  numerical_renaming M value u v l (zeroM M) shifted.
Proof.
  intros HF HK HMap HV HS HFresh HFix HL.
  destruct (source_renaming_range_bound M (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1) k)
    as [ks HRange].
  pose proof (numerical_renaming_preserves_bound M phi _ _ _ _ shifted k ks HF HS HRange) as HSB.
  apply (numerical_source_renaming_diamond M phi k
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    ab ac (code_numeral M 2)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) u v l (zeroM M) shifted value shifted
    HF HS HV (source_valid_identity M shifted ks HSB)).
  intros i j p q HI HJ HQ HP.
  apply context_shift_lookup in HJ. subst j.
  pose proof (renaming_lookup_functional M _ _ _ _ _ q (succM M i) HQ
    (source_empty_renaming_lookup M (succM M i))) as E. subst q.
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - assert (HFirst:renaming_lookup M ab ac (code_numeral M 2)(code_numeral M 1)
        (zeroM M)(succM M fresh)).
    { apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
      exact (proj1 (substitution_lookup_inside M ab ac (code_numeral M 2)(zeroM M)
        (zeroM M)(succM M fresh)(coding_zero_lt_succ M (code_numeral M 1))) (proj1 HMap)). }
    pose proof (renaming_lookup_functional M _ _ _ _ _ p _ HP HFirst) as E. subst p.
    exact (proj2 (renaming_lift_tail M b c n (zeroM M) u v l fresh (zeroM M) HL) HFresh).
  - destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + assert (HSecond:renaming_lookup M ab ac (code_numeral M 2)(code_numeral M 1)
          (code_numeral M 1)(code_numeral M 2)).
      { apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
        exact (proj1 (substitution_lookup_inside M ab ac (code_numeral M 2)(zeroM M)
          (code_numeral M 1)(code_numeral M 2)(coding_lt_succ M (code_numeral M 1))) (proj2 HMap)). }
      pose proof (renaming_lookup_functional M _ _ _ _ _ p _ HP HSecond) as E. subst p.
      apply (proj2 (renaming_lift_tail M b c n (zeroM M) u v l (code_numeral M 1)(code_numeral M 1) HL)).
      apply HFix;[intro E;change (succM M (zeroM M)=zeroM M) in E;pose proof (coding_zero_lt_succ M (zeroM M)) as H;rewrite E in H;exact (coding_not_lt_zero M (zeroM M) H)|].
      exact (coding_lt_trans M _ k fresh HI HK).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))) in HP.
      cbn [code_numeral] in HP. rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in HP. subst p.
      apply (proj2 (renaming_lift_tail M b c n (zeroM M) u v l _ _ HL)).
      apply HFix;[intro E;change (succM M (succM M i'')=zeroM M) in E;pose proof (coding_zero_lt_succ M (succM M i'')) as H;rewrite E in H;exact (coding_not_lt_zero M (zeroM M) H)|].
      exact (coding_lt_trans M _ k fresh HI HK).
Qed.

Print Assumptions source_native_upshift_carrier_fixed.
Print Assumptions source_reopened_carrier_to_shift.
