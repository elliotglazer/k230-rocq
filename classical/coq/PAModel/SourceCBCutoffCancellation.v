(** The extra container-parameter slot in the OC theorem is removed by
    an actual singleton substitution lifted under its two binders. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
  SourceSubstitutionIdentity SourceRenamingIdentity SourceShiftSpecialization SourceFiniteCutoffShift
  SourceCutoffShiftCommutation SourceRenamingSquare SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_two_singleton_double_lift_cancel M phi shifted k b c ab ac an tb tc tn:
  source_bounded M phi k ->source_cutoff_shift M 2 phi shifted ->
  substitution_lift M b c(code_numeral M 1)(zeroM M)ab ac an ->
  substitution_lift M ab ac an(code_numeral M 1)tb tc tn ->
  numerical_substitution M shifted tb tc tn(code_numeral M 2)phi.
Proof.
  intros HB(rb&rc&rn&HM&HS)HL1 HL2.
  pose proof(source_cutoff_shift_map_renaming M 2 phi shifted rb rc rn HM HS) as HR.
  assert(HId:numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
  { apply(numerical_renaming_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_renaming_lookup. }
  assert(HSub:numerical_substitution M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
  { apply(numerical_substitution_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_substitution_lookup. }
  apply(numerical_source_renaming_square M phi k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)rb rc rn(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)tb tc tn(code_numeral M 2)
    phi shifted phi HB HSub HR HId).
  intros i j l m HI HSI HIM HIL.
  pose proof(substitution_lookup_functional M _ _ _ _ i j i HSI(source_empty_substitution_lookup M i)) as E. subst j.
  pose proof(renaming_lookup_functional M _ _ _ _ i m i HIM(source_empty_renaming_lookup M i)) as E. subst m.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 rb rc rn i l HM)) in HIL.
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[E|[idx E]];subst i.
  - pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HIL
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 0)) as E. subst l.
    exact(proj2(substitution_lift_head M ab ac an(code_numeral M 1)tb tc tn(zeroM M)HL2)eq_refl).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)idx)
      as[E|[tail E]];subst idx.
    + pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HIL
        (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HM 1)) as E. subst l.
      apply(proj2(substitution_lift_tail M ab ac an(code_numeral M 1)tb tc tn(zeroM M)(zeroM M)HL2)).
      exact(proj2(substitution_lift_head M b c(code_numeral M 1)(zeroM M)ab ac an(zeroM M)HL1)eq_refl).
    + pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HIL
        (source_cutoff_shift_map_tail_lookup M 2 rb rc rn tail HM)) as E. subst l.
      apply(proj2(substitution_lift_tail M ab ac an(code_numeral M 1)tb tc tn
        (succM M(succM M tail))(succM M tail)HL2)).
      apply(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M)ab ac an
        (succM M tail)tail HL1)). apply substitution_singleton_tail.
Qed.

Print Assumptions source_cutoff_two_singleton_double_lift_cancel.
