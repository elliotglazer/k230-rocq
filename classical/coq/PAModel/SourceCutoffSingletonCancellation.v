(** A source matrix ignores the fresh parameter inserted above its
    witness. Removing that parameter by any variable preserves the matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
  SourceSubstitutionIdentity SourceRenamingIdentity SourceShiftSpecialization
  SourceFiniteCutoffShift SourceSeparationSpecializationMaps SourceRenamingSquare SubstitutionSource.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_one_singleton_lift_cancel M phi shifted k b c ab ac an :
  source_bounded M phi k ->source_cutoff_shift M 1 phi shifted ->
  substitution_lift M b c(code_numeral M 1)(zeroM M) ab ac an ->
  numerical_substitution M shifted ab ac an(code_numeral M 1) phi.
Proof.
  intros HB HC HL.
  destruct(source_cutoff_one_renaming M phi shifted HC) as (rb&rc&rn&HRL&HR).
  assert(HS:numerical_substitution M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M) phi).
  { apply(numerical_substitution_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_substitution_lookup. }
  assert(HId:numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M) phi).
  { apply(numerical_renaming_identity_on_bound M phi _ _ _ _ k HB).
    intros i _. apply source_empty_renaming_lookup. }
  apply(numerical_source_renaming_square M phi k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) rb rc rn(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) ab ac an(code_numeral M 1)
    phi shifted phi HB HS HR HId).
  intros i j l m HI HSub HIdLookup HShift.
  pose proof(substitution_lookup_functional M _ _ _ _ i j i HSub
    (source_empty_substitution_lookup M i)) as E. subst j.
  pose proof(renaming_lookup_functional M _ _ _ _ i m i HIdLookup
    (source_empty_renaming_lookup M i)) as E. subst m.
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i) as [E|[idx E]];subst i.
  - apply(proj1(renaming_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      rb rc rn l HRL)) in HShift. subst l.
    exact(proj2(substitution_lift_head M b c(code_numeral M 1)(zeroM M) ab ac an(zeroM M) HL) eq_refl).
  - destruct(renaming_lift_tail_inv M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      rb rc rn idx l HRL HShift) as (v&HV&EL).
    apply NumericalContextRenaming.context_shift_lookup in HV. subst v l.
    apply(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M) ab ac an
      (succM M idx) idx HL)). apply substitution_singleton_tail.
Qed.

Print Assumptions source_cutoff_one_singleton_lift_cancel.
