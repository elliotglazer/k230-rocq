(** Inserting a fresh outer parameter above the distinguished witness
    commutes with arbitrary source substitution lifted under that witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceSeparationSpecializationMaps
  SourceRenamingSquare.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_one_lifted_substitution M phi phi' shifted shifted' k
    b c n base ab ac an tb tc tn :
  source_bounded M phi k ->substitution_lift M b c n base ab ac an ->
  substitution_lift M ab ac an(succM M base) tb tc tn ->
  numerical_substitution M phi ab ac an(succM M base) phi' ->
  source_cutoff_shift M 1 phi shifted ->source_cutoff_shift M 1 phi' shifted' ->
  numerical_substitution M shifted tb tc tn(succM M(succM M base)) shifted'.
Proof.
  intros HB HL HT HS HC HC'.
  destruct(source_cutoff_one_renaming M phi shifted HC) as (rb&rc&rn&HRL&HR).
  destruct(source_cutoff_one_renaming M phi' shifted' HC') as (sb&sc&sn&HSL&HShift).
  apply(numerical_source_renaming_square M phi k
    ab ac an(succM M base) rb rc rn(code_numeral M 1)
    sb sc sn(code_numeral M 1) tb tc tn(succM M(succM M base))
    phi' shifted shifted' HB HS HR HShift).
  intros i j l m HI HSub HAfter HBefore.
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i) as [E|[idx E]];subst i.
  - apply(proj1(substitution_lift_head M b c n base ab ac an j HL)) in HSub. subst j.
    apply(proj1(renaming_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      sb sc sn m HSL)) in HAfter. subst m.
    apply(proj1(renaming_lift_head M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      rb rc rn l HRL)) in HBefore. subst l.
    exact(proj2(substitution_lift_head M ab ac an(succM M base) tb tc tn(zeroM M) HT) eq_refl).
  - destruct(substitution_lift_tail_inv M b c n base ab ac an idx j HL HSub) as (v&HV&EJ).
    subst j.
    destruct(renaming_lift_tail_inv M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      sb sc sn v m HSL HAfter) as (w&HW&EM).
    apply NumericalContextRenaming.context_shift_lookup in HW. subst w m.
    destruct(renaming_lift_tail_inv M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
      rb rc rn idx l HRL HBefore) as (q&HQ&EL).
    apply NumericalContextRenaming.context_shift_lookup in HQ. subst q l.
    apply(proj2(substitution_lift_tail M ab ac an(succM M base) tb tc tn
      (succM M idx)(succM M v) HT)).
    exact(proj2(substitution_lift_tail M b c n base ab ac an idx v HL) HV).
Qed.

Print Assumptions source_cutoff_one_lifted_substitution.
