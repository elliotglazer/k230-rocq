(** Assigning parameters i to i+start is literally a shift above the
    distinguished witness, even for internally many parameters. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 SourceBounded SourceShiftSpecialization SourceRenamingIdentity SourceSubstitutionIdentity SourceRenamingSquare SourceBallSMembershipBlock.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_piece_offset_matrix M count start pb pc ub uc un rb rc rn phi out:
 source_bounded M phi(succM M count) ->balls_offset_assignment M start count pb pc ->
 substitution_lift M pb pc count(zeroM M)ub uc un ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->
 numerical_renaming M phi rb rc rn start out ->numerical_substitution M phi ub uc un(code_numeral M 1)out.
Proof.
 intros HB HOffset HU HRL HR.
 assert(HId:numerical_substitution M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
 { apply(numerical_substitution_identity_on_bound M phi _ _ _ _(succM M count)HB).
   intros i _. apply source_empty_substitution_lookup. }
 assert(HRI:numerical_renaming M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
 { apply(numerical_renaming_identity_on_bound M phi _ _ _ _ (succM M count)HB).
   intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_square M phi(succM M count)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  rb rc rn start ub uc un(code_numeral M 1)phi phi out HB HId HRI HR).
 intros i j l m HI HJ HM HL.
 assert(E:j=i)by(eapply substitution_lookup_functional;[exact HJ|apply source_empty_substitution_lookup]). subst j.
 assert(E:l=i)by(eapply renaming_lookup_functional;[exact HL|apply source_empty_renaming_lookup]). subst l.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - apply(proj1(renaming_lift_head M _ _ _ _ _ _ _ _ HRL))in HM. subst m.
   exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HU)eq_refl).
 - destruct(renaming_lift_tail_inv M _ _ _ _ _ _ _ _ _ HRL HM)as(value&HV&E). subst m.
   apply(proj1(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)start idx value(coding_not_lt_zero M idx)))in HV.
   subst value. apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HU)).
   assert(HIdx:coding_lt M idx count)by(exact(proj1(coding_lt_succ_cancel M idx count)HI)).
   apply(proj2(substitution_lookup_inside M pb pc count(zeroM M)idx(addM M idx start)HIdx)).
   exact(proj2(HOffset idx(addM M idx start)HIdx)eq_refl).
Qed.
Print Assumptions source_piece_offset_matrix.
