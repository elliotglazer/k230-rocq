(** Ordinary whole-formula shift has no occurrence of its new slot0;
    specializing that slot at any name restores the original internal code. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalRenaming NumericalRenamingMaps NumericalSubstitutionMaps NumericalSubstitution
 NumericalInstantiation SourceQuantifierRules SourceRenamingIdentity SourceShiftSpecialization
 SourceRenamingSquare RenamingSubstitution SubstitutionSource.
Unset Implicit Arguments.
Theorem source_whole_shift_instantiation M f shifted k witness:
 source_bounded M f k ->source_formula_shift M f shifted ->numerical_instantiation M shifted witness f.
Proof.
 intros BF HS. destruct(substitution_singleton_total M witness)as(b&c&HH&HT).
 assert(HI:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF).
   intros i _. apply source_empty_renaming_lookup. }
 exists b,c. split;[exact HH|].
 apply(numerical_source_renaming_square M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  b c(code_numeral M 1)(zeroM M)f shifted f BF
  (proj1(numerical_renaming_empty_substitution M f _ _ _ f)HI)HS HI).
 intros i j l m HBound HJ HM HL.
 assert(EJ:j=i)by(eapply substitution_lookup_functional;[exact HJ|apply source_empty_substitution_lookup]). subst j.
 assert(EM:m=i)by(eapply renaming_lookup_functional;[exact HM|apply source_empty_renaming_lookup]). subst m.
 assert(EL:l=succM M i).
 { apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)i l
    (coding_not_lt_zero M i))in HL. rewrite HL. symmetry. apply Arithmetic.succ_as_add. }
 subst l. apply substitution_singleton_tail.
Qed.
Print Assumptions source_whole_shift_instantiation.
