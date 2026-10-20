(** A guarded existential shifts its arbitrary witness matrix by C1;
    its fixed unary domain predicate is unchanged. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceRelativizationRules NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity
  SourceFiniteCutoffShift SourceLiftedPredicateShift SourceQfFunctionality SourceDomainInstances
  SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_guarded_witness_shift M domain phi phi' ex shifted :
  source_bounded M domain (code_numeral M 1) ->source_cutoff_shift M 1 phi phi' ->
  sr_quantifier M false domain phi ex ->source_formula_shift M ex shifted ->
  sr_quantifier M false domain phi' shifted.
Proof.
  intros HD HC (body&HB&HE) HS.
  destruct (proj1 (numerical_renaming_quantifier M false body ex (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) shifted HE) HS) as (rb&rc&rn&body'&HMap&HR&HEx).
  destruct (proj1 (numerical_renaming_binary M SFAnd domain phi body rb rc rn (code_numeral M 1)
    body' (or_introl eq_refl) HB) HR) as (domain'&phi''&HD'&HP'&HBody).
  assert (HDomain:numerical_renaming M domain rb rc rn (code_numeral M 1) domain).
  { apply (numerical_renaming_identity_on_bound M domain rb rc rn (code_numeral M 1)
      (code_numeral M 1) HD).
    intros i HI. rewrite (domain_index_below_one M i HI). exact (proj1 (proj2 HMap)). }
  pose proof (numerical_renaming_functional M domain rb rc rn (code_numeral M 1) domain' domain HD' HDomain) as E.
  subst domain'.
  pose proof (source_lifted_shift_is_cutoff M phi rb rc rn phi'' HMap HP') as HC'.
  pose proof (source_cutoff_shift_functional M 1 phi phi'' phi' HC' HC) as E. subst phi''.
  exists body'. auto.
Qed.

Print Assumptions source_guarded_witness_shift.
