(** Exact cutoff square for the two ordinal-monotonicity predicate matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceRenamingSquare SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceOrdinalMonotoneMaps
  SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_oc_mono_matrix_shift M right phi phi' row row' k :
  source_bounded M phi k ->source_oc_mono_matrix M right phi row ->
  source_cutoff_shift M 2 phi phi' ->source_cutoff_shift M 3 row row' ->
  source_oc_mono_matrix M right phi' row'.
Proof.
  intros HB HRow (rb&rc&rn&HRM&HR) (tb&tc&tn&HTM&HT).
  pose proof(proj1(numerical_renaming_substitution M phi
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)
    (code_numeral M 3) row) HRow) as HS. rewrite descriptor_numeral_add in HS.
  apply(proj2(numerical_renaming_substitution M phi'
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)
    (code_numeral M 3) row')). rewrite descriptor_numeral_add.
  apply(numerical_source_renaming_square M phi k
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 5)
    rb rc rn(code_numeral M 1) tb tc tn(code_numeral M 1)
    (code_numeral M(source_oc_mono_dividend right))(code_numeral M 3)(code_numeral M 2)(code_numeral M 5)
    row phi' row' HB HS
    (source_cutoff_shift_map_renaming M 2 phi phi' rb rc rn HRM HR)
    (source_cutoff_shift_map_renaming M 3 row row' tb tc tn HTM HT)).
  intros i j l m HI HSI HTJ HRI.
  pose proof(renaming_substitution_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 3) i j) as HC.
  rewrite descriptor_numeral_add in HC. apply(proj2 HC) in HSI.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 rb rc rn i l HRM)) in HRI.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 3 tb tc tn j m HTM)) in HTJ.
  pose proof(renaming_substitution_lookup M(code_numeral M(source_oc_mono_dividend right))
    (code_numeral M 3)(code_numeral M 2)(code_numeral M 3) l m) as HC'.
  rewrite descriptor_numeral_add in HC'. apply(proj1 HC').
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i)
    as [E|[idx E]];subst i.
  - pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI(source_oc_mono_first_lookup M right)) as E. subst j.
    pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HRM 0)) as E. subst l.
    assert(HFix:substitution_lookup M tb tc tn(code_numeral M 4)
      (code_numeral M(source_oc_mono_first right))(code_numeral M(source_oc_mono_first right))).
    { destruct right;[exact(source_cutoff_shift_map_fixed_lookup M 3 tb tc tn HTM 0)|
        exact(source_cutoff_shift_map_fixed_lookup M 3 tb tc tn HTM 1)]. }
    pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ HFix) as E. subst m.
    exact(source_oc_mono_first_lookup M right).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) idx)
      as [E|[tail E]];subst idx.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI(source_oc_mono_second_lookup M right)) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
        (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HRM 1)) as E. subst l.
      pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ
        (source_cutoff_shift_map_fixed_lookup M 3 tb tc tn HTM 2)) as E. subst m.
      exact(source_oc_mono_second_lookup M right).
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI(source_oc_mono_tail_lookup M right tail)) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
        (source_cutoff_shift_map_tail_lookup M 2 rb rc rn tail HRM)) as E. subst l.
      pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ
        (source_cutoff_shift_map_tail_lookup M 3 tb tc tn(succM M(succM M tail)) HTM)) as E. subst m.
      exact(source_oc_mono_tail_lookup M right(succM M tail)).
Qed.

Print Assumptions source_oc_mono_matrix_shift.
