(** Inserting a parameter above slots0 and1 commutes with their swap. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceRenamingSquare SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceSwap SourceFixedSwap.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_two_swap M phi phi' swapped swapped' k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  numerical_renaming M phi(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M) swapped ->
  source_cutoff_shift M 2 swapped swapped' ->
  numerical_renaming M phi'(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M) swapped'.
Proof.
  intros HB (rb&rc&rn&HRM&HR) HSwap (tb&tc&tn&HTM&HT).
  pose proof(proj1(numerical_renaming_substitution M phi(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M) swapped) HSwap) as HS.
  rewrite coding_add_zero_r in HS.
  apply(proj2(numerical_renaming_substitution M phi'(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M) swapped')). rewrite coding_add_zero_r.
  apply(numerical_source_renaming_square M phi k
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(code_numeral M 2)
    rb rc rn(code_numeral M 1) tb tc tn(code_numeral M 1)
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(code_numeral M 2)
    swapped phi' swapped' HB HS
    (source_cutoff_shift_map_renaming M 2 phi phi' rb rc rn HRM HR)
    (source_cutoff_shift_map_renaming M 2 swapped swapped' tb tc tn HTM HT)).
  intros i j l m HI HSI HTJ HRI.
  pose proof(renaming_substitution_lookup M(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M) i j) as HConvert. rewrite coding_add_zero_r in HConvert.
  apply(proj2 HConvert) in HSI.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 rb rc rn i l HRM)) in HRI.
  apply(proj1(source_cutoff_shift_map_renaming_lookup M 2 tb tc tn j m HTM)) in HTJ.
  pose proof(renaming_substitution_lookup M(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M) l m) as HConvert'. rewrite coding_add_zero_r in HConvert'.
  apply(proj1 HConvert').
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i)
    as [E|[idx E]];subst i.
  - pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI(proj1(source_fixed_swap_map M))) as E. subst j.
    pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
      (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HRM 0)) as E. subst l.
    pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ
      (source_cutoff_shift_map_fixed_lookup M 2 tb tc tn HTM 1)) as E. subst m.
    exact(proj1(source_fixed_swap_map M)).
  - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) idx)
      as [E|[tail E]];subst idx.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI(proj2(source_fixed_swap_map M))) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
        (source_cutoff_shift_map_fixed_lookup M 2 rb rc rn HRM 1)) as E. subst l.
      pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ
        (source_cutoff_shift_map_fixed_lookup M 2 tb tc tn HTM 0)) as E. subst m.
      exact(proj2(source_fixed_swap_map M)).
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HSI
        (source_swap_tail M(code_numeral M 3)(code_numeral M 1) tail)) as E. subst j.
      pose proof(substitution_lookup_functional M _ _ _ _ _ l _ HRI
        (source_cutoff_shift_map_tail_lookup M 2 rb rc rn tail HRM)) as E. subst l.
      pose proof(substitution_lookup_functional M _ _ _ _ _ m _ HTJ
        (source_cutoff_shift_map_tail_lookup M 2 tb tc tn tail HTM)) as E. subst m.
      exact(source_swap_tail M(code_numeral M 3)(code_numeral M 1)(succM M tail)).
Qed.

Print Assumptions source_cutoff_two_swap.
