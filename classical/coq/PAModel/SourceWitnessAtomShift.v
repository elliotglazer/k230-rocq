(** Actual shifts of the fixed hierarchy relation and atomic membership. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
  NumericalContextRenaming RenamingSubstitution SourceQuantifierRules SourceFiniteCutoffShift SourceHierarchySyntax.
Unset Implicit Arguments.

Theorem source_LL_instance_shift M d y f shifted :
  source_LL_instance M d y f ->source_formula_shift M f shifted ->
  source_LL_instance M(succM M d)(succM M y)shifted.
Proof.
  intros HG HS.
  destruct(source_LL_instance_total M(succM M d)(succM M y)) as(next&HN).
  pose proof(source_LL_instance_substitution M d y f(succM M d)(succM M y)next
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HG HN
    (source_cutoff_shift_base_lookup M d)(source_cutoff_shift_base_lookup M y)) as HSub.
  pose proof(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)
    (code_numeral M 1)next)HSub) as HR.
  pose proof(numerical_renaming_functional M f(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    next shifted HR HS) as E. now subst next.
Qed.

Theorem source_member_atom_shift M x y f shifted :
  sf_relation M SFMember x y f ->source_formula_shift M f shifted ->
  sf_relation M SFMember(succM M x)(succM M y)shifted.
Proof.
  intros HG HS.
  destruct(proj1(numerical_renaming_member M x y f(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)shifted HG)HS) as(x'&y'&HX&HY&HO).
  apply context_shift_lookup in HX,HY. now subst x' y'.
Qed.

Print Assumptions source_LL_instance_shift.
Print Assumptions source_member_atom_shift.
