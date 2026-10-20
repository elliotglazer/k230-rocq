(** Exact arbitrary-matrix normalization of L_definable(psiS phi).
    The free hierarchy carrier is index0 and the selected set is index1,
    so after the witness and point binders their names are 2 and 3. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceFiniteCutoffShift SourceQfFunctionality SourceCutoffShiftConstructors SourceLMatrixRecipes
  SourceLDefinableProfile SourceSetRelativization SourceSetRelativizationFunctionality.
Unset Implicit Arguments.

Theorem source_L_psiS_definable_normalization M domain phi psi result :
  source_l_psiS M phi psi ->source_definable_profile M domain psi result ->
  exists first second matrix member selected relative,
    source_cutoff_shift M 1 phi first /\source_cutoff_shift M 1 first second /\source_cutoff_shift M 1 second matrix /\
    sf_relation M SFMember(zeroM M)(code_numeral M 3)member /\
    source_set_relativization M(code_numeral M 2)matrix relative /\sf_relation M SFAnd member relative selected /\
    code_relation M(L_definable_profile_environment selected domain)
      (E_L_definable_profile(CEvar 0)(CEvar 1))result.
Proof.
  intros(first&atom1&HFirst&HAtom1&HPsi)(psi1&psi2&psiRelative&HPsi1&HPsi2&HRelative&HResult).
  destruct(source_cutoff_shift_total M 1 first) as(second&HSecond).
  destruct(source_cutoff_shift_total M 1 second) as(matrix&HMatrix).
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 2)) as(atom2&HAtom2).
  destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 3)) as(atom3&HAtom3).
  destruct(sf_relation_total M SFAnd atom2 second) as(raw1&HRaw1).
  destruct(sf_relation_total M SFAnd atom3 matrix) as(raw2&HRaw2).
  pose proof(source_cutoff_shift_fixed_member M 1 0 1 atom1 atom2 HAtom1 HAtom2) as HA1.
  pose proof(source_cutoff_shift_fixed_member M 1 0 2 atom2 atom3 HAtom2 HAtom3) as HA2.
  pose proof(source_cutoff_shift_binary M 1 SFAnd atom1 first psi atom2 second raw1(or_introl eq_refl)HPsi HRaw1 HA1 HSecond) as HR1.
  pose proof(source_cutoff_shift_functional M 1 psi psi1 raw1 HPsi1 HR1) as E. subst psi1.
  pose proof(source_cutoff_shift_binary M 1 SFAnd atom2 second raw1 atom3 matrix raw2(or_introl eq_refl)HRaw1 HRaw2 HA2 HMatrix) as HR2.
  pose proof(source_cutoff_shift_functional M 1 raw1 psi2 raw2 HPsi2 HR2) as E. subst psi2.
  destruct(source_set_relativization_total M(code_numeral M 2)matrix) as(relative&HR).
  destruct(sf_relation_total M SFAnd atom3 relative) as(selected&HS).
  pose proof(source_set_relativization_atom M(code_numeral M 2)SFMember(zeroM M)(code_numeral M 3)atom3(or_introl eq_refl)HAtom3) as HAtomRelative.
  pose proof(source_set_relativization_binary M(code_numeral M 2)SFAnd atom3 matrix raw2 atom3 relative selected
    (or_introl eq_refl)HRaw2 HAtomRelative HR HS) as HSelectedRelative.
  pose proof(source_set_relativization_functional M raw2(code_numeral M 2)psiRelative selected HRelative HSelectedRelative) as E. subst psiRelative.
  exists first,second,matrix,atom3,selected,relative. repeat first[assumption|split].
Qed.
Print Assumptions source_L_psiS_definable_normalization.
