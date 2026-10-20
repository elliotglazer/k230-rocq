From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalSubstitutionMaps NumericalSubstitution
  NumericalRenaming SourceFiniteCutoffShift SourceRelativizationFunctionality SourceD0Recipe SourceDn SourceQfRecipe.
Unset Implicit Arguments.

Theorem source_cutoff_shift_maps_equivalent M depth b c n d e m :
  source_cutoff_shift_map M depth b c n -> source_cutoff_shift_map M depth d e m ->
  substitution_equivalent M b c n d e m (code_numeral M (S depth)).
Proof.
  revert b c n d e m. induction depth as [|depth IH];intros b c n d e m HB HD.
  - destruct HB as [-> [-> ->]],HD as [-> [-> ->]]. apply substitution_equivalent_refl.
  - destruct HB as (u & v & l & HU & HL),HD as (u' & v' & l' & HU' & HL').
    exact (substitution_lift_extensional M u v l u' v' l' (code_numeral M (S depth))
      b c n d e m (IH u v l u' v' l' HU HU') HL HL').
Qed.
Theorem source_cutoff_shift_functional M depth phi out out' :
  source_cutoff_shift M depth phi out -> source_cutoff_shift M depth phi out' -> out=out'.
Proof.
  intros (b & c & n & HM & HG) (d & e & m & HM' & HG').
  exact (numerical_substitution_functional_equivalent M phi b c n d e m (code_numeral M (S depth)) out out'
    (source_cutoff_shift_maps_equivalent M depth b c n d e m HM HM') HG HG').
Qed.
Theorem source_cutoff_shift_thrice_functional M phi out out' :
  source_cutoff_shift_thrice M phi out -> source_cutoff_shift_thrice M phi out' -> out=out'.
Proof.
  intros (a & b & HA & HB & HO) (a' & b' & HA' & HB' & HO').
  assert (E : a=a') by (eapply source_cutoff_shift_functional;eassumption). subst a'.
  assert (E : b=b') by (eapply source_cutoff_shift_functional;eassumption). subst b'.
  exact (source_cutoff_shift_functional M 1 b out out' HO HO').
Qed.
Theorem source_ew_recipe_functional M domain matrix out out' :
  source_ew_recipe M domain matrix out -> source_ew_recipe M domain matrix out' -> out=out'.
Proof.
  intros (atom & left & right & HA & HL & HR & HO) (atom' & left' & right' & HA' & HL' & HR' & HO').
  assert (E : atom=atom') by (eapply sf_relation_functional;eassumption). subst atom'.
  assert (E : left=left') by (eapply sr_quantifier_functional;eassumption). subst left'.
  assert (E : right=right') by (eapply sr_quantifier_functional;eassumption). subst right'.
  exact (sf_relation_functional M SFImpl left right out out' HO HO').
Qed.
Theorem source_d0_recipe_functional M domain level body out out' :
  source_d0_recipe M domain level body out -> source_d0_recipe M domain level body out' -> out=out'.
Proof.
  intros (shifted & ew & implication & HS & HE & HI & HO) (shifted' & ew' & implication' & HS' & HE' & HI' & HO').
  assert (E : shifted=shifted') by (eapply source_cutoff_shift_thrice_functional;eassumption). subst shifted'.
  assert (E : ew=ew') by (eapply source_ew_recipe_functional;eassumption). subst ew'.
  assert (E : implication=implication') by (eapply sf_relation_functional;eassumption). subst implication'.
  exact (sf_relation_functional M SFAll implication (zeroM M) out out' HO HO').
Qed.
Theorem source_qf_recipe_functional M domain level count body out out' :
  source_qf_recipe M domain level count body out -> source_qf_recipe M domain level count body out' -> out=out'.
Proof.
  intros (d0 & dn & HD & HN & HO) (d0' & dn' & HD' & HN' & HO').
  assert (E : d0=d0') by (eapply source_d0_recipe_functional;eassumption). subst d0'.
  assert (E : dn=dn') by (eapply source_dn_functional;eassumption). subst dn'.
  exact (numerical_renaming_functional M dn (code_numeral M 210) (code_numeral M 6)
    (code_numeral M 3) (zeroM M) out out' HO HO').
Qed.

Print Assumptions source_cutoff_shift_functional.
Print Assumptions source_cutoff_shift_thrice_functional.
Print Assumptions source_ew_recipe_functional.
Print Assumptions source_d0_recipe_functional.
Print Assumptions source_qf_recipe_functional.
