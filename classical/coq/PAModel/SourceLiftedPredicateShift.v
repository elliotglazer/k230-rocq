(** The cutoff1 predicate shift is exactly renaming lifted under one
    source binder. The beta representation of the lifted map is arbitrary. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SourceFiniteCutoffShift SourceQfFunctionality.
Unset Implicit Arguments.

Theorem source_lifted_shift_is_cutoff M phi rb rc rn out :
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) rb rc rn ->
  numerical_renaming M phi rb rc rn (code_numeral M 1) out ->
  source_cutoff_shift M 1 phi out.
Proof.
  intros HL HR. exists rb,rc,rn. split.
  - exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    pose proof (proj1 (renaming_substitution_lift M (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) rb rc rn) HL) as HS.
    rewrite Arithmetic.add_zero in HS. exact HS.
  - pose proof (proj1 (numerical_renaming_substitution_uniform M phi rb rc rn
      (code_numeral M 1) out) HR) as HS.
    assert (EE:addM M rn (code_numeral M 1)=code_numeral M 2).
    { rewrite (proj1 HL). change (addM M (succM M (zeroM M)) (code_numeral M 1)=code_numeral M 2). rewrite Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. }
    rewrite EE in HS. exact HS.
Qed.

Theorem source_cutoff_is_lifted_shift M phi out rb rc rn :
  source_cutoff_shift M 1 phi out ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) rb rc rn ->
  numerical_renaming M phi rb rc rn (code_numeral M 1) out.
Proof.
  intros HP HL.
  destruct (numerical_renaming_total M phi rb rc rn (code_numeral M 1)) as [other HR].
  pose proof (source_lifted_shift_is_cutoff M phi rb rc rn other HL HR) as HO.
  pose proof (source_cutoff_shift_functional M 1 phi other out HO HP) as E. now subst other.
Qed.

Print Assumptions source_lifted_shift_is_cutoff.
Print Assumptions source_cutoff_is_lifted_shift.

