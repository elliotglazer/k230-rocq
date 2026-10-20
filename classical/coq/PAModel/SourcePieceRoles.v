(** Any actual substitution with the same two live roles computes the
    canonical Pc instance. Unused tail names require no agreement. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SourceSubstitutionIdentity
  SourceSubstitutionComposition SourceShiftSpecialization SourceNumeralLift SourceRoleReopening
  SourcePieceClosure SourceD0Recipe SourceDn.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_two_role_substitution M f rb rc rn base out d X b c:
  source_bounded M f(code_numeral M 2) ->numerical_substitution M f rb rc rn base out ->
  substitution_lookup M rb rc rn base(zeroM M)d ->
  substitution_lookup M rb rc rn base(code_numeral M 1)X ->source_role_reopening M X d b c ->
  numerical_substitution M f b c(code_numeral M 2)(code_numeral M 2)out.
Proof.
  intros HB HS H0 H1 HR.
  assert(HId:numerical_substitution M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
  { apply(numerical_substitution_identity_on_bound M f _ _ _ _(code_numeral M 2)HB).
    intros i _. apply source_empty_substitution_lookup. }
  apply(numerical_substitution_composition M f(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)rb rc rn base b c(code_numeral M 2)(code_numeral M 2)f out HB HId HS).
  intros i j v HI HFirst HSecond.
  pose proof(substitution_lookup_functional M _ _ _ _ i j i HFirst(source_empty_substitution_lookup M i)) as E. subst j.
  destruct(source_numeral_initial_segment M 2 i HI) as(n&HN&->).
  assert(HKnown:substitution_lookup M rb rc rn base(code_numeral M n)(if Nat.eqb n 0 then d else X)).
  { destruct n as[|[|n]];try lia;assumption. }
  pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond HKnown) as E. subst v.
  exact(source_pc_reopening_lookup M X d b c(code_numeral M 2)n HR HN).
Qed.

Theorem source_pc_instance_of_substitution M domain level count phi d0 dn d X rb rc rn base out:
  source_d0_recipe M domain level phi d0 ->source_dn M count d0 dn ->source_bounded M dn(code_numeral M 2) ->
  numerical_substitution M dn rb rc rn base out ->substitution_lookup M rb rc rn base(zeroM M)d ->
  substitution_lookup M rb rc rn base(code_numeral M 1)X ->source_pc_instance M domain level count phi d X out.
Proof.
  intros HD0 HDN HB HS H0 H1. destruct(source_role_reopening_total M X d) as(b&c&HR).
  exists d0,dn,b,c. split;[exact HD0|]. split;[exact HDN|]. split;[exact HR|].
  exact(source_two_role_substitution M dn rb rc rn base out d X b c HB HS H0 H1 HR).
Qed.

Theorem source_pc_instance_of_renaming M domain level count phi d0 dn d X rb rc rn delta out:
  source_d0_recipe M domain level phi d0 ->source_dn M count d0 dn ->source_bounded M dn(code_numeral M 2) ->
  numerical_renaming M dn rb rc rn delta out ->renaming_lookup M rb rc rn delta(zeroM M)d ->
  renaming_lookup M rb rc rn delta(code_numeral M 1)X ->source_pc_instance M domain level count phi d X out.
Proof.
  intros HD0 HDN HB HR H0 H1.
  exact(source_pc_instance_of_substitution M domain level count phi d0 dn d X rb rc rn(addM M rn delta)out
    HD0 HDN HB(proj1(numerical_renaming_substitution M dn rb rc rn delta out)HR)
    (proj1(renaming_substitution_lookup M rb rc rn delta(zeroM M)d)H0)
    (proj1(renaming_substitution_lookup M rb rc rn delta(code_numeral M 1)X)H1)).
Qed.

Print Assumptions source_two_role_substitution.
Print Assumptions source_pc_instance_of_substitution.
Print Assumptions source_pc_instance_of_renaming.
