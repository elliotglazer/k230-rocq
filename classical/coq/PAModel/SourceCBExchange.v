(** The two literal role permutations in Qf and OC compose to the Dn
    rotation. All formulas and source bounds remain internal model codes. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SourceBounded NumericalEnvironments
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution
  SourceShiftSpecialization SourceRenamingIdentity SourceSubstitutionIdentity SourceRenamingSquare SourceQfRecipe
  SourceDnStep SourceSwap SourceFixedSwap SourceNumeralLift SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_qf_exchange_swap_rotate M previous q rotated k:
  source_bounded M previous k ->
  numerical_renaming M previous(code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)q ->
  numerical_renaming M previous(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)rotated ->
  numerical_renaming M q(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M)rotated.
Proof.
  intros HB HQ HR.
  assert(HId:numerical_substitution M previous(zeroM M)(zeroM M)(zeroM M)(zeroM M)previous).
  { apply(numerical_substitution_identity_on_bound M previous _ _ _ _ k HB).
    intros i _. apply source_empty_substitution_lookup. }
  apply(proj2(numerical_renaming_substitution M q(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M)rotated)). rewrite coding_add_zero_r.
  apply(numerical_source_renaming_square M previous k
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 210)(code_numeral M 6)(code_numeral M 3)(zeroM M)
    (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)
    (code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(code_numeral M 2)
    previous q rotated HB HId HQ HR).
  intros i j l m HI HSI HRL HQL.
  pose proof(substitution_lookup_functional M _ _ _ _ i j i HSI(source_empty_substitution_lookup M i)) as E. subst j.
  assert(Convert:forall i v,renaming_lookup M(code_numeral M 3)(code_numeral M 1)
    (code_numeral M 2)(zeroM M)i v ->substitution_lookup M(code_numeral M 3)(code_numeral M 1)
      (code_numeral M 2)(code_numeral M 2)i v).
  { intros a v HH. pose proof(proj1(renaming_substitution_lookup M(code_numeral M 3)(code_numeral M 1)
      (code_numeral M 2)(zeroM M)a v)HH) as H. now rewrite coding_add_zero_r in H. }
  apply Convert.
  destruct(environment_lt_cases M i(code_numeral M 3)) as[HL|HL].
  - destruct(source_numeral_initial_segment M 3 i HL) as(v&HV&->).
    destruct v as[|[|[|v]]];try lia.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HQL(source_qf_exchange_zero M)) as E. subst l.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HRL(source_dn_rotate_zero M)) as E. subst m.
      exact(proj1(source_fixed_swap_map M)).
    + pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HQL(source_qf_exchange_one M)) as E. subst l.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HRL(source_dn_rotate_one M)) as E. subst m.
      apply source_swap_tail.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ l _ HQL(source_qf_exchange_two M)) as E. subst l.
      pose proof(renaming_lookup_functional M _ _ _ _ _ m _ HRL(source_dn_rotate_two M)) as E. subst m.
      exact(proj2(source_fixed_swap_map M)).
  - pose proof(renaming_lookup_functional M _ _ _ _ i l i HQL(source_qf_exchange_outside M i HL)) as E. subst l.
    pose proof(renaming_lookup_functional M _ _ _ _ i m i HRL(source_dn_rotate_outside M i HL)) as E. subst m.
    assert(HN:~coding_lt M i(code_numeral M 2)).
    { intro HBad. apply HL. exact(coding_lt_trans M i(code_numeral M 2)(code_numeral M 3)HBad(coding_lt_succ M _)). }
    apply(proj2(renaming_lookup_outside M _ _ _ _ i i HN)). symmetry. apply coding_add_zero_r.
Qed.

Print Assumptions source_qf_exchange_swap_rotate.
