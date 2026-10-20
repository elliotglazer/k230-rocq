(** The two reopened roles determine Pc exactly, independently of the
    particular beta witnesses used to store the prefix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SourceBounded
  NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution SourceNumeralLift
  SourceRoleReopening SourcePieceClosure SourceQfFunctionality SourceDn.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_pc_reopening_equivalent M X d b c e j base:
  source_role_reopening M X d b c ->source_role_reopening M X d e j ->
  substitution_equivalent M b c(code_numeral M 2)e j(code_numeral M 2)base.
Proof.
  intros HR HT i v.
  assert(Forward:forall b c e j,source_role_reopening M X d b c ->source_role_reopening M X d e j ->
    substitution_lookup M b c(code_numeral M 2)base i v ->substitution_lookup M e j(code_numeral M 2)base i v).
  { intros ab ac tb tc HA HB HS. destruct(environment_lt_cases M i(code_numeral M 2)) as[HI|HI].
    - destruct(source_numeral_initial_segment M 2 i HI) as(n&HN&->).
      pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HS
        (source_pc_reopening_lookup M X d ab ac base n HA HN)) as E. subst v.
      exact(source_pc_reopening_lookup M X d tb tc base n HB HN).
    - apply(proj2(substitution_lookup_outside M tb tc(code_numeral M 2)base i v HI)).
      exact(proj1(substitution_lookup_outside M ab ac(code_numeral M 2)base i v HI)HS). }
  split;[exact(Forward b c e j HR HT)|exact(Forward e j b c HT HR)].
Qed.

Theorem source_pc_instance_functional M domain level count phi d X a b:
  source_pc_instance M domain level count phi d X a ->source_pc_instance M domain level count phi d X b ->a=b.
Proof.
  intros(d0&dn&rb&rc&H0&HDN&HR&HA)(d0'&dn'&sb&sc&H0'&HDN'&HS&HB).
  pose proof(source_d0_recipe_functional M domain level phi d0' d0 H0' H0) as E. subst d0'.
  pose proof(source_dn_functional M count d0 dn' dn HDN' HDN) as E. subst dn'.
  pose proof(proj1(numerical_substitution_extensional M dn sb sc(code_numeral M 2)
    rb rc(code_numeral M 2)(code_numeral M 2)b
    (source_pc_reopening_equivalent M X d sb sc rb rc(code_numeral M 2)HS HR))HB) as HB'.
  exact(numerical_substitution_functional M dn rb rc(code_numeral M 2)(code_numeral M 2)a b HA HB').
Qed.

Print Assumptions source_pc_reopening_equivalent.
Print Assumptions source_pc_instance_functional.
