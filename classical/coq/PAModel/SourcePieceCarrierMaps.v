(** Three simultaneous names specialize the carrier equality cutoff square. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceNumeralLift
  NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionComposition SourceRoleReopening
  SourceTripleSpecialization SourceFiniteCutoffShift SourceQuantifierRules SourceDnCutoffDiamonds SourcePieceClosure.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_pc_carrier_cutoff_specialization M (right:bool) dn row d X Y tb tc rb rc desired :
  source_bounded M dn(code_numeral M 2) ->
  source_cutoff_shift M(if right then 1 else 2)dn row ->source_triple_prefix M d X Y tb tc ->
  source_role_reopening M(if right then Y else X)d rb rc ->
  numerical_substitution M dn rb rc(code_numeral M 2)(code_numeral M 2)desired ->
  numerical_substitution M row tb tc(code_numeral M 3)(zeroM M)desired.
Proof.
  intros HB(sb&sc&sn&HM&HRow)HTriple HRole HDesired.
  destruct(numerical_substitution_total M row tb tc(code_numeral M 3)(zeroM M)) as(actual&HActual).
  assert(HCombined:numerical_substitution M dn rb rc(code_numeral M 2)(code_numeral M 2)actual).
  { apply(numerical_substitution_composition M dn(code_numeral M 2)
      sb sc sn(code_numeral M(S(if right then 1 else 2)))
      tb tc(code_numeral M 3)(zeroM M)rb rc(code_numeral M 2)(code_numeral M 2)
      row actual HB HRow HActual).
    intros i j v HI HJ HV.
    destruct(source_numeral_initial_segment M 2 i HI) as(n&HN&->).
    assert(EJ:j=code_numeral M(SetFormulaCodes.sf_index(source_shift_sigma(if right then 1 else 2)n))).
    { eapply substitution_lookup_functional;[exact HJ|exact(source_cutoff_shift_map_fixed_lookup M _ sb sc sn HM n)]. }
    subst j. destruct right;destruct n as[|[|n]];try lia.
    - assert(EV:v=d) by(eapply substitution_lookup_functional;[exact HV|exact(proj1 HTriple)]). subst v.
      exact(source_pc_reopening_lookup M Y d rb rc(code_numeral M 2)0 HRole ltac:(lia)).
    - assert(EV:v=Y) by(eapply substitution_lookup_functional;[exact HV|exact(proj2(proj2 HTriple))]). subst v.
      exact(source_pc_reopening_lookup M Y d rb rc(code_numeral M 2)1 HRole ltac:(lia)).
    - assert(EV:v=d) by(eapply substitution_lookup_functional;[exact HV|exact(proj1 HTriple)]). subst v.
      exact(source_pc_reopening_lookup M X d rb rc(code_numeral M 2)0 HRole ltac:(lia)).
    - assert(EV:v=X) by(eapply substitution_lookup_functional;[exact HV|exact(proj1(proj2 HTriple))]). subst v.
      exact(source_pc_reopening_lookup M X d rb rc(code_numeral M 2)1 HRole ltac:(lia)). }
  pose proof(numerical_substitution_functional M dn rb rc(code_numeral M 2)(code_numeral M 2)actual desired HCombined HDesired) as E.
  now subst actual.
Qed.

Print Assumptions source_pc_carrier_cutoff_specialization.
