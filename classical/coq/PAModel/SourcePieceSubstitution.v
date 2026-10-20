(** Pc commutes with arbitrary capture-avoiding source substitutions on
    its two explicit ordinal/set names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  SourceSubstitutionComposition SourceNumeralLift SourceRoleReopening SourcePieceClosure.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_pc_instance_substitution M domain level count phi d X f rb rc rn base e Y out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(succM M count) ->source_pc_instance M domain level count phi d X f ->
  numerical_substitution M f rb rc rn base out ->substitution_lookup M rb rc rn base d e ->
  substitution_lookup M rb rc rn base X Y ->source_pc_instance M domain level count phi e Y out.
Proof.
  intros HD HL HB(d0&dn&ab&ac&H0&HN&HA&HS)HT HDE HXY.
  pose proof(source_pc_dn_bounded M domain level count phi d0 dn HD HL HB H0 HN) as HBDN.
  destruct(source_role_reopening_total M Y e) as(tb&tc&HMap).
  exists d0,dn,tb,tc. split;[exact H0|]. split;[exact HN|]. split;[exact HMap|].
  apply(numerical_substitution_composition M dn(code_numeral M 2)
    ab ac(code_numeral M 2)(code_numeral M 2)rb rc rn base
    tb tc(code_numeral M 2)(code_numeral M 2)f out HBDN HS HT).
  intros i j v HI HFirst HSecond.
  destruct(source_numeral_initial_segment M 2 i HI) as(n&HN'&->).
  pose proof(substitution_lookup_functional M _ _ _ _ _ j _ HFirst
    (source_pc_reopening_lookup M X d ab ac(code_numeral M 2)n HA HN')) as E. subst j.
  assert(HKnown:substitution_lookup M rb rc rn base(if Nat.eqb n 0 then d else X)(if Nat.eqb n 0 then e else Y)).
  { destruct n as[|[|n]];try lia;assumption. }
  pose proof(substitution_lookup_functional M _ _ _ _ _ v _ HSecond HKnown) as E. subst v.
  exact(source_pc_reopening_lookup M Y e tb tc(code_numeral M 2)n HMap HN').
Qed.

Print Assumptions source_pc_instance_substitution.
