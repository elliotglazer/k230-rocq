(** Raw subset formulas commute with actual numerical substitutions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution SourceOrdinalUpperMembers.
Unset Implicit Arguments.

Theorem source_oc_subset_substitution M x y subset x' y' out rb rc rn base :
  source_oc_subset_graph M x y subset ->substitution_lookup M rb rc rn base x x' ->
  substitution_lookup M rb rc rn base y y' ->source_oc_subset_graph M x' y' out ->
  numerical_substitution M subset rb rc rn base out.
Proof.
  intros (left&right&point&HL&HR&HP&HA) HX HY (left'&right'&point'&HL'&HR'&HP'&HA').
  destruct (substitution_lift_total M rb rc rn base) as (ab&ac&an&HMap).
  assert (HAtom:forall z z' a a',substitution_lookup M rb rc rn base z z' ->
      sf_relation M SFMember (zeroM M) (succM M z) a ->
      sf_relation M SFMember (zeroM M) (succM M z') a' ->
      numerical_substitution M a ab ac an (succM M base) a').
  { intros z z' a a' HZ HS HT.
    apply (proj2 (numerical_substitution_member M _ _ a ab ac an (succM M base) a' HS)).
    exists (zeroM M),(succM M z'). split;[exact (proj1 (proj2 HMap))|].
    split;[exact (proj2 (proj2 HMap) z z' HZ)|exact HT]. }
  apply (proj2 (numerical_substitution_quantifier M true point subset rb rc rn base out HA)).
  exists ab,ac,an,point'. split;[exact HMap|]. split;[|exact HA'].
  apply (proj2 (numerical_substitution_binary M SFImpl left right point ab ac an (succM M base)
    point' (or_intror (or_intror eq_refl)) HP)).
  exists left',right'. split;[exact (HAtom x x' left left' HX HL HL')|].
  split;[exact (HAtom y y' right right' HY HR HR')|exact HP'].
Qed.

Print Assumptions source_oc_subset_substitution.
