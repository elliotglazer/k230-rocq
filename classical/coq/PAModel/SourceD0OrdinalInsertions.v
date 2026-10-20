(** Insert the second external ordinal name without changing the source matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceQfFunctionality SourceD0At SourceD0Substitution
  SourceD0Instances SourceD0Recipe SourceCBD0Canonical SourceHierarchySyntax SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_d0_at_cutoff_one M domain phi phi' out shifted k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 2 phi phi' ->source_d0_at M domain phi(zeroM M) out ->
  source_cutoff_shift M 1 out shifted ->source_d0_at M domain phi'(zeroM M) shifted.
Proof.
  intros HD HB HC HG(sb&sc&sn&HM&HS).
  destruct(substitution_lift_total M sb sc sn(code_numeral M 2)) as(ab&ac&an&HL).
  assert(HM2:source_cutoff_shift_map M 2 ab ac an) by(exists sb,sc,sn;auto).
  destruct HC as(rb&rc&rn&HRM&HMatrix).
  assert(HP:numerical_substitution M phi ab ac an(code_numeral M 3) phi').
  { exact(proj1(numerical_substitution_extensional M phi rb rc rn ab ac an(code_numeral M 3) phi'
      (source_cutoff_shift_maps_equivalent M 2 rb rc rn ab ac an HRM HM2)) HMatrix). }
  destruct(source_d0_at_total M domain phi'(zeroM M)) as(next&HN).
  pose proof(source_d0_at_substitution M domain phi phi'(zeroM M)(zeroM M) out next k
    sb sc sn(code_numeral M 2) ab ac an HD HB HL HP
    (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HM 0) HG HN) as HNext.
  pose proof(numerical_substitution_functional M out sb sc sn(code_numeral M 2) next shifted HNext HS) as E.
  now subst next.
Qed.

Theorem source_d0_recipe_ordinal_insertions M domain level phi p1 p2 p3 d0 da db k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  source_LL_instance M(code_numeral M 1)(zeroM M) level ->
  source_cutoff_shift M 1 phi p1 ->source_cutoff_shift M 1 p1 p2 ->source_cutoff_shift M 1 p2 p3 ->
  source_d0_recipe M domain level phi d0 ->source_formula_shift M d0 da ->source_cutoff_shift M 1 d0 db ->
  source_d0_at M domain p3(code_numeral M 1) da /\source_d0_at M domain p3(zeroM M) db.
Proof.
  intros HD HB HL H1 H2 H3 HG HDA HDB.
  pose proof(proj1(source_d0_recipe_at_canonical M domain level phi p1 p2 d0 HL H1 H2) HG) as HAt.
  pose proof(source_cutoff_shift_bounded M 1 phi p1 k HB H1) as BP1.
  pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M k) BP1 H2) as BP2.
  split.
  - exact(source_d0_at_shift M domain p2 p3(zeroM M) d0 da (succM M(succM M(succM M k))) HD BP2 H3 HAt HDA).
  - destruct(source_cutoff_shift_total M 2 p2) as(q&HQ).
    pose proof(source_cutoff_one_two_commute M p1 p2 p2 q (succM M(succM M k)) BP1 H2 H2 HQ) as HQ1.
    pose proof(source_cutoff_shift_functional M 1 p2 q p3 HQ1 H3) as E. subst q.
    exact(source_d0_at_cutoff_one M domain p2 p3 d0 db(succM M(succM M(succM M k))) HD BP2 HQ HAt HDB).
Qed.

Print Assumptions source_d0_at_cutoff_one.
Print Assumptions source_d0_recipe_ordinal_insertions.
