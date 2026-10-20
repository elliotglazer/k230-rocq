(** Insert the second external ordinal name without changing the source matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalSubstitutionMaps NumericalSubstitution
  SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceQfFunctionality SourceD0At SourceD0Substitution
  SourceD0Instances SourceD0OrdinalInsertions SourceCBD0Canonical SourceD0Recipe SourceCutoffQuantifiers SourceCBD0Canonical SourceHierarchySyntax SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_d0_at_cutoff_two M domain phi phi' out shifted k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi k ->
  source_cutoff_shift M 3 phi phi' ->source_d0_at M domain phi(zeroM M) out ->
  source_cutoff_shift M 2 out shifted ->source_d0_at M domain phi'(zeroM M) shifted.
Proof.
  intros HD HB HC HG(sb&sc&sn&HM&HS).
  destruct(substitution_lift_total M sb sc sn(code_numeral M 3)) as(ab&ac&an&HL).
  assert(HM2:source_cutoff_shift_map M 3 ab ac an) by(exists sb,sc,sn;auto).
  destruct HC as(rb&rc&rn&HRM&HMatrix).
  assert(HP:numerical_substitution M phi ab ac an(code_numeral M 4) phi').
  { exact(proj1(numerical_substitution_extensional M phi rb rc rn ab ac an(code_numeral M 4) phi'
      (source_cutoff_shift_maps_equivalent M 3 rb rc rn ab ac an HRM HM2)) HMatrix). }
  destruct(source_d0_at_total M domain phi'(zeroM M)) as(next&HN).
  pose proof(source_d0_at_substitution M domain phi phi'(zeroM M)(zeroM M) out next k
    sb sc sn(code_numeral M 3) ab ac an HD HB HL HP
    (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HM 0) HG HN) as HNext.
  pose proof(numerical_substitution_functional M out sb sc sn(code_numeral M 3) next shifted HNext HS) as E.
  now subst next.
Qed.


(** The D0 payload has no assignment-container role. Thus inserting a
    carrier before or after that unused role gives the same actual code. *)
Theorem source_d0_carrier_insertions_equal M domain level phi d0 before after k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_d0_recipe M domain level phi d0 ->
  source_cutoff_shift M 2 d0 before ->source_cutoff_shift M 1 d0 after ->before=after.
Proof.
  intros HD HB HL HD0 HBefore HAfter.
  destruct(source_cutoff_shift_total M 1 phi)as(p1&H1).
  destruct(source_cutoff_shift_total M 1 p1)as(p2&H2).
  destruct(source_cutoff_shift_total M 1 p2)as(p3&H3).
  pose proof(source_cutoff_shift_bounded M 1 phi p1 k HB H1)as B1.
  pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M k)B1 H2)as B2.
  assert(H12:source_cutoff_shift M 2 p1 p2).
  { destruct(source_cutoff_shift_total M 2 p1)as(q&HQ).
    pose proof(source_cutoff_one_two_commute M phi p1 p1 q(succM M k)HB H1 H1 HQ)as HSame.
    pose proof(source_cutoff_shift_functional M 1 p1 q p2 HSame H2)as E. now subst q. }
  assert(H23:source_cutoff_shift M 2 p2 p3).
  { destruct(source_cutoff_shift_total M 2 p2)as(q&HQ).
    pose proof(source_cutoff_one_two_commute M p1 p2 p2 q(succM M(succM M k))B1 H2 H2 HQ)as HSame.
    pose proof(source_cutoff_shift_functional M 1 p2 q p3 HSame H3)as E. now subst q. }
  assert(H33:source_cutoff_shift M 3 p2 p3).
  { destruct(source_cutoff_shift_total M 3 p2)as(q&HQ).
    pose proof(source_cutoff_two_three_commute M p1 p2 p2 q(succM M(succM M k))B1 H12 H12 HQ)as HSame.
    pose proof(source_cutoff_shift_functional M 2 p2 q p3 HSame H23)as E. now subst q. }
  pose proof(proj1(source_d0_recipe_at_canonical M domain level phi p1 p2 d0 HL H1 H2)HD0)as HAt.
  pose proof(source_d0_at_cutoff_one M domain p2 p3 d0 after(succM M(succM M(succM M k)))HD B2 H23 HAt HAfter)as HAtAfter.
  pose proof(source_d0_at_cutoff_two M domain p2 p3 d0 before(succM M(succM M(succM M k)))HD B2 H33 HAt HBefore)as HAtBefore.
  exact(source_d0_at_functional M domain p3(zeroM M)before after HAtBefore HAtAfter).
Qed.

Print Assumptions source_d0_at_cutoff_two.
Print Assumptions source_d0_carrier_insertions_equal.
