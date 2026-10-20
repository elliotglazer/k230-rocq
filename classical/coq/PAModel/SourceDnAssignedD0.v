(** A fully assigned D0 recipe is literally the ordinary witness
    request for the assigned matrix, not a semantic replacement. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution SourceFiniteCutoffShift SourceD0Recipe SourceD0At
 SourceD0Substitution SourceHierarchySyntax SourceCBD0Canonical SourceDnAssignments SourceDnAssignedMatrix.
Unset Implicit Arguments.
Theorem source_dn_assigned_d0 M domain level count phi d0 pb pc d X ab ac ub uc un phi' result:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M count) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_d0_recipe M domain level phi d0 ->
 source_dn_assignment M count pb pc d X ab ac ->substitution_lift M pb pc count(zeroM M)ub uc un ->
 numerical_substitution M phi ub uc un(code_numeral M 1)phi' ->
 numerical_substitution M d0 ab ac(succM M(succM M count))(zeroM M)result ->
 source_d0_at M domain phi' d result.
Proof.
 intros HD HB HL HRecipe HA HU HP HResult.
 destruct(source_cutoff_shift_total M 1 phi)as(p1&H1).
 destruct(source_cutoff_shift_total M 1 p1)as(p2&H2).
 pose proof(source_cutoff_shift_bounded M 1 phi p1 count HB H1)as B1.
 pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M count)B1 H2)as B2.
 pose proof(proj1(source_d0_recipe_at_canonical M domain level phi p1 p2 d0 HL H1 H2)HRecipe)as HAt.
 destruct(substitution_lift_total M ab ac(succM M(succM M count))(zeroM M))as(lb&lc&ln&HLL).
 destruct(numerical_substitution_total M p2 lb lc ln(code_numeral M 1))as(theta&HTheta).
 pose proof(source_dn_assigned_matrix M count pb pc d X ab ac lb lc ln ub uc un phi p1 p2 theta
  HB H1 H2 HA HLL HU HTheta)as HPT.
 assert(E:theta=phi')by(eapply numerical_substitution_functional;eassumption). subst theta.
 destruct(source_d0_at_total M domain phi' d)as(other&HOther).
 pose proof(source_d0_at_substitution M domain p2 phi'(zeroM M)d d0 other
  (succM M(succM M(succM M count)))ab ac(succM M(succM M count))(zeroM M)lb lc ln
  HD B2 HLL HTheta(source_dn_assignment_zero M _ _ _ _ _ _ _ HA)HAt HOther)as HOtherSub.
 assert(E:other=result)by(eapply numerical_substitution_functional;eassumption). now subst other.
Qed.
Print Assumptions source_dn_assigned_d0.
