(** A real Pc proof yields the ordinary assigned-matrix witness request.
    Dn guards, the hierarchy-set binder and their substitutions are all
    eliminated by actual source derivations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SourceBounded SetFormulaCodes
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalSourceFull
 SourceHierarchySyntax SourcePieceClosure SourceD0Recipe SourceD0At SourceD0Specialization SourceEwMonotone
 SourceDnAssignments SourceDnAssignedD0 SourceDnEliminationInvariant SourceDnElimination.
Unset Implicit Arguments.
Theorem source_full_pc_parameter_witness M domain level count phi d X pc pb pC ub uc un phi' Y lev ew
 gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->
 source_bounded M phi(succM M count) ->source_bounded M phi' k ->
 source_pc_instance M domain level count phi d X pc ->
 substitution_lift M pb pC count(zeroM M)ub uc un ->
 numerical_substitution M phi ub uc un(code_numeral M 1)phi' ->
 source_dn_parameter_proofs M count pb pC X gb gc gn ->
 source_LL_instance M d Y lev ->source_ew_at M domain phi' Y ew ->
 source_full_prv M gb gc gn pc ->source_full_prv M gb gc gn lev ->source_full_prv M gb gc gn ew.
Proof.
 intros HD HL HLg HB HB'(d0&dn&rb&rc&H0&HN&HR&HPC)HU HMatrix HMembers HLev HEw PP PL.
 pose proof(source_d0_recipe_bounded M domain level phi d0 count HD HL HB H0)as HD0B.
 destruct(source_dn_assignment_total M count pb pC d X)as(ab&ac&HA).
 destruct(numerical_substitution_total M d0 ab ac(succM M(succM M count))(zeroM M))as(result&HResult).
 pose proof(source_full_dn_elimination M count d0 dn d X rb rc pc pb pC ab ac result gb gc gn
  HD0B HN HR HPC HA HResult PP HMembers)as PResult.
 pose proof(source_dn_assigned_d0 M domain level count phi d0 pb pC d X ab ac ub uc un phi' result
  HD HB HLg H0 HA HU HMatrix HResult)as HAt.
 exact(source_full_d0_at_specialization M gb gc gn domain phi' d result Y lev ew k HD HB' HAt HLev HEw PResult PL).
Qed.
Print Assumptions source_full_pc_parameter_witness.
