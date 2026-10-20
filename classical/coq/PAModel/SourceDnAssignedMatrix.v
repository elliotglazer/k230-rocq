(** Literal matrix cancellation for the two inserted D0 roles followed
    by an internally finite parameter assignment. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution SourceBounded SourceBoundedMapComposition
 SourceSubstitutionComposition SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceDnAssignments.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_dn_assigned_matrix M count pb pc d X ab ac lb lc ln ub uc un phi p1 p2 out:
 source_bounded M phi(succM M count) ->source_cutoff_shift M 1 phi p1 ->source_cutoff_shift M 1 p1 p2 ->
 source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 substitution_lift M pb pc count(zeroM M)ub uc un ->
 numerical_substitution M p2 lb lc ln(code_numeral M 1)out ->
 numerical_substitution M phi ub uc un(code_numeral M 1)out.
Proof.
 intros HB(a&b&n&HA&HS1)(c&e&m&HC&HS2)HAssign HL HU HOut.
 destruct(numerical_substitution_composition_total M phi(succM M count)
  a b n(code_numeral M 2)c e m(code_numeral M 2)p1 p2 HB HS1 HS2)as(cb&cc&HCombined&HLookup).
 apply(numerical_substitution_composition M phi(succM M count)
  cb cc(succM M count)(zeroM M)lb lc ln(code_numeral M 1)ub uc un(code_numeral M 1)p2 out HB HCombined HOut).
 intros i j v HI HJ HV. apply(proj1(HLookup i j HI))in HJ. destruct HJ as(mid&HFirst&HSecond).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - assert(E:mid=zeroM M)by(eapply substitution_lookup_functional;[exact HFirst|
   exact(source_cutoff_shift_map_fixed_lookup M 1 a b n HA 0)]). subst mid.
   assert(E:j=zeroM M)by(eapply substitution_lookup_functional;[exact HSecond|
   exact(source_cutoff_shift_map_fixed_lookup M 1 c e m HC 0)]). subst j.
   apply(proj1(substitution_lift_head M _ _ _ _ _ _ _ _ HL))in HV. subst v.
   exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HU)eq_refl).
 - assert(HIdx:coding_lt M idx count)by(exact(proj1(coding_lt_succ_cancel M idx count)HI)).
   assert(E:mid=succM M(succM M idx))by(eapply substitution_lookup_functional;[exact HFirst|
    exact(source_cutoff_shift_map_tail_lookup M 1 a b n idx HA)]). subst mid.
   assert(E:j=succM M(succM M(succM M idx)))by(eapply substitution_lookup_functional;[exact HSecond|
    exact(source_cutoff_shift_map_tail_lookup M 1 c e m(succM M idx)HC)]). subst j.
   destruct(beta_total M pb pc idx)as(value&HValue).
   assert(E:v=succM M value).
   { eapply substitution_lookup_functional;[exact HV|].
     apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
     exact(proj2(source_dn_assignment_parameter M _ _ _ _ _ _ _ _ _ HAssign HIdx)HValue). } subst v.
   apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HU)).
   exact(proj2(substitution_lookup_inside M pb pc count(zeroM M)idx value HIdx)HValue).
Qed.
Print Assumptions source_dn_assigned_matrix.
