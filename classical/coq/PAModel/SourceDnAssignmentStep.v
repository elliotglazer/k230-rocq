(** Actual rotation/lifting/instantiation square for one Dn parameter. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 RenamingSubstitution SubstitutionSource SourceDnStep SourceDnAssignments SourceBoundedMapComposition
 SourceSubstitutionComposition SourceBounded.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Lemma source_dn_assignment_step_lookup M count pb pc head tb tc d X ab ac fb fc lb lc ln ib ic i j l v:
 environment_cons M tb tc count head pb pc(succM M count) ->
 source_dn_assignment M count tb tc d X ab ac ->
 source_dn_assignment M(succM M count)pb pc d X fb fc ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 substitution_lookup M ib ic(code_numeral M 1)(zeroM M)(zeroM M)head ->
 coding_lt M i(succM M(succM M(succM M count))) ->
 renaming_lookup M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)i j ->
 substitution_lookup M lb lc ln(code_numeral M 1)j l ->
 substitution_lookup M ib ic(code_numeral M 1)(zeroM M)l v ->
 substitution_lookup M fb fc(succM M(succM M(succM M count)))(zeroM M)i v.
Proof.
 intros HT HA HF HL HI HB HR HJ HV.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[q E]];subst i.
 - assert(E:j=code_numeral M 1)by(eapply renaming_lookup_functional;[exact HR|apply source_dn_rotate_zero]). subst j.
   assert(EL:l=succM M d).
   { eapply substitution_lookup_functional;[exact HJ|].
     apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
     exact(source_dn_assignment_zero M _ _ _ _ _ _ _ HA). }
   subst l. assert(E:v=d)by(eapply substitution_lookup_functional;[exact HV|apply substitution_singleton_tail]).
   subst v. exact(source_dn_assignment_zero M _ _ _ _ _ _ _ HF).
 - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)q)as[E|[r E]];subst q.
   + assert(E:j=code_numeral M 2)by(eapply renaming_lookup_functional;[exact HR|apply source_dn_rotate_one]). subst j.
     assert(EL:l=succM M X).
     { eapply substitution_lookup_functional;[exact HJ|].
       apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
       exact(source_dn_assignment_one M _ _ _ _ _ _ _ HA). }
     subst l. assert(E:v=X)by(eapply substitution_lookup_functional;[exact HV|apply substitution_singleton_tail]).
     subst v. exact(source_dn_assignment_one M _ _ _ _ _ _ _ HF).
   + destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)r)as[E|[s E]];subst r.
     * assert(E:j=zeroM M)by(eapply renaming_lookup_functional;[exact HR|apply source_dn_rotate_two]). subst j.
       assert(EL:l=zeroM M)by(exact(proj1(substitution_lift_head M _ _ _ _ _ _ _ _ HL)HJ)). subst l.
       assert(E:v=head)by(eapply substitution_lookup_functional;eassumption). subst v.
       apply(proj2(source_dn_assignment_parameter M _ _ _ _ _ _ _ _ _ HF(coding_zero_lt_succ M count))).
       apply(proj1(environment_lookup_inside M pb pc(succM M count)(zeroM M)head(coding_zero_lt_succ M count))).
       exact(proj2(environment_cons_head M _ _ _ _ _ _ _ _ HT)eq_refl).
     * assert(HS:coding_lt M s count).
       { apply(proj1(coding_lt_succ_cancel M s count)).
         apply(proj1(coding_lt_succ_cancel M(succM M s)(succM M count))).
         exact(proj1(coding_lt_succ_cancel M(succM M(succM M s))(succM M(succM M count)))HB). }
       assert(E:j=succM M(succM M(succM M s))).
       { eapply renaming_lookup_functional;[exact HR|]. apply source_dn_rotate_outside.
         intro HH. apply(coding_not_lt_zero M s).
         apply(proj1(coding_lt_succ_cancel M s(zeroM M))).
         apply(proj1(coding_lt_succ_cancel M(succM M s)(code_numeral M 1))).
         exact(proj1(coding_lt_succ_cancel M(succM M(succM M s))(code_numeral M 2))HH). }
       subst j. destruct(beta_total M tb tc s)as(w&HW).
       assert(EL:l=succM M w).
       { eapply substitution_lookup_functional;[exact HJ|].
         apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
         exact(proj2(source_dn_assignment_parameter M _ _ _ _ _ _ _ _ _ HA HS)HW). }
       subst l. assert(E:v=w)by(eapply substitution_lookup_functional;[exact HV|apply substitution_singleton_tail]). subst v.
       apply(proj2(source_dn_assignment_parameter M _ _ _ _ _ _ _ _ _ HF(proj2(coding_lt_succ_cancel M s count)HS))).
       apply(proj1(environment_lookup_inside M pb pc(succM M count)(succM M s)w(proj2(coding_lt_succ_cancel M s count)HS))).
       apply(proj2(environment_cons_tail M _ _ _ _ _ _ _ _ _ HT)).
       exact(proj2(environment_lookup_inside M tb tc count s w HS)HW).
Qed.
Theorem source_dn_assignment_step_substitution M count pb pc head tb tc d X ab ac fb fc lb lc ln ib ic
 body rotated reopened result:
 environment_cons M tb tc count head pb pc(succM M count) ->
 source_dn_assignment M count tb tc d X ab ac ->source_dn_assignment M(succM M count)pb pc d X fb fc ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 substitution_lookup M ib ic(code_numeral M 1)(zeroM M)(zeroM M)head ->
 source_bounded M body(succM M(succM M(succM M count))) ->
 numerical_renaming M body(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)rotated ->
 numerical_substitution M rotated lb lc ln(code_numeral M 1)reopened ->
 numerical_substitution M reopened ib ic(code_numeral M 1)(zeroM M)result ->
 numerical_substitution M body fb fc(succM M(succM M(succM M count)))(zeroM M)result.
Proof.
 intros HT HA HF HL HI HB HR HReopen HResult.
 pose proof(proj1(numerical_renaming_substitution M body _ _ _ _ rotated)HR)as HRS.
 rewrite coding_add_zero_r in HRS.
 destruct(numerical_substitution_composition_total M body(succM M(succM M(succM M count)))
  (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(code_numeral M 3)
  lb lc ln(code_numeral M 1)rotated reopened HB HRS HReopen)as(cb&cc&HC&HLK).
 apply(numerical_substitution_composition M body(succM M(succM M(succM M count)))
  cb cc(succM M(succM M(succM M count)))(zeroM M)ib ic(code_numeral M 1)(zeroM M)
  fb fc(succM M(succM M(succM M count)))(zeroM M)reopened result HB HC HResult).
 intros i l v HBound HLookup HFinal.
 apply(proj1(HLK i l HBound))in HLookup. destruct HLookup as(j&HRotate&HLift).
 apply(source_dn_assignment_step_lookup M count pb pc head tb tc d X ab ac fb fc lb lc ln ib ic i j l v
  HT HA HF HL HI HBound);try assumption.
 apply(proj2(renaming_substitution_lookup M _ _ _ _ _ _)).
 rewrite coding_add_zero_r. exact HRotate.
Qed.
Print Assumptions source_dn_assignment_step_lookup.
Print Assumptions source_dn_assignment_step_substitution.
