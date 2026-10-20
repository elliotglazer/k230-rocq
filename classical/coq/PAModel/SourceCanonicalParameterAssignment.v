(** An actual canonical parameter table and head-cons assignment agree
    with representative-only renaming on the whole internal matrix bound. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming RenamingSubstitution
 SourceBallSMembershipBlock SourceRepresentativeRenaming SourceSubstitutionComposition SourceSubstitutionIdentity SourceShiftSpecialization.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_canonical_parameter_assignment_total M count value:
 exists pb pc vb vc,balls_offset_assignment M(code_numeral M 1)count pb pc /\
 environment_cons M pb pc count value vb vc(succM M count).
Proof.
 destruct(balls_offset_assignment_total M(code_numeral M 1)count)as(pb&pc&HP).
 destruct(environment_cons_total M pb pc count value)as(vb&vc&vn&HV).
 pose proof(proj1 HV)as E. subst vn. exists pb,pc,vb,vc. auto.
Qed.

Theorem source_canonical_parameter_assignment M count pb pc value vb vc phi assigned:
 source_bounded M phi(succM M count) ->balls_offset_assignment M(code_numeral M 1)count pb pc ->
 environment_cons M pb pc count value vb vc(succM M count) ->
 source_representative_renaming M value phi assigned ->
 numerical_substitution M phi vb vc(succM M count)(zeroM M)assigned.
Proof.
 intros HP HOffset HCons HRep.
 assert(HIdentity:numerical_substitution M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)phi).
 { apply(numerical_substitution_identity_on_bound M phi(zeroM M)(zeroM M)(zeroM M)(zeroM M)(succM M count)HP).
   intros i _. apply source_empty_substitution_lookup. }
 assert(HRepSub:numerical_substitution M phi value value(code_numeral M 1)(code_numeral M 1)assigned).
 { apply(proj1(numerical_renaming_substitution M phi value value(code_numeral M 1)(zeroM M)assigned))in HRep.
   now rewrite coding_add_zero_r in HRep. }
 apply(numerical_substitution_composition M phi(succM M count)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)value value(code_numeral M 1)(code_numeral M 1)
  vb vc(succM M count)(zeroM M)phi assigned HP HIdentity HRepSub).
 intros i j v HI HJ HV.
 assert(EJ:j=i)by(exact(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(zeroM M)i j i HJ(source_empty_substitution_lookup M i))).
 subst j.
 assert(RMap:representative_lookup M value i v).
 { apply(proj2(renaming_substitution_lookup M value value(code_numeral M 1)(zeroM M)i v)).
   now rewrite coding_add_zero_r. }
 apply(proj2(substitution_lookup_inside M vb vc(succM M count)(zeroM M)i v HI)).
 apply(proj1(environment_lookup_inside M vb vc(succM M count)i v HI)).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
  as[EI|[idx EI]];subst i.
 - assert(EV:v=value)by(exact(renaming_lookup_functional M value value(code_numeral M 1)(zeroM M)(zeroM M)v value RMap(representative_lookup_zero M value))).
   subst v. exact(proj2(environment_cons_head M pb pc count value vb vc(succM M count)value HCons)eq_refl).
 - assert(EV:v=succM M idx).
   { eapply renaming_lookup_functional;[exact RMap|]. apply representative_lookup_nonzero.
     intro E. symmetry in E. exact(Model.zero_ne_succ M idx E). }
   subst v. apply(proj2(environment_cons_tail M pb pc count value vb vc(succM M count)idx(succM M idx)HCons)).
   pose proof(proj1(coding_lt_succ_cancel M idx count)HI)as HIdx.
   apply(proj2(environment_lookup_inside M pb pc count idx(succM M idx)HIdx)).
   apply(proj2(HOffset idx(succM M idx)HIdx)).
   change(succM M idx=addM M idx(succM M(zeroM M))).
   rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.
Print Assumptions source_canonical_parameter_assignment_total.
Print Assumptions source_canonical_parameter_assignment.
