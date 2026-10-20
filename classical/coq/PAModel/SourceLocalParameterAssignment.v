(** Actual internally finite table [A,S,C,parameters], with no external
    choice function on the model. Three checked cons operations suffice. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalEnvironments
 NumericalSubstitutionMaps NumericalRenamingMaps SourceDnAssignments.
Unset Implicit Arguments.
Definition source_local_role_length M count:=succM M(succM M(succM M count)).
Definition source_local_role_assignment M count pb pc A S C rb rc:=exists cb cc,
 environment_cons M pb pc count C cb cc(succM M count) /\
 source_dn_assignment M(succM M count)cb cc A S rb rc.
Theorem source_local_role_assignment_total M count pb pc A S C:exists rb rc,
 source_local_role_assignment M count pb pc A S C rb rc.
Proof.
 destruct(environment_cons_total M pb pc count C)as(cb&cc&cn&HC). pose proof(proj1 HC)as E. subst cn.
 destruct(source_dn_assignment_total M(succM M count)cb cc A S)as(rb&rc&HD).
 exists rb,rc,cb,cc. auto.
Qed.
Lemma source_local_role_zero M count pb pc A S C rb rc:
 source_local_role_assignment M count pb pc A S C rb rc ->
 renaming_lookup M rb rc(source_local_role_length M count)(zeroM M)(zeroM M)A.
Proof.
 intros(cb&cc&HC&HD). unfold source_local_role_length.
 apply(proj2(renaming_lookup_inside M rb rc _ _ _ _ (coding_zero_lt_succ M(succM M(succM M count))))).
 exact(proj1(substitution_lookup_inside M rb rc _ (zeroM M)(zeroM M)A(coding_zero_lt_succ M(succM M(succM M count))))
  (source_dn_assignment_zero M(succM M count)cb cc A S rb rc HD)).
Qed.
Lemma source_local_role_one M count pb pc A S C rb rc:
 source_local_role_assignment M count pb pc A S C rb rc ->
 renaming_lookup M rb rc(source_local_role_length M count)(zeroM M)(code_numeral M 1)S.
Proof.
 intros(cb&cc&HC&HD). unfold source_local_role_length.
 assert(HI:coding_lt M(code_numeral M 1)(succM M(succM M(succM M count)))).
 { apply(proj2(coding_lt_succ_cancel M _ _)),coding_zero_lt_succ. }
 apply(proj2(renaming_lookup_inside M rb rc _ _ _ _ HI)).
 exact(proj1(substitution_lookup_inside M rb rc _ (zeroM M)(code_numeral M 1)S HI)
  (source_dn_assignment_one M(succM M count)cb cc A S rb rc HD)).
Qed.
Lemma source_local_role_two M count pb pc A S C rb rc:
 source_local_role_assignment M count pb pc A S C rb rc ->
 renaming_lookup M rb rc(source_local_role_length M count)(zeroM M)(code_numeral M 2)C.
Proof.
 intros(cb&cc&HC&HD). unfold source_local_role_length.
 assert(HI:coding_lt M(code_numeral M 2)(succM M(succM M(succM M count)))).
 { do 2 apply(proj2(coding_lt_succ_cancel M _ _)). apply coding_zero_lt_succ. }
 apply(proj2(renaming_lookup_inside M rb rc _ _ _ _ HI)).
 apply(proj1(substitution_lookup_inside M rb rc _ (zeroM M)(code_numeral M 2)C HI)).
 apply(proj2(source_dn_assignment_parameter M(succM M count)cb cc A S rb rc(zeroM M)C HD(coding_zero_lt_succ M count))).
 apply(proj1(environment_lookup_inside M cb cc(succM M count)(zeroM M)C(coding_zero_lt_succ M count))).
 exact(proj2(environment_cons_head M pb pc count C cb cc(succM M count)C HC)eq_refl).
Qed.
Lemma source_local_role_parameter M count pb pc A S C rb rc i value:
 source_local_role_assignment M count pb pc A S C rb rc ->coding_lt M i count ->beta M pb pc i value ->
 renaming_lookup M rb rc(source_local_role_length M count)(zeroM M)(succM M(succM M(succM M i)))value.
Proof.
 intros(cb&cc&HC&HD)HI HV. unfold source_local_role_length.
 assert(HBound:coding_lt M(succM M(succM M(succM M i)))(succM M(succM M(succM M count)))).
 { do 3 apply(proj2(coding_lt_succ_cancel M _ _)). exact HI. }
 apply(proj2(renaming_lookup_inside M rb rc _ _ _ _ HBound)).
 apply(proj1(substitution_lookup_inside M rb rc _ (zeroM M)(succM M(succM M(succM M i)))value HBound)).
 apply(proj2(source_dn_assignment_parameter M(succM M count)cb cc A S rb rc(succM M i)value HD
  (proj2(coding_lt_succ_cancel M i count)HI))).
 apply(proj1(environment_lookup_inside M cb cc(succM M count)(succM M i)value
  (proj2(coding_lt_succ_cancel M i count)HI))).
 apply(proj2(environment_cons_tail M pb pc count C cb cc(succM M count)i value HC)).
 exact(proj2(environment_lookup_inside M pb pc count i value HI)HV).
Qed.
Print Assumptions source_local_role_assignment_total.
Print Assumptions source_local_role_zero.
Print Assumptions source_local_role_one.
Print Assumptions source_local_role_two.
Print Assumptions source_local_role_parameter.
