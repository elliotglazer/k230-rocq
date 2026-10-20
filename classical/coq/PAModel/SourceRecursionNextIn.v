(** Literal existence of a next G-value in a named carrier, with actual source rules. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution NumericalInstantiation SubstitutionSource
 SourceQuantifierRules SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport SourceRecursionShiftGraphs
 SourceInstantiationConstructors SourceTracePointRules NumericalContexts NumericalSourceFull SourceTraceBounds.
Unset Implicit Arguments.
Definition source_rec_next_in M phi v Y out:=exists binary member body,
 source_rec_binary M phi(succM M v)(zeroM M)binary /\sf_relation M SFMember(zeroM M)(succM M Y)member /\
 sf_relation M SFAnd binary member body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_next_in_total M phi v Y:exists out,source_rec_next_in M phi v Y out.
Proof.
 destruct(source_rec_binary_total M phi(succM M v)(zeroM M))as(binary&HB).
 destruct(sf_relation_total M SFMember(zeroM M)(succM M Y))as(member&HM).
 destruct(sf_relation_total M SFAnd binary member)as(body&HBody).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,binary,member,body. auto.
Qed.
Theorem source_rec_next_in_bounded M phi v Y out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M v k ->coding_lt M Y k ->source_rec_next_in M phi v Y out ->source_bounded M out k.
Proof.
 intros BP BV BY(binary&member&body&HB&HM&HBody&HO).
 pose proof(source_rec_binary_bounded M phi(succM M v)(zeroM M)binary(succM M k)BP(proj2(coding_lt_succ_cancel M v k)BV)(coding_zero_lt_succ M k)HB)as BB.
 pose proof(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M Y)member(succM M k)(or_introl eq_refl)HM)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M Y k)BY)))as BM.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)(proj2(source_bounded_accept_binary M SFAnd binary member body(succM M k)(or_introl eq_refl)HBody)(conj BB BM))).
Qed.
Theorem source_rec_next_in_substitution M phi v Y old v' Y' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_next_in M phi v Y old ->source_rec_next_in M phi v' Y' new ->
 substitution_lookup M rb rc rn base v v' ->substitution_lookup M rb rc rn base Y Y' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(binary&member&body&HB&HM&HBody&HO)(binary'&member'&body'&HB'&HM'&HBody'&HO')HV HY.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HL|]. split;[|exact HO'].
 apply(proj2(numerical_substitution_binary M SFAnd binary member body lb lc ln(succM M base)body'(or_introl eq_refl)HBody)). exists binary',member'.
 split;[|split;[|exact HBody']].
 - exact(source_rec_binary_substitution_graph M phi(succM M v)(zeroM M)binary(succM M v')(zeroM M)binary' lb lc ln(succM M base)BP HB HB'(proj2(proj2 HL)v v' HV)(proj1(proj2 HL))).
 - apply(proj2(numerical_substitution_member M _ _ member lb lc ln(succM M base)member' HM)). exists(zeroM M),(succM M Y'). exact(conj(proj1(proj2 HL))(conj(proj2(proj2 HL)Y Y' HY)HM')).
Qed.
Theorem source_rec_next_in_shift M phi v Y old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_next_in M phi v Y old ->source_rec_next_in M phi(succM M v)(succM M Y)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_next_in_substitution M phi v Y old(succM M v)(succM M Y)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M v)(source_rec_shift_lookup M Y)).
Qed.
Theorem source_full_rec_next_in_intro M cb cc cn phi v Y w binary member target k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M v k ->coding_lt M Y k ->context_bounded M cb cc cn k ->
 source_rec_binary M phi v w binary ->sf_relation M SFMember w Y member ->source_rec_next_in M phi v Y target ->
 source_full_prv M cb cc cn binary ->source_full_prv M cb cc cn member ->source_full_prv M cb cc cn target.
Proof.
 intros BP BV BY BC HB HM HT PB PM.
 pose proof(source_rec_next_in_bounded M phi v Y target k BP BV BY HT)as BT.
 destruct HT as(binary0&member0&body&HB0&HM0&HBody&HEx).
 destruct(sf_relation_total M SFAnd binary member)as(instance&HInstance).
 destruct(substitution_singleton_total M w)as(rb&rc&HHead&_).
 assert(HInstB:numerical_instantiation M binary0 w binary).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_binary_substitution_graph M phi(succM M v)(zeroM M)binary0 v w binary rb rc(code_numeral M 1)(zeroM M)BP HB0 HB(substitution_singleton_tail M rb rc v)HHead). }
 pose proof(source_instantiation_binary M SFAnd binary0 member0 body w binary member instance(or_introl eq_refl)HBody HInstB
  (source_instantiation_head_member M Y member0 w member HM0 HM)HInstance)as HInst.
 assert(PInstance:source_full_prv M cb cc cn instance).
 { exact(full_source_CI M cb cc cn binary member instance(source_wf_binary M cb cc cn SFAnd binary member instance(or_introl eq_refl)HInstance
  (source_full_prv_wellformed M cb cc cn binary PB)(source_full_prv_wellformed M cb cc cn member PM))PB PM HInstance). }
 exact(full_source_ExI M cb cc cn body target w instance(ex_intro _ k(conj BT BC))PInstance HEx HInst).
Qed.
Print Assumptions source_rec_next_in_total.
Print Assumptions source_rec_next_in_bounded.
Print Assumptions source_rec_next_in_substitution.
Print Assumptions source_rec_next_in_shift.
Print Assumptions source_full_rec_next_in_intro.
