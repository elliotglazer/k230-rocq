(** Exact existential K-successor profile and actual ExI. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution NumericalInstantiation SubstitutionSource
 SourceQuantifierRules SourceInstantiationConstructors NumericalContexts NumericalSourceFull
 SourcePieceConjunctionBounds SourceReflectionKFWitness SourceReflectionKFWitnessTransport SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_reflection_KF_next M domain level sb sc n K x out:=exists body,
 source_reflection_KF_witness M domain level sb sc n(succM M K)(succM M x)(zeroM M)body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_reflection_KF_next_total M domain level sb sc n K x:exists out,source_reflection_KF_next M domain level sb sc n K x out.
Proof.
 destruct(source_reflection_KF_witness_total M domain level sb sc n(succM M K)(succM M x)(zeroM M))as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,body. auto.
Qed.
Theorem source_reflection_KF_next_bounded M domain level sb sc n K x out k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 coding_lt M K k ->coding_lt M x k ->source_reflection_KF_next M domain level sb sc n K x out ->source_bounded M out k.
Proof.
 intros HD HL HV BK BX(body&HB&HO). apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)).
 exact(source_reflection_KF_witness_bounded M domain level sb sc n(succM M K)(succM M x)(zeroM M)body(succM M k)HD HL HV
  (proj2(coding_lt_succ_cancel M K k)BK)(proj2(coding_lt_succ_cancel M x k)BX)(coding_zero_lt_succ M k)HB).
Qed.
Theorem source_reflection_KF_next_substitution M domain level sb sc n K x old K' x' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 source_reflection_KF_next M domain level sb sc n K x old ->source_reflection_KF_next M domain level sb sc n K' x' new ->
 substitution_lookup M rb rc rn base K K' ->substitution_lookup M rb rc rn base x x' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV(body&HB&HO)(body'&HB'&HO')HK HX. destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HMap|]. split;[|exact HO'].
 exact(source_reflection_KF_witness_substitution M domain level sb sc n(succM M K)(succM M x)(zeroM M)body(succM M K')(succM M x')(zeroM M)body'
  lb lc ln(succM M base)HD HL HV HB HB'(proj2(proj2 HMap)K K' HK)(proj2(proj2 HMap)x x' HX)(proj1(proj2 HMap))).
Qed.
Theorem source_reflection_KF_next_shift M domain level sb sc n K x old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->
 source_reflection_KF_next M domain level sb sc n K x old ->source_reflection_KF_next M domain level sb sc n(succM M K)(succM M x)new ->source_formula_shift M old new.
Proof.
 intros HD HL HV HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_reflection_KF_next_substitution M domain level sb sc n K x old(succM M K)(succM M x)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  HD HL HV HO HN(source_rec_shift_lookup M K)(source_rec_shift_lookup M x)).
Qed.
Theorem source_full_reflection_KF_next_intro M b c n domain level sb sc count K x w witness target k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 coding_lt M K k ->coding_lt M x k ->context_bounded M b c n k ->
 source_reflection_KF_witness M domain level sb sc count K x w witness ->source_reflection_KF_next M domain level sb sc count K x target ->
 source_full_prv M b c n witness ->source_full_prv M b c n target.
Proof.
 intros HD HL HV BK BX BC HW HT PW.
 pose proof(source_reflection_KF_next_bounded M domain level sb sc count K x target k HD HL HV BK BX HT)as BT.
 destruct HT as(body&HB&HEx). destruct(substitution_singleton_total M w)as(rb&rc&HHead&_).
 assert(HInst:numerical_instantiation M body w witness).
 { exists rb,rc. split;[exact HHead|]. exact(source_reflection_KF_witness_substitution M domain level sb sc count(succM M K)(succM M x)(zeroM M)body K x w witness
   rb rc(code_numeral M 1)(zeroM M)HD HL HV HB HW(substitution_singleton_tail M rb rc K)(substitution_singleton_tail M rb rc x)HHead). }
 exact(full_source_ExI M b c n body target w witness(ex_intro _ k(conj BT BC))PW HEx HInst).
Qed.
Print Assumptions source_reflection_KF_next_total.
Print Assumptions source_reflection_KF_next_bounded.
Print Assumptions source_reflection_KF_next_substitution.
Print Assumptions source_reflection_KF_next_shift.
Print Assumptions source_full_reflection_KF_next_intro.
