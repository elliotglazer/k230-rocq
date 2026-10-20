(** Literal existence of a larger member of K and actual ExI. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution NumericalInstantiation SubstitutionSource
 SourceQuantifierRules SourceInstantiationConstructors SourceTracePointRules NumericalContexts NumericalSourceFull SourceNamedProofRules SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_reflection_no_last_next M K x out:=exists member next body,
 sf_relation M SFMember(zeroM M)(succM M K)member /\sf_relation M SFMember(succM M x)(zeroM M)next /\
 sf_relation M SFAnd member next body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_reflection_no_last_next_total M K x:exists out,source_reflection_no_last_next M K x out.
Proof.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M K))as(member&HM).
 destruct(sf_relation_total M SFMember(succM M x)(zeroM M))as(next&HN).
 destruct(sf_relation_total M SFAnd member next)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,member,next,body. auto.
Qed.
Theorem source_reflection_no_last_next_bounded M K x out k:
 coding_lt M K k ->coding_lt M x k ->source_reflection_no_last_next M K x out ->source_bounded M out k.
Proof.
 intros BK BX(m&t&body&HM&HT&HB&HO).
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ m(succM M k)(or_introl eq_refl)HM)(conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M K k)BK)))as BM.
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ t(succM M k)(or_introl eq_refl)HT)(conj(proj2(coding_lt_succ_cancel M x k)BX)(coding_zero_lt_succ M k)))as BT.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)(proj2(source_bounded_accept_binary M SFAnd m t body(succM M k)(or_introl eq_refl)HB)(conj BM BT))).
Qed.
Theorem source_reflection_no_last_next_substitution M K x old K' x' new rb rc rn base:
 source_reflection_no_last_next M K x old ->source_reflection_no_last_next M K' x' new ->
 substitution_lookup M rb rc rn base K K' ->substitution_lookup M rb rc rn base x x' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros(m&t&body&HM&HT&HB&HO)(m'&t'&body'&HM'&HT'&HB'&HO')HK HX.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 assert(SM:numerical_substitution M m lb lc ln(succM M base)m').
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M K)m lb lc ln(succM M base)m' HM)). exists(zeroM M),(succM M K'). exact(conj(proj1(proj2 HMap))(conj(proj2(proj2 HMap)K K' HK)HM')). }
 assert(ST:numerical_substitution M t lb lc ln(succM M base)t').
 { apply(proj2(numerical_substitution_member M(succM M x)(zeroM M)t lb lc ln(succM M base)t' HT)). exists(succM M x'),(zeroM M). exact(conj(proj2(proj2 HMap)x x' HX)(conj(proj1(proj2 HMap))HT')). }
 assert(SB:numerical_substitution M body lb lc ln(succM M base)body').
 { apply(proj2(numerical_substitution_binary M SFAnd m t body lb lc ln(succM M base)body'(or_introl eq_refl)HB)). exists m',t'. auto. }
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. auto.
Qed.
Theorem source_reflection_no_last_next_shift M K x old new:
 source_reflection_no_last_next M K x old ->source_reflection_no_last_next M(succM M K)(succM M x)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_reflection_no_last_next_substitution M K x old(succM M K)(succM M x)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M K)(source_rec_shift_lookup M x)).
Qed.
Theorem source_full_reflection_no_last_next_intro M b c n K x w member next target k:
 coding_lt M K k ->coding_lt M x k ->context_bounded M b c n k ->sf_relation M SFMember w K member ->sf_relation M SFMember x w next ->
 source_reflection_no_last_next M K x target ->source_full_prv M b c n member ->source_full_prv M b c n next ->source_full_prv M b c n target.
Proof.
 intros BK BX BC HM HT HTarget PM PT.
 pose proof(source_reflection_no_last_next_bounded M K x target k BK BX HTarget)as BT.
 destruct HTarget as(m0&t0&body&HM0&HT0&HB0&HEx).
 destruct(sf_relation_total M SFAnd member next)as(instance&HI).
 destruct(substitution_singleton_total M w)as(rb&rc&HHead&_).
 assert(IM:numerical_instantiation M m0 w member)by(exact(source_instantiation_head_member M K m0 w member HM0 HM)).
 assert(IT:numerical_instantiation M t0 w next).
 { exists rb,rc. split;[exact HHead|]. apply(proj2(numerical_substitution_member M(succM M x)(zeroM M)t0 rb rc(code_numeral M 1)(zeroM M)next HT0)).
   exists x,w. exact(conj(substitution_singleton_tail M rb rc x)(conj HHead HT)). }
 pose proof(source_instantiation_binary M SFAnd m0 t0 body w member next instance(or_introl eq_refl)HB0 IM IT HI)as IBody.
 exact(full_source_ExI M b c n body target w instance(ex_intro _ k(conj BT BC))(source_full_and_intro M b c n member next instance HI PM PT)HEx IBody).
Qed.
Print Assumptions source_reflection_no_last_next_total.
Print Assumptions source_reflection_no_last_next_bounded.
Print Assumptions source_reflection_no_last_next_substitution.
Print Assumptions source_reflection_no_last_next_shift.
Print Assumptions source_full_reflection_no_last_next_intro.
