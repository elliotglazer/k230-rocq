(** Actual totality and witness specialization of an arbitrary internal binary relation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenaming RenamingSubstitution SubstitutionSource
 SourceRecursionBinaryInstance SourceRecursionBinaryTransport SourceRecursionBinaryGraphTransport SourceRecursionShiftGraphs SourceQuantifierRules
 SourceTraceBounds SourceInstantiationConstructors NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.
Definition source_rec_relation_witness M phi v out:=exists body,
 source_rec_binary M phi(succM M v)(zeroM M)body /\sf_relation M SFEx body(zeroM M)out.
Definition source_rec_total_relation M phi out:=exists witness,
 source_rec_relation_witness M phi(zeroM M)witness /\sf_relation M SFAll witness(zeroM M)out.
Theorem source_rec_relation_witness_total M phi v:exists out,source_rec_relation_witness M phi v out.
Proof.
 destruct(source_rec_binary_total M phi(succM M v)(zeroM M))as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,body. auto.
Qed.
Theorem source_rec_total_relation_total M phi:exists out,source_rec_total_relation M phi out.
Proof.
 destruct(source_rec_relation_witness_total M phi(zeroM M))as(witness&HW).
 destruct(sf_relation_total M SFAll witness(zeroM M))as(out&HO). exists out,witness. auto.
Qed.
Theorem source_rec_relation_witness_bounded M phi v out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M v k ->source_rec_relation_witness M phi v out ->source_bounded M out k.
Proof.
 intros BP BV(body&HB&HO). apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)).
 exact(source_rec_binary_bounded M phi(succM M v)(zeroM M)body(succM M k)BP(proj2(coding_lt_succ_cancel M v k)BV)(coding_zero_lt_succ M k)HB).
Qed.
Theorem source_rec_total_relation_closed M phi out:
 source_bounded M phi(code_numeral M 2) ->source_rec_total_relation M phi out ->source_bounded M out(zeroM M).
Proof.
 intros BP(witness&HW&HO). apply(proj2(source_bounded_accept_unary M SFAll witness out(zeroM M)(or_introl eq_refl)HO)).
 exact(source_rec_relation_witness_bounded M phi(zeroM M)witness(succM M(zeroM M))BP(coding_zero_lt_succ M(zeroM M))HW).
Qed.
Theorem source_rec_relation_witness_substitution M phi v old v' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_relation_witness M phi v old ->source_rec_relation_witness M phi v' new ->
 substitution_lookup M rb rc rn base v v' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(body&HB&HO)(body'&HB'&HO')HV. destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HL|]. split;[|exact HO'].
 exact(source_rec_binary_substitution_graph M phi(succM M v)(zeroM M)body(succM M v')(zeroM M)body' lb lc ln(succM M base)BP HB HB'(proj2(proj2 HL)v v' HV)(proj1(proj2 HL))).
Qed.
Theorem source_rec_relation_witness_shift M phi v old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_relation_witness M phi v old ->source_rec_relation_witness M phi(succM M v)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_relation_witness_substitution M phi v old(succM M v)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M v)).
Qed.
Theorem source_full_rec_total_relation_use M cb cc cn phi total v out:
 source_bounded M phi(code_numeral M 2) ->source_rec_total_relation M phi total ->source_rec_relation_witness M phi v out ->
 source_full_prv M cb cc cn total ->source_full_prv M cb cc cn out.
Proof.
 intros BP(witness&HW&HAll)HOut PTotal.
 destruct(substitution_singleton_total M v)as(rb&rc&HHead&_).
 assert(HInst:numerical_instantiation M witness v out).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_relation_witness_substitution M phi(zeroM M)witness v out rb rc(code_numeral M 1)(zeroM M)BP HW HOut HHead). }
 exact(full_source_AllE M cb cc cn witness total v out(source_wf_quantifier_instance M cb cc cn SFAll witness total v out(or_introl eq_refl)HAll
  (source_full_prv_wellformed M cb cc cn total PTotal)HInst)PTotal HAll HInst).
Qed.
Print Assumptions source_rec_relation_witness_total.
Print Assumptions source_rec_total_relation_total.
Print Assumptions source_rec_relation_witness_bounded.
Print Assumptions source_rec_total_relation_closed.
Print Assumptions source_rec_relation_witness_substitution.
Print Assumptions source_rec_relation_witness_shift.
Print Assumptions source_full_rec_total_relation_use.
