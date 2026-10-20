(** The literal App/G conjunction carried by a predecessor witness. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport
 SourceRecursionShiftGraphs SourceRecursionAttemptStepShell SourceRecursionAgreementPoints SourceRecursionFunctionality
 SourcePieceBoundMaxJoint NumericalContexts NumericalSourceFull.
Unset Implicit Arguments.
Definition source_rec_value_pair M phi f z u v out:=exists app binary,
 source_rec_app M f z u app /\source_rec_binary M phi u v binary /\sf_relation M SFAnd app binary out.
Theorem source_rec_value_pair_total M phi f z u v:exists out,source_rec_value_pair M phi f z u v out.
Proof.
 destruct(source_rec_app_total M f z u)as(app&HA). destruct(source_rec_binary_total M phi u v)as(binary&HG).
 destruct(sf_relation_total M SFAnd app binary)as(out&HO). exists out,app,binary. auto.
Qed.
Theorem source_rec_value_pair_bounded M phi f z u v out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M f k ->coding_lt M z k ->coding_lt M u k ->coding_lt M v k ->
 source_rec_value_pair M phi f z u v out ->source_bounded M out k.
Proof.
 intros BP BF BZ BU BV(app&binary&HA&HG&HO).
 exact(proj2(source_bounded_accept_binary M SFAnd app binary out k(or_introl eq_refl)HO)
  (conj(source_rec_app_bounded M f z u app k BF BZ BU HA)(source_rec_binary_bounded M phi u v binary k BP BU BV HG))).
Qed.
Theorem source_rec_value_pair_substitution M phi f z u v out f' z' u' v' out' rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_value_pair M phi f z u v out ->source_rec_value_pair M phi f' z' u' v' out' ->
 substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base z z' ->
 substitution_lookup M rb rc rn base u u' ->substitution_lookup M rb rc rn base v v' ->numerical_substitution M out rb rc rn base out'.
Proof.
 intros BP(app&binary&HA&HG&HO)(app'&binary'&HA'&HG'&HO')HF HZ HU HV.
 apply(proj2(numerical_substitution_binary M SFAnd app binary out rb rc rn base out'(or_introl eq_refl)HO)).
 exists app',binary'. repeat split;try assumption.
 - exact(source_rec_app_substitution M f z u app f' z' u' app' rb rc rn base HA HA' HF HZ HU).
 - exact(source_rec_binary_substitution_graph M phi u v binary u' v' binary' rb rc rn base BP HG HG' HU HV).
Qed.
Theorem source_rec_value_pair_shift M phi f z u v out out':
 source_bounded M phi(code_numeral M 2) ->source_rec_value_pair M phi f z u v out ->
 source_rec_value_pair M phi(succM M f)(succM M z)(succM M u)(succM M v)out' ->source_formula_shift M out out'.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M out(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)out')).
 rewrite Arithmetic.add_zero. exact(source_rec_value_pair_substitution M phi f z u v out
  (succM M f)(succM M z)(succM M u)(succM M v)out'(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  BP HO HN(source_rec_shift_lookup M f)(source_rec_shift_lookup M z)(source_rec_shift_lookup M u)(source_rec_shift_lookup M v)).
Qed.
Theorem source_rec_transition_witness_bounded M phi f z v out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->
 source_rec_transition_witness M phi f z v out ->source_bounded M out k.
Proof.
 intros BP BF BZ BV(app&binary&body&HA&HG&HB&HE).
 apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HE)).
 apply(source_rec_value_pair_bounded M phi(succM M f)(succM M z)(zeroM M)(succM M v)body(succM M k)BP).
 - apply FiniteCRT.coding_lt_succ_cancel. exact BF.
 - apply FiniteCRT.coding_lt_succ_cancel. exact BZ.
 - apply coding_zero_lt_succ.
 - apply FiniteCRT.coding_lt_succ_cancel. exact BV.
 - exists app,binary. auto.
Qed.
Print Assumptions source_rec_value_pair_total.
Print Assumptions source_rec_value_pair_bounded.
Print Assumptions source_rec_value_pair_substitution.
Print Assumptions source_rec_value_pair_shift.
Print Assumptions source_rec_transition_witness_bounded.
