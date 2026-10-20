(** Existence of an App value, with actual source syntax transport and ExI. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionShiftGraphs SourceInstantiationConstructors.
Unset Implicit Arguments.
Definition source_rec_app_exists M f z out:=exists app,source_rec_app M(succM M f)(succM M z)(zeroM M)app /\sf_relation M SFEx app(zeroM M)out.
Theorem source_rec_app_exists_total M f z:exists out,source_rec_app_exists M f z out.
Proof.
 destruct(source_rec_app_total M(succM M f)(succM M z)(zeroM M))as(app&HA).
 destruct(sf_relation_total M SFEx app(zeroM M))as(out&HO). exists out,app. auto.
Qed.
Theorem source_rec_app_exists_bounded M f z out k:coding_lt M f k ->coding_lt M z k ->source_rec_app_exists M f z out ->source_bounded M out k.
Proof.
 intros BF BZ(app&HA&HO). apply(proj2(source_bounded_accept_unary M SFEx app out k(or_intror eq_refl)HO)).
 exact(source_rec_app_bounded M(succM M f)(succM M z)(zeroM M)app(succM M k)(proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M z k)BZ)(coding_zero_lt_succ M k)HA).
Qed.
Theorem source_rec_app_exists_substitution M f z old f' z' new rb rc rn base:
 source_rec_app_exists M f z old ->source_rec_app_exists M f' z' new ->substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base z z' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros(app&HA&HO)(app'&HA'&HO')HF HZ.
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false app old rb rc rn base new HO)). exists lb,lc,ln,app'. split;[exact HL|]. split;[|exact HO'].
 exact(source_rec_app_substitution M(succM M f)(succM M z)(zeroM M)app(succM M f')(succM M z')(zeroM M)app' lb lc ln(succM M base)HA HA'
  (proj2(proj2 HL)f f' HF)(proj2(proj2 HL)z z' HZ)(proj1(proj2 HL))).
Qed.
Theorem source_rec_app_exists_shift M f z old new:
 source_rec_app_exists M f z old ->source_rec_app_exists M(succM M f)(succM M z)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_app_exists_substitution M f z old(succM M f)(succM M z)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M f)(source_rec_shift_lookup M z)).
Qed.
Theorem source_full_rec_app_exists_intro M cb cc cn f z v app target k:
 coding_lt M f k ->coding_lt M z k ->context_bounded M cb cc cn k ->source_rec_app M f z v app ->source_rec_app_exists M f z target ->
 source_full_prv M cb cc cn app ->source_full_prv M cb cc cn target.
Proof.
 intros BF BZ BC HA HT PA. pose proof(source_rec_app_exists_bounded M f z target k BF BZ HT)as BT.
 destruct HT as(body&HB&HE). exact(full_source_ExI M cb cc cn body target v app(ex_intro _ k(conj BT BC))PA HE(source_rec_app_instantiation M f z body v app HB HA)).
Qed.
Print Assumptions source_rec_app_exists_total.
Print Assumptions source_rec_app_exists_bounded.
Print Assumptions source_rec_app_exists_substitution.
Print Assumptions source_rec_app_exists_shift.
Print Assumptions source_full_rec_app_exists_intro.
