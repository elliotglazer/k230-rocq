(** The literal carrier-existence conclusion of the generic recursion theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution NumericalInstantiation SubstitutionSource
 NumericalContexts NumericalSourceFull SourceRecursionClosureSyntax SourceRecursionClosureTransport SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Definition source_rec_closure_exists M phi a out:=exists body,
 source_rec_closure M phi(succM M a)(zeroM M)body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_closure_exists_total M phi a:exists out,source_rec_closure_exists M phi a out.
Proof.
 destruct(source_rec_closure_total M phi(succM M a)(zeroM M))as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,body. auto.
Qed.
Theorem source_rec_closure_exists_functional M phi a x y:
 source_rec_closure_exists M phi a x ->source_rec_closure_exists M phi a y ->x=y.
Proof.
 intros(body&HB&HX)(body'&HB'&HY).
 pose proof(source_rec_closure_functional M phi(succM M a)(zeroM M)body' body HB' HB)as E. subst body'.
 exact(sf_relation_functional M SFEx body(zeroM M)x y HX HY).
Qed.
Theorem source_rec_closure_exists_bounded M phi a out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M a k ->source_rec_closure_exists M phi a out ->source_bounded M out k.
Proof.
 intros BP BA(body&HB&HO). apply(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)).
 exact(source_rec_closure_bounded M phi(succM M a)(zeroM M)body(succM M k)BP(proj2(coding_lt_succ_cancel M a k)BA)(coding_zero_lt_succ M k)HB).
Qed.
Theorem source_rec_closure_exists_substitution M phi a old a' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_exists M phi a old ->source_rec_closure_exists M phi a' new ->
 substitution_lookup M rb rc rn base a a' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(body&HB&HO)(body'&HB'&HO')HA. destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HL).
 apply(proj2(numerical_substitution_quantifier M false body old rb rc rn base new HO)). exists lb,lc,ln,body'. split;[exact HL|]. split;[|exact HO'].
 exact(source_rec_closure_substitution M phi(succM M a)(zeroM M)body(succM M a')(zeroM M)body' lb lc ln(succM M base)BP HB HB'(proj2(proj2 HL)a a' HA)(proj1(proj2 HL))).
Qed.
Theorem source_rec_closure_exists_shift M phi a old new:
 source_bounded M phi(code_numeral M 2) ->source_rec_closure_exists M phi a old ->source_rec_closure_exists M phi(succM M a)new ->source_formula_shift M old new.
Proof.
 intros BP HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_rec_closure_exists_substitution M phi a old(succM M a)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M a)).
Qed.
Theorem source_full_rec_closure_exists_intro M cb cc cn phi a Y body target k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M a k ->context_bounded M cb cc cn k ->
 source_rec_closure M phi a Y body ->source_rec_closure_exists M phi a target ->source_full_prv M cb cc cn body ->source_full_prv M cb cc cn target.
Proof.
 intros BP BA BC HB HT PB. pose proof(source_rec_closure_exists_bounded M phi a target k BP BA HT)as BT.
 destruct HT as(oldBody&HOldBody&HEx). destruct(substitution_singleton_total M Y)as(rb&rc&HHead&_).
 assert(HInst:numerical_instantiation M oldBody Y body).
 { exists rb,rc. split;[exact HHead|]. exact(source_rec_closure_substitution M phi(succM M a)(zeroM M)oldBody a Y body rb rc(code_numeral M 1)(zeroM M)BP HOldBody HB(substitution_singleton_tail M rb rc a)HHead). }
 exact(full_source_ExI M cb cc cn oldBody target Y body(ex_intro _ k(conj BT BC))PB HEx HInst).
Qed.
Print Assumptions source_rec_closure_exists_total.
Print Assumptions source_rec_closure_exists_functional.
Print Assumptions source_rec_closure_exists_bounded.
Print Assumptions source_rec_closure_exists_substitution.
Print Assumptions source_rec_closure_exists_shift.
Print Assumptions source_full_rec_closure_exists_intro.
