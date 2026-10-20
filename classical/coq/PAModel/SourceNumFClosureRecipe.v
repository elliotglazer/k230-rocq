(** PA-definable literal numeral-in-closure statement. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceBoundMonotone SchemaConstructorBounds SourcePropositionalRebase
 SourceDefinabilityPrimitives SourceNumFClosureSyntax SourceRepresentationClosureRecipe
 SourceClosureNumeralsOld SourceClosureNumeralsFixed SourceNumFClosureSuccessorPointFixed
 SourceDefinabilitySuccessor OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_base Z_cl.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition numf_closure_succ_code M :=code_numeral M(sf_encode source_def_successor01).
Definition numf_closure_condition_code M :=code_numeral M(sf_encode representation_closure_condition).
Definition numf_closure_statement_expression :code_expr :=E_sf SFImpl(CEconst(sf_encode source_def_successor01))
 (E_sf SFImpl(CEconst(sf_encode representation_closure_condition))
 (E_sf SFEx(E_sf SFAnd(CEvar 0)(CEconst(sf_make SFMember 0 3)))(CEconst 0))).
Definition source_numf_closure_statement M f out :=code_relation M(fun _=>f)numf_closure_statement_expression out.
Definition source_numf_closure_statement_formula(f out:pa_term):pa_form :=
 code_formula numf_closure_statement_expression(fun _=>f)out.
Local Opaque code_numeral source_def_successor01 representation_closure_condition.
Theorem source_numf_closure_statement_formula_correct M rho f out :
 holds M rho(source_numf_closure_statement_formula f out) <->
 source_numf_closure_statement M(evalM M rho f)(evalM M rho out).
Proof. unfold source_numf_closure_statement_formula,source_numf_closure_statement. rewrite code_formula_correct. reflexivity. Qed.
Theorem source_numf_closure_statement_total M f :exists out,source_numf_closure_statement M f out.
Proof. apply code_relation_total. Qed.
Theorem source_numf_closure_statement_functional M f out other :
 source_numf_closure_statement M f out ->source_numf_closure_statement M f other ->out=other.
Proof. apply code_relation_functional. Qed.
Theorem source_numf_closure_statement_parts M f out :source_numf_closure_statement M f out ->
 exists body ex middle,source_numf_member_shell M f 3 body ex /\
 sf_relation M SFImpl(numf_closure_condition_code M)ex middle /\
 sf_relation M SFImpl(numf_closure_succ_code M)middle out.
Proof.
 intro H. unfold source_numf_closure_statement,numf_closure_statement_expression in H.
 destruct(schema_expression_split M(fun _=>f)_ _ _ out H)as(s&middle&HS&HM&HO).
 change(s=numf_closure_succ_code M)in HS. subst s.
 destruct(schema_expression_split M(fun _=>f)_ _ _ middle HM)as(c&ex&HC&HE&HI).
 change(c=numf_closure_condition_code M)in HC. subst c.
 destruct(schema_expression_split M(fun _=>f)_ _ _ ex HE)as(body&unused&HB&HU&HEx).
 change(unused=zeroM M)in HU. subst unused.
 destruct(schema_expression_split M(fun _=>f)_ _ _ body HB)as(p&m&HP&HMemb&HAnd).
 change(p=f)in HP. subst p. change(m=source_numf_closure_member M 3)in HMemb. subst m.
 exists body,ex,middle. exact(conj(conj HAnd HEx)(conj HI HO)).
Qed.
Lemma source_numf_code_join M rho h A B a b out :
 code_relation M rho A a ->code_relation M rho B b ->sf_relation M h a b out ->
 code_relation M rho(E_sf h A B)out.
Proof. intros HA HB HO. exact(proj2(schema_expression_graph M rho h A B a b out HA HB)HO). Qed.
Theorem source_numf_closure_statement_join M f body ex middle out :
 source_numf_member_shell M f 3 body ex ->
 sf_relation M SFImpl(numf_closure_condition_code M)ex middle ->
 sf_relation M SFImpl(numf_closure_succ_code M)middle out ->source_numf_closure_statement M f out.
Proof.
 intros(HB&HE)HM HO. unfold source_numf_closure_statement,numf_closure_statement_expression.
 eapply source_numf_code_join;[reflexivity| |exact HO].
 eapply source_numf_code_join;[reflexivity| |exact HM].
 eapply source_numf_code_join;[|reflexivity|exact HE].
 eapply source_numf_code_join;[reflexivity|reflexivity|exact HB].
Qed.
Local Transparent code_numeral.
Theorem source_numf_closure_statement_bounded M f out :source_bounded M f(code_numeral M 1) ->
 source_numf_closure_statement M f out ->source_bounded M out(code_numeral M 3).
Proof.
 intros BF H. destruct(source_numf_closure_statement_parts M f out H)as(body&ex&middle&(HB&HE)&HM&HO).
 assert(BF4:source_bounded M f(code_numeral M 4)).
 { apply(source_bounded_monotone M f(code_numeral M 1)(code_numeral M 4)BF).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(BM:source_bounded M(source_numf_closure_member M 3)(code_numeral M 4)).
 { apply source_numf_closure_member_bounded;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd f _ body(code_numeral M 4)(or_introl eq_refl)HB)(conj BF4 BM))as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex(code_numeral M 3)(or_intror eq_refl)HE)BBody)as BEx.
 assert(BC:source_bounded M(numf_closure_condition_code M)(code_numeral M 3)).
 { apply source_formula_numeral_bounded,representation_closure_finite_bound. }
 assert(BS:source_bounded M(numf_closure_succ_code M)(code_numeral M 3)).
 { apply(source_bounded_monotone M _(code_numeral M 2)(code_numeral M 3)(numerical_def_successor_bound M)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 exact(proj2(source_bounded_accept_binary M SFImpl _ middle out(code_numeral M 3)(or_intror(or_intror eq_refl))HO)
  (conj BS(proj2(source_bounded_accept_binary M SFImpl _ ex middle(code_numeral M 3)(or_intror(or_intror eq_refl))HM)(conj BC BEx)))).
Qed.
Print Assumptions source_numf_closure_statement_formula_correct.
Print Assumptions source_numf_closure_statement_bounded.
