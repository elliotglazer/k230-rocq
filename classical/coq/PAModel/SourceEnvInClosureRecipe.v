(** Literal EnvF-in-C statement with arbitrary internal parameter count.
    Parameters occupy3,...,n+2; A,S,C occupy0,1,2. The graph contains
    numerical syntax only. Actual proof production is separate. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent NumericalProofs
 SourceBounded SourceBoundMonotone SourceNumeralLift SourceDefinabilityPrimitives SourceDefinabilityBounds
 SourceFiniteCutoffShift SourceQfFunctionality SourceMembershipBlocks SourceMembershipBlockProofs
 SourceRepresentationClosureRecipe SourceNumFClosureRecipe SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition env_in_closure_values {A}(block shifted:A)i:=match i with 0=>block|_=>shifted end.
Definition E_env_in_closure:=E_sf SFImpl(CEconst(sf_encode source_def_successor01))
 (E_sf SFImpl(CEconst(sf_encode representation_closure_condition))
  (E_sf SFImpl(CEvar 0)(E_sf SFEx
   (E_sf SFAnd(CEvar 1)(CEconst(sf_make SFMember 0 3)))(CEconst 0)))).
Definition source_env_in_closure_recipe M count environment out:=exists block first second shifted,
 source_membership_block M(code_numeral M 3)(zeroM M)count block /\
 source_cutoff_shift M 1 environment first /\source_cutoff_shift M 1 first second /\
 source_cutoff_shift M 1 second shifted /\
 code_relation M(env_in_closure_values block shifted)E_env_in_closure out.
Definition eic_lift4(t:term):=t`[↑]`[↑]`[↑]`[↑].
Definition source_env_in_closure_recipe_formula(count environment out:term):form:=∃∃∃∃(
 source_membership_block_formula(num 3)zero(eic_lift4 count)$3 ∧
 (source_cutoff_shift_formula 1(eic_lift4 environment)$2 ∧
 (source_cutoff_shift_formula 1 $2 $1 ∧
 (source_cutoff_shift_formula 1 $1 $0 ∧
 code_formula E_env_in_closure(env_in_closure_values $3 $0)(eic_lift4 out))))).
Lemma eic_eval_lift4 M rho a b c d t:evalM M(d.:c.:b.:a.:rho)(eic_lift4 t)=evalM M rho t.
Proof. unfold eic_lift4,evalM. now rewrite !eval_up. Qed.
Local Opaque holds source_membership_block_formula source_cutoff_shift_formula code_formula.
Theorem source_env_in_closure_recipe_formula_correct M rho count environment out:
 holds M rho(source_env_in_closure_recipe_formula count environment out)<->
 source_env_in_closure_recipe M(evalM M rho count)(evalM M rho environment)(evalM M rho out).
Proof.
 unfold source_env_in_closure_recipe_formula,source_env_in_closure_recipe.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_membership_block_formula_correct. setoid_rewrite source_cutoff_shift_formula_correct.
 setoid_rewrite code_formula_correct. setoid_rewrite eic_eval_lift4. repeat setoid_rewrite code_eval_num.
 split;intros(block&first&second&shifted&HB&H1&H2&H3&HO);exists block,first,second,shifted;
 refine(conj HB(conj H1(conj H2(conj H3 _))));exact HO.
Qed.
Theorem source_env_in_closure_recipe_total M count environment:
 exists out,source_env_in_closure_recipe M count environment out.
Proof.
 destruct(source_membership_block_total M(code_numeral M 3)(zeroM M)count)as(block&HB).
 destruct(source_cutoff_shift_total M 1 environment)as(first&H1).
 destruct(source_cutoff_shift_total M 1 first)as(second&H2).
 destruct(source_cutoff_shift_total M 1 second)as(shifted&H3).
 destruct(code_relation_total M E_env_in_closure(env_in_closure_values block shifted))as(out&HO).
 exists out,block,first,second,shifted. exact(conj HB(conj H1(conj H2(conj H3 HO)))).
Qed.
Theorem source_env_in_closure_recipe_functional M count environment f g:
 source_env_in_closure_recipe M count environment f->source_env_in_closure_recipe M count environment g->f=g.
Proof.
 intros(b&a&c&d&HB&HA&HC&HD&HF)(b'&a'&c'&d'&HB'&HA'&HC'&HD'&HG).
 assert(b=b')by(eapply source_membership_block_functional;eassumption). subst b'.
 assert(a=a')by(eapply source_cutoff_shift_functional;eassumption). subst a'.
 assert(c=c')by(eapply source_cutoff_shift_functional;eassumption). subst c'.
 assert(d=d')by(eapply source_cutoff_shift_functional;eassumption). subst d'.
 eapply code_relation_functional;eassumption.
Qed.
Theorem source_env_in_closure_recipe_bounded M count environment out:
 source_envf M count environment->source_env_in_closure_recipe M count environment out->
 source_bounded M out(succM M(succM M(succM M count))).
Proof.
 intros HE(block&first&second&shifted&HB&H1&H2&H3&HO).
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as B1.
 pose proof(source_cutoff_shift_bounded M 1 first second(succM M count)B1 H2)as B2.
 pose proof(source_cutoff_shift_bounded M 1 second shifted(succM M(succM M count))B2 H3)as B3.
 assert(BBlock:source_bounded M block(succM M(succM M(succM M count)))).
 { apply(source_membership_block_bound M(code_numeral M 3)(zeroM M)count block _);try assumption.
   - intros i HI. rewrite(Arithmetic.add_comm M i(code_numeral M 3)).
     change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M)))) i)(succM M(succM M(succM M count)))).
     rewrite!Arithmetic.add_succ,Arithmetic.add_zero. do 3 apply coding_lt_succ_cancel. exact HI.
   - apply coding_zero_lt_succ. }
 assert(BSucc:source_bounded M(code_numeral M(sf_encode source_def_successor01))(succM M(succM M(succM M count)))).
 { apply(source_bounded_monotone M _(code_numeral M 2)_(numerical_def_successor_bound M)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BCl:source_bounded M(code_numeral M(sf_encode representation_closure_condition))(succM M(succM M(succM M count)))).
 { apply(source_bounded_monotone M _(code_numeral M 3) _).
   - apply source_formula_numeral_bounded,representation_closure_finite_bound.
   - do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(B:schema_expression_bound M(env_in_closure_values block shifted)E_env_in_closure(succM M(succM M(succM M count)))).
 { unfold E_env_in_closure.
   apply schema_expression_binary;[unfold sf_binary;auto| |].
   - intros f EF. change(f=code_numeral M(sf_encode source_def_successor01))in EF. now subst f.
   - apply schema_expression_binary;[unfold sf_binary;auto| |].
     + intros f EF. change(f=code_numeral M(sf_encode representation_closure_condition))in EF. now subst f.
     + apply schema_expression_binary;[unfold sf_binary;auto|apply schema_expression_variable;exact BBlock|].
       apply schema_expression_unary;[unfold sf_unary;auto|].
       apply schema_expression_binary;[unfold sf_binary;auto|apply schema_expression_variable;exact B3|].
       intros f EF. change(f=code_numeral M(sf_make SFMember 0 3))in EF. subst f.
       apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)_
        (succM M(succM M(succM M(succM M count))))(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
       split;schema_small_index. }
 exact(B out HO).
Qed.
Print Assumptions source_env_in_closure_recipe_formula_correct.
Print Assumptions source_env_in_closure_recipe_total.
Print Assumptions source_env_in_closure_recipe_functional.
Print Assumptions source_env_in_closure_recipe_bounded.
