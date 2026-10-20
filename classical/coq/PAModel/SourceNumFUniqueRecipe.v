(** Literal canonical uniqueness assertion for an internally coded unary matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceQuantifierRules NumericalRenaming SourceNumFClosureRecipe
 SourceImplicationAllShift SourcePropositionalRebase SchemaConstructorBounds SourceNumeralLift.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition numf_equal01 M :=code_numeral M(sf_make SFEqual 0 1).
Definition numf_unique_expression :=E_sf SFImpl(CEvar 0)(E_sf SFImpl(CEvar 1)(CEconst(sf_make SFEqual 0 1))).
Definition source_numf_unique_recipe M p out :=exists ps,
 source_formula_shift M p ps /\code_relation M(sf_env p ps)numf_unique_expression out.
Definition source_numf_unique_recipe_formula(p out:term):form :=∃(
 source_formula_shift_formula p`[↑] $0 ∧code_formula numf_unique_expression(sf_env p`[↑] $0)out`[↑]).
Lemma numf_unique_eval_env M rho x p idx :
 evalM M(x.:rho)(sf_env p`[↑] $0 idx)=sf_env(evalM M rho p)x idx.
Proof. destruct idx as[|idx];cbn[sf_env];[unfold evalM;now rewrite eval_up|reflexivity]. Qed.
Local Opaque holds source_formula_shift_formula code_formula.
Theorem source_numf_unique_recipe_formula_correct M rho p out :
 holds M rho(source_numf_unique_recipe_formula p out)<->source_numf_unique_recipe M(evalM M rho p)(evalM M rho out).
Proof.
 unfold source_numf_unique_recipe_formula,source_numf_unique_recipe.
 setoid_rewrite NumericalProofs.holds_ex. setoid_rewrite NumericalProofs.holds_and.
 setoid_rewrite source_formula_shift_formula_correct. setoid_rewrite code_formula_correct.
 unfold evalM. repeat setoid_rewrite eval_up.
 split;intros(ps&HS&HO);exists ps;split;[exact HS| |exact HS|].
 - apply(proj1(code_relation_ext M numf_unique_expression
    (fun idx=>evalM M(ps.:rho)(sf_env p`[↑] $0 idx))
    (sf_env(evalM M rho p)ps)(evalM M rho out)(numf_unique_eval_env M rho ps p))). exact HO.
 - apply(proj2(code_relation_ext M numf_unique_expression
    (fun idx=>evalM M(ps.:rho)(sf_env p`[↑] $0 idx))
    (sf_env(evalM M rho p)ps)(evalM M rho out)(numf_unique_eval_env M rho ps p))). exact HO.
Qed.
Theorem source_numf_unique_recipe_total M p :exists out,source_numf_unique_recipe M p out.
Proof.
 destruct(numerical_renaming_total M p(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(ps&HS).
 destruct(code_relation_total M numf_unique_expression(sf_env p ps))as(out&HO). exists out,ps. auto.
Qed.
Theorem source_numf_unique_recipe_functional M p f g :source_numf_unique_recipe M p f ->source_numf_unique_recipe M p g ->f=g.
Proof.
 intros(ps&HS&HF)(pt&HT&HG).
 assert(E:pt=ps)by(eapply numerical_renaming_functional;eassumption). subst pt.
 eapply code_relation_functional;eassumption.
Qed.
Theorem source_numf_unique_recipe_parts M p out :source_numf_unique_recipe M p out ->exists ps inner,
 source_formula_shift M p ps /\sf_relation M SFImpl ps(numf_equal01 M)inner /\sf_relation M SFImpl p inner out.
Proof.
 intros(ps&HS&HO). unfold numf_unique_expression in HO.
 destruct(schema_expression_split M(sf_env p ps)_ _ _ out HO)as(a&inner&HA&HI&HOut).
 change(a=p)in HA. subst a.
 destruct(schema_expression_split M(sf_env p ps)_ _ _ inner HI)as(b&e&HB&HE&HInner).
 change(b=ps)in HB. subst b. change(e=numf_equal01 M)in HE. subst e.
 exists ps,inner. auto.
Qed.
Theorem source_numf_unique_recipe_join M p ps inner out :source_formula_shift M p ps ->
 sf_relation M SFImpl ps(numf_equal01 M)inner ->sf_relation M SFImpl p inner out ->source_numf_unique_recipe M p out.
Proof.
 intros HS HI HO. exists ps. split;[exact HS|]. unfold numf_unique_expression.
 eapply source_numf_code_join;[reflexivity| |exact HO].
 eapply source_numf_code_join;[reflexivity|reflexivity|exact HI].
Qed.
Theorem source_numf_unique_recipe_bounded M p out :source_bounded M p(code_numeral M 1) ->
 source_numf_unique_recipe M p out ->source_bounded M out(code_numeral M 2).
Proof.
 intros BP H. destruct(source_numf_unique_recipe_parts M p out H)as(ps&inner&HS&HI&HO).
 pose proof(source_shift_bound M p ps(code_numeral M 1)BP HS)as BPS.
 assert(BP2:source_bounded M p(code_numeral M 2)).
 { apply(source_bounded_monotone M p(code_numeral M 1)(code_numeral M 2)BP). apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(BE:source_bounded M(numf_equal01 M)(code_numeral M 2)).
 { exact(proj2(source_bounded_accept_atom M SFEqual(zeroM M)(code_numeral M 1)_(code_numeral M 2)(or_intror eq_refl)
    (sf_make_numeral M SFEqual 0 1))(conj(coding_zero_lt_succ M(code_numeral M 1))(coding_lt_succ M(code_numeral M 1)))). }
 exact(proj2(source_bounded_accept_binary M SFImpl p inner out(code_numeral M 2)(or_intror(or_intror eq_refl))HO)
  (conj BP2(proj2(source_bounded_accept_binary M SFImpl ps _ inner(code_numeral M 2)(or_intror(or_intror eq_refl))HI)(conj BPS BE)))).
Qed.
Print Assumptions source_numf_unique_recipe_formula_correct.
Print Assumptions source_numf_unique_recipe_bounded.
