(** A genuine PA formula for the closure-container representation graph.
    The graph contains syntax only, with no proof-output condition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceNumeralLift SourceRepresentationRecipe SourceRepresentationClosureRecipe
 SourceRepresentationFalsityClosure SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_representation_in_closure_recipe_formula(n phi result:term):form :=∃∃∃∃∃∃(
 source_representation_recipe_formula(rep_lift6 n)(rep_lift6 phi) $5 ∧
 (code_formula representation_successor_expression(fun index => num index) $4 ∧
 (code_formula representation_closure_expression(fun index => num index) $3 ∧
 (sf_formula SFAnd(num(sf_make SFMember 0 3)) $5 $2 ∧
 (sf_formula SFEx $2 zero $1 ∧
 (sf_formula SFImpl $3 $1 $0 ∧sf_formula SFImpl $4 $0(rep_lift6 result))))))).
Local Opaque holds source_representation_recipe_formula code_formula sf_formula.
Theorem source_representation_in_closure_recipe_formula_correct M rho n phi result :
 holds M rho(source_representation_in_closure_recipe_formula n phi result) <->
 source_representation_in_closure_recipe M(evalM M rho n)(evalM M rho phi)(evalM M rho result).
Proof.
 unfold source_representation_in_closure_recipe_formula,source_representation_in_closure_recipe.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_representation_recipe_formula_correct. setoid_rewrite code_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite rep_eval_lift6. repeat setoid_rewrite code_eval_num.
 split;intros(rep&succ&closure&body&ex&middle&HR&HS&HC&HB&HE&HM&HO);
  exists rep,succ,closure,body,ex,middle;refine(conj HR(conj _(conj _(conj HB(conj HE(conj HM HO)))))).
 - apply(proj1(code_relation_ext M representation_successor_expression
    (fun index => evalM M(middle .:ex .:body .:closure .:succ .:rep .:rho)(num index))
    (representation_identity_environment M) succ ltac:(intro i;apply code_eval_num))). exact HS.
 - apply(proj1(code_relation_ext M representation_closure_expression
    (fun index => evalM M(middle .:ex .:body .:closure .:succ .:rep .:rho)(num index))
    (representation_identity_environment M) closure ltac:(intro i;apply code_eval_num))). exact HC.
 - apply(proj2(code_relation_ext M representation_successor_expression
    (fun index => evalM M(middle .:ex .:body .:closure .:succ .:rep .:rho)(num index))
    (representation_identity_environment M) succ ltac:(intro i;apply code_eval_num))). exact HS.
 - apply(proj2(code_relation_ext M representation_closure_expression
    (fun index => evalM M(middle .:ex .:body .:closure .:succ .:rep .:rho)(num index))
    (representation_identity_environment M) closure ltac:(intro i;apply code_eval_num))). exact HC.
Qed.
Theorem source_representation_in_closure_recipe_bounded M n phi result :
 source_bounded M phi n ->source_representation_in_closure_recipe M n phi result ->
 source_bounded M result(code_numeral M 3).
Proof.
 intros HP(rep&succ&closure&body&ex&middle&HR&HS&HC&HB&HE&HM&HO).
 pose proof(source_representation_recipe_bounded M n phi rep HP HR)as BR.
 assert(BR4:source_bounded M rep(code_numeral M 4)).
 { apply(source_bounded_monotone M rep(code_numeral M 2)(code_numeral M 4) BR).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BM:source_bounded M(representation_member_code M)(code_numeral M 4)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)
    (representation_member_code M)(code_numeral M 4)(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd _ _ body(code_numeral M 4)(or_introl eq_refl) HB)
   (conj BM BR4))as BB.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex(code_numeral M 3)(or_intror eq_refl) HE) BB)as BE.
 pose proof(proj2(source_bounded_accept_binary M SFImpl closure ex middle(code_numeral M 3)
   (or_intror(or_intror eq_refl)) HM)(conj(representation_closure_condition_bounded M closure HC) BE))as BMidd.
 exact(proj2(source_bounded_accept_binary M SFImpl succ middle result(code_numeral M 3)
   (or_intror(or_intror eq_refl)) HO)(conj(representation_successor_condition_bounded M succ HS) BMidd)).
Qed.
Print Assumptions source_representation_in_closure_recipe_formula_correct.
Print Assumptions source_representation_in_closure_recipe_bounded.

