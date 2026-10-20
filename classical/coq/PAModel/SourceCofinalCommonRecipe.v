(** Exact two-witness cofinal common-level assertion. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded NumericalInstantiation SourceCofinalCommonPoint SourceOrdinalPredicate SourceCommonLevelRecipe.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_cofinal_common_recipe M start count K out :=exists point exY,
 source_cofinal_common_point M(succM M(succM M start))count(succM M(succM M K))(code_numeral M 1)(zeroM M)point /\
 sf_relation M SFEx point(zeroM M)exY /\sf_relation M SFEx exY(zeroM M)out.
Definition source_cofinal_lift2(t:term):=t`[↑]`[↑].
Definition source_cofinal_common_formula(ordcode start count K out:term):form :=∃∃
 (source_cofinal_common_point_formula(source_cofinal_lift2 ordcode)(σ(σ(source_cofinal_lift2 start)))
 (source_cofinal_lift2 count)(σ(σ(source_cofinal_lift2 K)))(num 1)zero $1 ∧
 sf_formula SFEx $1 zero $0 ∧sf_formula SFEx $0 zero(source_cofinal_lift2 out)).
Local Opaque holds source_cofinal_common_point_formula sf_formula.
Lemma source_cofinal_eval_lift2 M rho a b t :
 evalM M(a .:b .:rho)(source_cofinal_lift2 t)=evalM M rho t.
Proof. unfold source_cofinal_lift2,evalM. now rewrite !eval_up. Qed.
Theorem source_cofinal_common_formula_correct M rho ordcode start count K out :
 holds M rho(source_cofinal_common_formula ordcode start count K out) <->
 exists point exY,
 source_cofinal_common_point_data M(evalM M rho ordcode)(succM M(succM M(evalM M rho start)))
 (evalM M rho count)(succM M(succM M(evalM M rho K)))(code_numeral M 1)(zeroM M)point /\
 sf_relation M SFEx point(zeroM M)exY /\sf_relation M SFEx exY(zeroM M)(evalM M rho out).
Proof.
 unfold source_cofinal_common_formula. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite source_cofinal_common_point_formula_correct. setoid_rewrite sf_formula_correct.
 repeat setoid_rewrite source_common_eval_succ. setoid_rewrite source_cofinal_eval_lift2.
 split;intros(p&e&H);exists p,e;tauto.
Qed.
Theorem source_cofinal_common_recipe_total M start count K :exists out,
 source_cofinal_common_recipe M start count K out.
Proof.
 destruct(source_cofinal_common_point_total M(succM M(succM M start))count(succM M(succM M K))(code_numeral M 1)(zeroM M))as(point&HP).
 destruct(sf_relation_total M SFEx point(zeroM M))as(exY&HY).
 destruct(sf_relation_total M SFEx exY(zeroM M))as(out&HO).
 exists out,point,exY. auto.
Qed.
Theorem source_cofinal_common_recipe_functional M start count K f g :
 source_cofinal_common_recipe M start count K f ->source_cofinal_common_recipe M start count K g ->f=g.
Proof.
 intros(p&e&HP&HE&HF)(p'&e'&HP'&HE'&HG).
 pose proof(source_cofinal_common_point_functional M(succM M(succM M start))count(succM M(succM M K))
 (code_numeral M 1)(zeroM M)p p' HP HP')as E. subst p'.
 pose proof(sf_relation_functional M SFEx p(zeroM M)e e' HE HE')as E. subst e'.
 exact(sf_relation_functional M SFEx e(zeroM M)f g HF HG).
Qed.
Print Assumptions source_cofinal_common_formula_correct.
Print Assumptions source_cofinal_common_recipe_total.
Print Assumptions source_cofinal_common_recipe_functional.
