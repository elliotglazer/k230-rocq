(** Arithmetic graph of NumF_k(x) -> NumF_l(y) -> x in y. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes NumericalInstantiation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_numf_less_recipe M p q x y out :=exists px qy member inner,
 numerical_instantiation M p x px /\numerical_instantiation M q y qy /\sf_relation M SFMember x y member /\
 sf_relation M SFImpl qy member inner /\sf_relation M SFImpl px inner out.
Definition nl_lift4(t:term):=t`[↑]`[↑]`[↑]`[↑].
Definition source_numf_less_recipe_formula(p q x y out:term):form :=∃∃∃∃(
 numerical_instantiation_formula(nl_lift4 p)(nl_lift4 x)$3 ∧
 numerical_instantiation_formula(nl_lift4 q)(nl_lift4 y)$2 ∧
 sf_formula SFMember(nl_lift4 x)(nl_lift4 y)$1 ∧sf_formula SFImpl $2 $1 $0 ∧sf_formula SFImpl $3 $0(nl_lift4 out)).
Lemma nl_eval_lift4 M rho a b c d t :evalM M(a.:b.:c.:d.:rho)(nl_lift4 t)=evalM M rho t.
Proof. unfold nl_lift4,evalM. now rewrite !eval_up. Qed.
Local Opaque holds numerical_instantiation_formula sf_formula.
Theorem source_numf_less_recipe_formula_correct M rho p q x y out :
 holds M rho(source_numf_less_recipe_formula p q x y out) <->
 source_numf_less_recipe M(evalM M rho p)(evalM M rho q)(evalM M rho x)(evalM M rho y)(evalM M rho out).
Proof.
 unfold source_numf_less_recipe_formula,source_numf_less_recipe.
 repeat setoid_rewrite NumericalProofs.holds_ex. repeat setoid_rewrite NumericalProofs.holds_and.
 setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite sf_formula_correct. setoid_rewrite nl_eval_lift4.
 split;intros(a&b&c&d&H);exists a,b,c,d;cbn in *;tauto.
Qed.
Theorem source_numf_less_recipe_total M p q x y :exists out,source_numf_less_recipe M p q x y out.
Proof.
 destruct(numerical_instantiation_total M p x)as(px&HX).
 destruct(numerical_instantiation_total M q y)as(qy&HY).
 destruct(sf_relation_total M SFMember x y)as(member&HM).
 destruct(sf_relation_total M SFImpl qy member)as(inner&HI).
 destruct(sf_relation_total M SFImpl px inner)as(out&HO).
 exists out,px,qy,member,inner. repeat split;assumption.
Qed.
Theorem source_numf_less_recipe_functional M p q x y f g :source_numf_less_recipe M p q x y f ->source_numf_less_recipe M p q x y g ->f=g.
Proof.
 intros(px&qy&m&i&HX&HY&HM&HI&HF)(px'&qy'&m'&i'&HX'&HY'&HM'&HI'&HG).
 assert(E:px'=px)by(eapply numerical_instantiation_functional;eassumption). subst px'.
 assert(E:qy'=qy)by(eapply numerical_instantiation_functional;eassumption). subst qy'.
 assert(E:m'=m)by(eapply sf_relation_functional;eassumption). subst m'.
 assert(E:i'=i)by(eapply sf_relation_functional;eassumption). subst i'.
 eapply sf_relation_functional;eassumption.
Qed.
Print Assumptions source_numf_less_recipe_formula_correct.
Print Assumptions source_numf_less_recipe_total.
