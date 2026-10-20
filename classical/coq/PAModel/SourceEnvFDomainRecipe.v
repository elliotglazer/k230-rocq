(** The exact first-order arithmetic environment-domain invariant. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes NumericalInstantiation
 SourceEnvFDomainGraph SourceDefinabilityBounds SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_env_domain_recipe M environment numeral out:=exists num1 dom inner,
 numerical_instantiation M numeral(code_numeral M 1)num1 /\source_env_domain M(zeroM M)(code_numeral M 1)dom /\
 sf_relation M SFImpl num1 dom inner /\sf_relation M SFImpl environment inner out.
Definition ed_lift3(t:term):=t`[↑]`[↑]`[↑].
Definition source_env_domain_recipe_formula(environment numeral out:term):form:=∃∃∃(
 numerical_instantiation_formula(ed_lift3 numeral)(num 1)$2 ∧source_env_domain_formula zero(num 1)$1 ∧
 sf_formula SFImpl $2 $1 $0 ∧sf_formula SFImpl(ed_lift3 environment)$0(ed_lift3 out)).
Lemma ed_eval_lift3 M rho a b c t:evalM M(a.:b.:c.:rho)(ed_lift3 t)=evalM M rho t.
Proof. unfold ed_lift3,evalM. now rewrite !eval_up. Qed.
Local Opaque holds numerical_instantiation_formula source_env_domain_formula sf_formula.
Theorem source_env_domain_recipe_formula_correct M rho e n out:holds M rho(source_env_domain_recipe_formula e n out)<->
 source_env_domain_recipe M(evalM M rho e)(evalM M rho n)(evalM M rho out).
Proof.
 unfold source_env_domain_recipe_formula,source_env_domain_recipe.
 repeat setoid_rewrite NumericalProofs.holds_ex. repeat setoid_rewrite NumericalProofs.holds_and.
 setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite source_env_domain_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite ed_eval_lift3. setoid_rewrite code_eval_num.
 split;intros(a&b&c&H);exists a,b,c;cbn in *;tauto.
Qed.
Theorem source_env_domain_recipe_total M environment numeral:exists out,source_env_domain_recipe M environment numeral out.
Proof.
 destruct(numerical_instantiation_total M numeral(code_numeral M 1))as(num1&HN).
 destruct(source_env_domain_total M(zeroM M)(code_numeral M 1))as(dom&HD).
 destruct(sf_relation_total M SFImpl num1 dom)as(inner&HI). destruct(sf_relation_total M SFImpl environment inner)as(out&HO).
 exists out,num1,dom,inner. repeat split;assumption.
Qed.
Theorem source_env_domain_recipe_functional M environment numeral f g:
 source_env_domain_recipe M environment numeral f ->source_env_domain_recipe M environment numeral g ->f=g.
Proof.
 intros(a&d&i&HA&HD&HI&HF)(b&e&j&HB&HE&HJ&HG).
 assert(E:b=a)by(eapply numerical_instantiation_functional;eassumption). subst b.
 assert(E:e=d)by(eapply code_relation_functional;[exact HE|exact HD]). subst e.
 assert(E:j=i)by(eapply sf_relation_functional;eassumption). subst j.
 eapply sf_relation_functional;eassumption.
Qed.
Local Opaque code_numeral.
Definition source_env_domain_proof_at M n:=forall environment numeral out,
 source_envf M n environment ->source_numf M n numeral ->source_env_domain_recipe M environment numeral out ->source_zfr_provable M out.
Definition source_env_domain_proof_formula:form:=∀∀∀(
 source_envf_formula $3 $2 →source_numf_formula $3 $1 →source_env_domain_recipe_formula $2 $1 $0 →source_zfr_provable_formula $0).
Local Opaque source_envf_formula source_numf_formula source_env_domain_recipe_formula source_zfr_provable_formula
 source_envf source_numf source_env_domain_recipe source_zfr_provable.
Theorem source_env_domain_proof_definable M:Definable1 M(source_env_domain_proof_at M).
Proof.
 exists source_env_domain_proof_formula,(fun _=>zeroM M). intro n.
 unfold source_env_domain_proof_formula,source_env_domain_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all.
 split.
 - intros H environment numeral out. rewrite !NumericalProofs.holds_imp. intros HE HN HO.
   apply(proj2(source_zfr_provable_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$0)).
   apply(H environment numeral out).
   + exact(proj1(source_envf_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$3 $2)HE).
   + exact(proj1(source_numf_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$3 $1)HN).
   + exact(proj1(source_env_domain_recipe_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$2 $1 $0)HO).
 - intros H environment numeral out HE HN HO. specialize(H environment numeral out).
   rewrite !NumericalProofs.holds_imp in H.
   apply(proj1(source_zfr_provable_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$0)).
   apply H.
   + exact(proj2(source_envf_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$3 $2)HE).
   + exact(proj2(source_numf_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$3 $1)HN).
   + exact(proj2(source_env_domain_recipe_formula_correct M(out.:numeral.:environment.:n.:fun _=>zeroM M)$2 $1 $0)HO).
Qed.
Print Assumptions source_env_domain_recipe_formula_correct.
Print Assumptions source_env_domain_recipe_total.
Print Assumptions source_env_domain_recipe_functional.
Print Assumptions source_env_domain_proof_definable.
