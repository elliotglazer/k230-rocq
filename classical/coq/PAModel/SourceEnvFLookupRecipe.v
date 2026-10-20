(** A genuine arithmetic invariant for reverse-indexed environment lookup.
    n = k+t+1 makes t the assignment-variable offset, without subtraction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceQuantifierRules
 SourceEnvFLookupProfile SourceEnvFDomainRecipe SourceDefinabilityBounds SourceZFRProvability NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_env_lookup_recipe M environment numeral tail out:=exists shifted profile inner,
 source_formula_shift M environment shifted /\source_env_profile M(code_numeral M 1)(zeroM M)(succM M(succM M tail))profile /\
 sf_relation M SFImpl numeral profile inner /\sf_relation M SFImpl shifted inner out.
Definition source_env_lookup_recipe_formula(environment numeral tail out:term):form:=∃∃∃(
 source_formula_shift_formula(ed_lift3 environment)$2 ∧source_env_profile_formula(num 1)zero(σ(σ(ed_lift3 tail)))$1 ∧
 sf_formula SFImpl(ed_lift3 numeral)$1 $0 ∧sf_formula SFImpl $2 $0(ed_lift3 out)).
Lemma lookup_eval_double_succ M rho a b c t:evalM M(a.:b.:c.:rho)(σ(σ(ed_lift3 t)))=
 succM M(succM M(evalM M rho t)).
Proof.
 change(succM M(succM M(evalM M(a.:b.:c.:rho)(ed_lift3 t)))=succM M(succM M(evalM M rho t))).
 now rewrite ed_eval_lift3.
Qed.
Local Opaque holds source_formula_shift_formula source_env_profile_formula sf_formula.
Theorem source_env_lookup_recipe_formula_correct M rho e n tail out:holds M rho(source_env_lookup_recipe_formula e n tail out)<->
 source_env_lookup_recipe M(evalM M rho e)(evalM M rho n)(evalM M rho tail)(evalM M rho out).
Proof.
 unfold source_env_lookup_recipe_formula,source_env_lookup_recipe.
 repeat setoid_rewrite NumericalProofs.holds_ex. repeat setoid_rewrite NumericalProofs.holds_and.
 setoid_rewrite source_formula_shift_formula_correct. setoid_rewrite source_env_profile_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite lookup_eval_double_succ.
 setoid_rewrite ed_eval_lift3. setoid_rewrite code_eval_num.
 split;intros(a&b&c&H);exists a,b,c;cbn in *;tauto.
Qed.
Theorem source_env_lookup_recipe_total M environment numeral tail:exists out,source_env_lookup_recipe M environment numeral tail out.
Proof.
 destruct(numerical_renaming_total M environment(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
 destruct(source_env_profile_total M(code_numeral M 1)(zeroM M)(succM M(succM M tail)))as(profile&HP).
 destruct(sf_relation_total M SFImpl numeral profile)as(inner&HI). destruct(sf_relation_total M SFImpl shifted inner)as(out&HO).
 exists out,shifted,profile,inner. repeat split;assumption.
Qed.
Definition source_env_lookup_proof_at M n:=forall k tail environment numeral out,
 n=succM M(addM M k tail) ->source_envf M n environment ->source_numf M k numeral ->
 source_env_lookup_recipe M environment numeral tail out ->source_zfr_provable M out.
Definition source_env_lookup_proof_formula:form:=∀∀∀∀∀(
 $5 ==σ($4⊕$3) →source_envf_formula $5 $2 →source_numf_formula $4 $1 →
 source_env_lookup_recipe_formula $2 $1 $3 $0 →source_zfr_provable_formula $0).
Lemma source_lookup_length_correct M rho n k tail:holds M rho(n==σ(k⊕tail))<->
 evalM M rho n=succM M(addM M(evalM M rho k)(evalM M rho tail)).
Proof. reflexivity. Qed.
Local Opaque code_numeral source_envf source_numf source_env_lookup_recipe source_zfr_provable
 source_envf_formula source_numf_formula source_env_lookup_recipe_formula source_zfr_provable_formula.
Theorem source_env_lookup_proof_definable M:Definable1 M(source_env_lookup_proof_at M).
Proof.
 exists source_env_lookup_proof_formula,(fun _=>zeroM M). intro n.
 unfold source_env_lookup_proof_formula,source_env_lookup_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all. split.
 - intros H k tail environment numeral out. rewrite!NumericalProofs.holds_imp. intros HL HE HN HO.
   set(rho:=out.:numeral.:environment.:tail.:k.:n.:fun _=>zeroM M)in *.
   apply(proj2(source_zfr_provable_formula_correct M rho $0)).
   apply(H k tail environment numeral out).
   + exact(proj1(source_lookup_length_correct M rho $5 $4 $3)HL).
   + exact(proj1(source_envf_formula_correct M rho $5 $2)HE).
   + exact(proj1(source_numf_formula_correct M rho $4 $1)HN).
   + exact(proj1(source_env_lookup_recipe_formula_correct M rho $2 $1 $3 $0)HO).
 - intros H k tail environment numeral out HL HE HN HO. specialize(H k tail environment numeral out).
   rewrite!NumericalProofs.holds_imp in H.
   set(rho:=out.:numeral.:environment.:tail.:k.:n.:fun _=>zeroM M)in *.
   apply(proj1(source_zfr_provable_formula_correct M rho $0)). apply H.
   + exact(proj2(source_lookup_length_correct M rho $5 $4 $3)HL).
   + exact(proj2(source_envf_formula_correct M rho $5 $2)HE).
   + exact(proj2(source_numf_formula_correct M rho $4 $1)HN).
   + exact(proj2(source_env_lookup_recipe_formula_correct M rho $2 $1 $3 $0)HO).
Qed.
Theorem source_zfr_env_lookup_zero M:source_env_lookup_proof_at M(zeroM M).
Proof. intros k tail environment numeral out HL. exfalso. exact(zero_ne_succ M(addM M k tail)HL). Qed.
Print Assumptions source_env_lookup_recipe_formula_correct.
Print Assumptions source_env_lookup_recipe_total.
Print Assumptions source_env_lookup_proof_definable.
Print Assumptions source_zfr_env_lookup_zero.
