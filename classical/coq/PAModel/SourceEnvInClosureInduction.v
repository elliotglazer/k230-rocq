(** Uniform parameter-environment existence inside the closure C.
    Genuine PA-definable induction covers every internal count, including
    nonstandard counts. No source-existence or constructor family remains. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SourceDefinabilityIteration SourceDefinabilityBounds
 SourceDefinabilityPrimitives SourceEnvInClosureRecipe SourceEnvInClosureBase SourceEnvInClosureStep SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_env_in_closure_proof_at M count:=forall environment out,
 source_envf M count environment->source_env_in_closure_recipe M count environment out->source_zfr_provable M out.
Definition source_env_in_closure_proof_formula:form:=∀∀(
 source_envf_formula $2 $1 →source_env_in_closure_recipe_formula $2 $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds source_envf_formula source_env_in_closure_recipe_formula source_zfr_provable_formula.
Theorem source_env_in_closure_proof_definable M:Definable1 M(source_env_in_closure_proof_at M).
Proof.
 exists source_env_in_closure_proof_formula,(fun _=>zeroM M). intro count.
 unfold source_env_in_closure_proof_formula,source_env_in_closure_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all. repeat setoid_rewrite NumericalProofs.holds_imp.
 setoid_rewrite source_envf_formula_correct. setoid_rewrite source_env_in_closure_recipe_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Theorem source_zfr_env_in_closure_uniform M:forall count,source_env_in_closure_proof_at M count.
Proof.
 apply(definable_induction M(source_env_in_closure_proof_at M)(source_env_in_closure_proof_definable M)).
 - intros environment out HE HO. apply source_def_iteration_zero in HE. subst environment.
   exact(source_zfr_env_in_closure_zero M out HO).
 - intros count IH environment out HE HO. pose proof HE as HNext.
   apply source_def_iteration_succ in HE. destruct HE as(previous&HP&HStep).
   destruct(source_env_in_closure_recipe_total M count previous)as(old&HOld).
   exact(source_zfr_env_in_closure_step M count previous environment old out HP HNext HStep HOld HO(IH previous old HP HOld)).
Qed.
Theorem source_zfr_env_in_closure_total M count:exists environment out,
 source_envf M count environment /\source_env_in_closure_recipe M count environment out /\source_zfr_provable M out.
Proof.
 destruct(source_envf_total M count)as(environment&HE).
 destruct(source_env_in_closure_recipe_total M count environment)as(out&HO).
 exists environment,out. exact(conj HE(conj HO(source_zfr_env_in_closure_uniform M count environment out HE HO))).
Qed.
Print Assumptions source_env_in_closure_proof_definable.
Print Assumptions source_zfr_env_in_closure_uniform.
Print Assumptions source_zfr_env_in_closure_total.
