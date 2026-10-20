(** PA induction on arbitrary internal environment lengths and numeral indices. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityPrimitives SourceDefinabilityStep SourceDefinabilityIteration.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_envf M n out :=source_def_iteration M true n(code_numeral M(sf_encode source_def_empty)) out.
Definition source_numf M n out :=source_def_iteration M false n(code_numeral M(sf_encode source_def_empty)) out.
Definition source_envf_formula(n out:term) :=source_def_iteration_formula true n(num(sf_encode source_def_empty)) out.
Definition source_numf_formula(n out:term) :=source_def_iteration_formula false n(num(sf_encode source_def_empty)) out.
Theorem source_envf_formula_correct M rho n out :holds M rho(source_envf_formula n out)<->
 source_envf M(evalM M rho n)(evalM M rho out).
Proof. unfold source_envf_formula,source_envf. rewrite source_def_iteration_formula_correct,code_eval_num. reflexivity. Qed.
Theorem source_numf_formula_correct M rho n out :holds M rho(source_numf_formula n out)<->
 source_numf M(evalM M rho n)(evalM M rho out).
Proof. unfold source_numf_formula,source_numf. rewrite source_def_iteration_formula_correct,code_eval_num. reflexivity. Qed.
Definition source_def_bound_at M environment n :=forall out,
 source_def_iteration M environment n(code_numeral M(sf_encode source_def_empty)) out ->
 source_bounded M out(if environment then succM M n else code_numeral M 1).
Definition source_def_bound_formula(environment:bool):form :=∀(
 source_def_iteration_formula environment $1(num(sf_encode source_def_empty)) $0 →
 source_bounded_accept_formula $0(if environment then σ $1 else num 1)).
Local Opaque holds source_def_iteration_formula source_bounded_accept_formula.
Lemma source_def_bound_definable M environment :Definable1 M(source_def_bound_at M environment).
Proof.
 exists(source_def_bound_formula environment),(fun _=>zeroM M). intro n.
 unfold source_def_bound_formula,source_def_bound_at. rewrite holds_all.
 setoid_rewrite holds_imp. setoid_rewrite source_def_iteration_formula_correct.
 setoid_rewrite source_bounded_accept_formula_correct.
 repeat setoid_rewrite code_eval_num. destruct environment;reflexivity.
Qed.
Theorem source_def_iteration_bounded M environment n :source_def_bound_at M environment n.
Proof.
 revert n. apply(definable_induction M(source_def_bound_at M environment)(source_def_bound_definable M environment)).
 - intros out HO. apply source_def_iteration_zero in HO. subst out.
   destruct environment;apply numerical_def_empty_bound.
 - intros n IH out HO. apply source_def_iteration_succ in HO. destruct HO as(p&HP&HS).
   pose proof(IH p HP) as HB. destruct environment.
   + exact(source_def_environment_step_bound M n p out HB HS).
   + exact(source_def_numeral_step_bound M p out HB HS).
Qed.
Theorem source_envf_total M n :exists out,source_envf M n out.
Proof. apply source_def_iteration_total. Qed.
Theorem source_numf_total M n :exists out,source_numf M n out.
Proof. apply source_def_iteration_total. Qed.
Theorem source_envf_bound M n out :source_envf M n out ->source_bounded M out(succM M n).
Proof. apply(source_def_iteration_bounded M true n out). Qed.
Theorem source_numf_bound M n out :source_numf M n out ->source_bounded M out(code_numeral M 1).
Proof. apply(source_def_iteration_bounded M false n out). Qed.
Print Assumptions source_envf_formula_correct.
Print Assumptions source_numf_formula_correct.
Print Assumptions source_def_bound_definable.
Print Assumptions source_def_iteration_bounded.
Print Assumptions source_envf_total.
Print Assumptions source_numf_total.
