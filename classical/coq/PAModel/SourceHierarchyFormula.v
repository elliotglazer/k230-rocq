(** An explicit PA formula for the literal hierarchy predicate graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceHierarchySyntax SourceFiniteParameters SourceFiniteNameParameters.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_LL_instance_formula(d z out:term):form :=
  code_formula(source_parameter_expression(source_finite_parameter_names 2)source_LL_predicate)
    (fun (idx:nat)=>match idx with 0=>d|_=>z end)out.

Theorem source_LL_instance_formula_correct M rho d z out :
  holds M rho(source_LL_instance_formula d z out) <->
  source_LL_instance M(evalM M rho d)(evalM M rho z)(evalM M rho out).
Proof.
  unfold source_LL_instance_formula. rewrite code_formula_correct.
  unfold source_LL_instance. apply code_relation_ext. intros[|idx];reflexivity.
Qed.

Print Assumptions source_LL_instance_formula_correct.
