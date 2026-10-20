(** Literal finite Dom0 graph at arbitrary model-valued source names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs
 SourceParameterIdentityCalibration SourceNumeralLift.
From OldZFC Require Z_base Z_prim Z_rel.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_env_domain_predicate:sf_form:=isolated_formula(OldZFC.Z_base.Dom0
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition source_env_domain_expression:=source_parameter_expression(source_finite_parameter_names 2)source_env_domain_predicate.
Definition source_env_domain M e d out:=code_relation M(sf_env e d)source_env_domain_expression out.
Definition source_env_domain_formula(e d out:term):form:=code_formula source_env_domain_expression(sf_env e d)out.
Local Opaque holds code_relation code_formula source_env_domain_expression.
Theorem source_env_domain_formula_correct M rho e d out:holds M rho(source_env_domain_formula e d out)<->
 source_env_domain M(evalM M rho e)(evalM M rho d)(evalM M rho out).
Proof.
 unfold source_env_domain_formula,source_env_domain. rewrite code_formula_correct.
 apply code_relation_ext. intros[|idx];reflexivity.
Qed.
Theorem source_env_domain_total M e d:exists out,source_env_domain M e d out.
Proof. apply code_relation_total. Qed.
Lemma source_env_domain_finite_bound:Undecidability.FOL.Syntax.Bounded.bounded 2 source_env_domain_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 2(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_env_domain_bounded M e d out k:coding_lt M e k ->coding_lt M d k ->
 source_env_domain M e d out ->source_bounded M out k.
Proof.
 intros HE HD HO. apply(source_parameter_graph_bounded M 2 source_env_domain_predicate source_env_domain_finite_bound
  (source_finite_parameter_names 2)(sf_env e d)k);[|exact HO].
 intros[|[|idx]] x HI HX;try lia.
 - change(x=e)in HX. now subst x.
 - change(x=d)in HX. now subst x.
Qed.
Theorem source_env_domain_canonical M:source_env_domain M(zeroM M)(code_numeral M 1)
 (code_numeral M(sf_encode source_env_domain_predicate)).
Proof.
 apply(source_parameter_identity_calibration M source_env_domain_predicate(source_finite_parameter_names 2)(sf_env(zeroM M)(code_numeral M 1))).
 intros[|[|idx]];reflexivity.
Qed.
Print Assumptions source_env_domain_formula_correct.
Print Assumptions source_env_domain_total.
Print Assumptions source_env_domain_finite_bound.
Print Assumptions source_env_domain_bounded.
Print Assumptions source_env_domain_canonical.
