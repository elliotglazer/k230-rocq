(** Actual Op3 closure existence in the finite named An proof frame. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceEnvironmentPointSlots SourceEnvironmentOperationPadding SourceClosureBinaryFixed SourceNamedDifferenceCertificates
 SourceNamedFiniteCalibration SourceFiniteParameterProofs SourceBoundedCalibration SourceFiniteNameParameters SourceFiniteParameters SourceParameterGraphs
 SourceParameterIdentityCalibration SourceFiniteParameterBounds SourceFiniteParameterComposition
 SourceNamedQuantifierRules SourceZFRProvability OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition environment_named_operation_sigma i:sf_term:=match i with 0=>$3|1=>$1|2=>$0|_=>$(i)end.
Definition environment_named_operation:sf_form:=environment_operation_source[environment_named_operation_sigma].
Definition environment_named_parameters i:sf_term:=match i with 0=>$1|1=>$7|2=>$2|3=>$3|4=>$1|_=>$(i)end.
Definition environment_named_certificate:sf_form:=(source_closure_binary_law 3)[environment_named_parameters].
Definition environment_named_matrix:sf_form:=($0 ∈' $2)∧environment_named_operation.
Definition environment_named_exists:sf_form:=∃(source_finite_closing 0 environment_named_matrix).
Lemma environment_named_certificate_shape:environment_named_certificate=
 (named_difference_successor→named_difference_closure→($3 ∈' $2)→($1 ∈' $2)→environment_named_exists).
Proof. reflexivity. Qed.
Theorem source_zfr_named_environment_certificate M:source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor→named_difference_closure→($3 ∈' $2)→($1 ∈' $2)→environment_named_exists))).
Proof.
 rewrite<-environment_named_certificate_shape.
 set(rho:=fun i=>code_numeral M(sf_index(environment_named_parameters i))).
 apply(source_zfr_closure_extension M rho(code_numeral M(sf_encode environment_named_certificate))).
 destruct(find_bounded(source_closure_binary_law 3))as(bound&HB).
 apply(proj2(source_parameter_graph_ext M bound(source_closure_binary_law 3)HB
  (source_finite_parameter_names 5)(fun i=>CEconst(sf_index(environment_named_parameters i)))
  rho(fun _=>zeroM M)ltac:(intros[|[|[|[|[|i]]]]]v HI;reflexivity)_)).
 exact(source_parameter_substitution_calibration M(source_closure_binary_law 3)environment_named_parameters).
Qed.
Theorem source_named_environment_operation_graph M:
 source_environment_operation_graph M(code_numeral M 3)(code_numeral M(sf_encode environment_named_operation)).
Proof.
 unfold source_environment_operation_graph.
 apply(proj2(source_parameter_graph_ext M 3 environment_operation_source environment_operation_source_bound
  source_three_parameter_names(fun i=>CEconst(sf_index(environment_named_operation_sigma i)))
  (environment_operation_roles M(code_numeral M 3))(fun _=>zeroM M)
  ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)_)).
 exact(source_parameter_substitution_calibration M environment_operation_source environment_named_operation_sigma).
Qed.
Theorem source_named_environment_exists_graph M:source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode environment_named_matrix))(code_numeral M(sf_encode environment_named_exists)).
Proof. exact(source_finite_named_quantifier_calibration M false 0 environment_named_matrix). Qed.
Theorem source_named_environment_operation_bound M:source_bounded M(code_numeral M(sf_encode environment_named_operation))(code_numeral M 8).
Proof.
 apply(proj2(source_formula_numeral_bounded M _ 8)).
 change(bounded 8(isolated_formula(OldZFC.Z_cl.Op 3(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)
  (@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))).
 apply(@isolated_bounded OC.falsity_on 8),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Print Assumptions source_zfr_named_environment_certificate.
Print Assumptions source_named_environment_operation_graph.
Print Assumptions source_named_environment_exists_graph.
Print Assumptions source_named_environment_operation_bound.

