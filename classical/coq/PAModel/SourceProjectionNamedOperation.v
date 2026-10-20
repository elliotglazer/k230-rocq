(** Exact finite source Op4 witness certificate in the shared named closure frame. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift SourceProjectionNamedOperationOld
 SourceProjectionFiniteSyntax SourceProjectionProfilePoint SourceNamedDifferenceCertificates SourceNamedFiniteCalibration
 SourceFiniteNameParameters SourceFiniteParameters SourceParameterGraphs SourceNamedQuantifierRules SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors
 OldNamedSyntaxBridge OldZFRProofLift SourceLFixed SourceLNonempty.
From OldZFC Require Z_cl.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition projection_named_operation:sf_form:=isolated_formula(OldZFC.Z_cl.Op 4(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)).
Definition projection_named_matrix:sf_form:=($0 ∈' $2)∧projection_named_operation.
Definition projection_named_exists:sf_form:=∃(source_finite_closing 0 projection_named_matrix).
Definition projection_named_law:sf_form:=named_difference_successor→named_difference_closure→($4 ∈' $2)→($3 ∈' $2)→projection_named_exists.
Lemma projection_named_old_shape:isolated_formula old_projection_named_law=projection_named_law.
Proof. reflexivity. Qed.
Theorem source_zfr_projection_named_certificate M:source_zfr_provable M(code_numeral M(sf_encode projection_named_law)).
Proof.
 rewrite<-projection_named_old_shape.
 exact(finite_old_zfr_proof_lift M old_L_background old_projection_named_law old_L_background_valid old_projection_named_proof).
Qed.
Theorem source_projection_named_quantifier M:source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode projection_named_matrix))(code_numeral M(sf_encode projection_named_exists)).
Proof. exact(source_finite_named_quantifier_calibration M false 0 projection_named_matrix). Qed.
Definition projection_named_substitution i:sf_term:=match i with 0=>$4|1=>$3|2=>$1|_=>$0 end.
Theorem source_projection_named_operation_graph M:code_relation M
 (projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))
 (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)(code_numeral M(sf_encode projection_named_operation)).
Proof.
 apply(proj2(source_parameter_graph_ext M 4 projection_operation4 projection_operation_bound(source_finite_parameter_names 4)
  (fun i=>CEconst(sf_index(projection_named_substitution i)))
  (projection_five_values(code_numeral M 4)(code_numeral M 3)(code_numeral M 1)(zeroM M)(zeroM M))(fun _=>zeroM M)
  ltac:(intros[|[|[|[|i]]]]v HI;try lia;reflexivity)(code_numeral M(sf_encode projection_named_operation)))).
 change(code_relation M(fun _=>zeroM M)(source_parameter_expression(fun i=>CEconst(sf_index(projection_named_substitution i)))projection_operation4)
  (code_numeral M(sf_encode(projection_operation4[projection_named_substitution])))).
 exact(source_parameter_substitution_calibration M projection_operation4 projection_named_substitution).
Qed.
Print Assumptions source_zfr_projection_named_certificate.
Print Assumptions source_projection_named_quantifier.
Print Assumptions source_projection_named_operation_graph.
