(** Exact literal operation graphs and bounds in the disjunction frame. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceNamedFiniteCalibration
 SourceNamedPairUnionCertificates SourcePairUnionFrame SourceRepresentationConjunctionFrame FixedSourceBounds.
From OldZFC Require Z_base.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition pair_union_outer_index i:=match i with 0=>3|1=>4|2=>5|3=>0|_=>i end.
Definition pair_union_outer_sigma i:sf_term:=$(pair_union_outer_index i).
Lemma named_pair_operation_shape:pair_union_pair_source[pair_union_outer_sigma]=named_pair_operation.
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Pair0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))
  (fun i=>@OC.var OB.sig_empty(pair_union_outer_index i))pair_union_outer_sigma ltac:(intro i;reflexivity))as E.
 rewrite OldZFC.Z_base.Pair0_subst in E. exact(eq_sym E).
Qed.
Lemma named_union_operation_shape:pair_union_union_source[pair_union_outer_sigma]=named_union_operation.
Proof.
 pose proof(isolated_formula_subst(OldZFC.Z_base.Union0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))
  (fun i=>@OC.var OB.sig_empty(pair_union_outer_index i))pair_union_outer_sigma ltac:(intro i;reflexivity))as E.
 rewrite OldZFC.Z_base.Union0_subst in E. exact(eq_sym E).
Qed.
Lemma source_pair_union_outer_calibration M phi:bounded 4 phi ->
 code_relation M(conjunction_outer_environment M)(source_parameter_expression(source_finite_parameter_names 4)phi)
  (code_numeral M(sf_encode(phi[pair_union_outer_sigma]))).
Proof.
 intro HB. apply(proj2(source_parameter_graph_ext M 4 phi HB(source_finite_parameter_names 4)
  (fun i=>CEconst(sf_index(pair_union_outer_sigma i)))(conjunction_outer_environment M)(fun _=>zeroM M)
  ltac:(intros[|[|[|[|i]]]]x HI;try lia;reflexivity)
  (code_numeral M(sf_encode(phi[pair_union_outer_sigma]))))).
 exact(source_parameter_substitution_calibration M phi pair_union_outer_sigma).
Qed.
Theorem source_named_pair_operation_graph M:code_relation M(conjunction_outer_environment M)E_pair_union_pair
 (code_numeral M(sf_encode named_pair_operation)).
Proof. rewrite <-named_pair_operation_shape. exact(source_pair_union_outer_calibration M pair_union_pair_source pair_union_pair_bound). Qed.
Theorem source_named_union_operation_graph M:code_relation M(conjunction_outer_environment M)E_pair_union_union
 (code_numeral M(sf_encode named_union_operation)).
Proof. rewrite <-named_union_operation_shape. exact(source_pair_union_outer_calibration M pair_union_union_source pair_union_union_bound). Qed.
Lemma pair_union_outer_names_eight M i:(i<4)%nat ->coding_lt M(conjunction_outer_environment M i)(code_numeral M 8).
Proof.
 intro HI. exact(coding_lt_trans M _ _ _(conjunction_outer_names_bound M i HI)(proj2(fixed_source_numeral_lt_iff M 6 8)ltac:(lia))).
Qed.
Theorem named_pair_union_fixed_bounds M:
 source_bounded M(code_numeral M(sf_encode named_pair_operation))(code_numeral M 8) /\
 source_bounded M(code_numeral M(sf_encode named_union_operation))(code_numeral M 8).
Proof.
 split.
 - exact(pair_union_parameter_bound M pair_union_pair_source(conjunction_outer_environment M)(code_numeral M 8)_
    pair_union_pair_bound(pair_union_outer_names_eight M)(source_named_pair_operation_graph M)).
 - exact(pair_union_parameter_bound M pair_union_union_source(conjunction_outer_environment M)(code_numeral M 8)_
    pair_union_union_bound(pair_union_outer_names_eight M)(source_named_union_operation_graph M)).
Qed.
Print Assumptions source_named_pair_operation_graph.
Print Assumptions source_named_union_operation_graph.
Print Assumptions named_pair_union_fixed_bounds.
