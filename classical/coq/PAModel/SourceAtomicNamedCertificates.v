(** Literal Op6/Op7 witness certificates in the atomic named frame.
    All formulas here are fixed finite source syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceAtomicClosureFixed SourceAtomicOperationSyntax SourceFiniteNameParameters SourceFiniteParameters SourceParameterGraphs
 SourceParameterIdentityCalibration SourceNamedFiniteCalibration SourceNamedQuantifierRules SourceNamedDifferenceCertificates SourceZFRProvability OldNamedSyntaxBridge.
From OldZFC Require Z_cl Z_prim.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition named_atomic_parameters i:sf_term:=match i with 0=>$1|1=>$7|_=>$(i)end.
Definition named_atomic_operation(member:bool):sf_form:=isolated_formula(OldZFC.Z_cl.Op(if member then 6 else 7)
 (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 0)).
Definition named_atomic_matrix(member:bool):sf_form:=($0 ∈' $2)∧named_atomic_operation member.
Definition named_atomic_exists(member:bool):sf_form:=∃(source_finite_closing 0(named_atomic_matrix member)).
Definition named_atomic_certificate(member:bool):sf_form:=
 (source_atomic_closure_ternary_law(if member then 6 else 7))[named_atomic_parameters].
Lemma named_atomic_certificate_shape member:named_atomic_certificate member=
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→($5 ∈' $2)→named_atomic_exists member).
Proof. destruct member;reflexivity. Qed.
Theorem source_zfr_named_atomic_certificate M(member:bool):source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→($5 ∈' $2)→named_atomic_exists member))).
Proof.
 rewrite <-named_atomic_certificate_shape.
 set(rho:=fun i=>code_numeral M(sf_index(named_atomic_parameters i))).
 apply(source_zfr_atomic_closure_operation M member rho(code_numeral M(sf_encode(named_atomic_certificate member)))).
 destruct(find_bounded(source_atomic_closure_ternary_law(if member then 6 else 7)))as(bound&HB).
 apply(proj2(source_parameter_graph_ext M bound(source_atomic_closure_ternary_law(if member then 6 else 7)) HB
   (source_finite_parameter_names 6)(fun i=>CEconst(sf_index(named_atomic_parameters i)))
   rho(fun _=>zeroM M) ltac:(intros[|[|[|[|[|[|i]]]]]]v HI;reflexivity)
   (code_numeral M(sf_encode(named_atomic_certificate member))))).
 exact(source_parameter_substitution_calibration M(source_atomic_closure_ternary_law(if member then 6 else 7))named_atomic_parameters).
Qed.
Theorem named_atomic_quantifier M member:source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode(named_atomic_matrix member)))(code_numeral M(sf_encode(named_atomic_exists member))).
Proof. exact(source_finite_named_quantifier_calibration M false 0(named_atomic_matrix member)). Qed.
Theorem named_atomic_operation_graph M member:source_atomic_operation M member(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M)
 (code_numeral M(sf_encode(named_atomic_operation member))).
Proof.
 apply(source_parameter_atomic_operation_instance M member(fun i=>CEconst i)(fun _=>zeroM M)
   3 4 5 0(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)(zeroM M)
   (code_numeral M(sf_encode(named_atomic_operation member)))eq_refl eq_refl eq_refl eq_refl).
 exact(source_parameter_identity_calibration M(named_atomic_operation member)(fun i=>CEconst i)(fun _=>zeroM M)ltac:(intro i;reflexivity)).
Qed.
Print Assumptions source_zfr_named_atomic_certificate.
Print Assumptions named_atomic_quantifier.
Print Assumptions named_atomic_operation_graph.
