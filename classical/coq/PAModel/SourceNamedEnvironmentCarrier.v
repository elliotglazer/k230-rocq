(** Actual A-in-C proof in the finite named An frame. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceClosureCarrierFixed SourceNamedDifferenceCertificates
 SourceNamedFiniteCalibration SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition environment_named_carrier_parameters i:sf_term:=match i with 0=>$1|1=>$7|2=>$2|_=>$(i)end.
Lemma environment_named_carrier_shape:source_closure_carrier_law[environment_named_carrier_parameters]=
 (named_difference_successor→named_difference_closure→($1 ∈' $2)).
Proof. reflexivity. Qed.
Theorem source_zfr_named_environment_carrier M:source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor→named_difference_closure→($1 ∈' $2)))).
Proof.
 rewrite<-environment_named_carrier_shape.
 set(rho:=fun i=>code_numeral M(sf_index(environment_named_carrier_parameters i))).
 apply(source_zfr_closure_carrier M rho(code_numeral M(sf_encode(source_closure_carrier_law[environment_named_carrier_parameters])))).
 destruct(find_bounded source_closure_carrier_law)as(bound&HB).
 apply(proj2(source_parameter_graph_ext M bound source_closure_carrier_law HB
  (source_finite_parameter_names 3)(fun i=>CEconst(sf_index(environment_named_carrier_parameters i)))
  rho(fun _=>zeroM M)ltac:(intros[|[|[|i]]]v HI;reflexivity)_)).
 exact(source_parameter_substitution_calibration M source_closure_carrier_law environment_named_carrier_parameters).
Qed.
Print Assumptions source_zfr_named_environment_carrier.
