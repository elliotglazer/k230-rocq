(** The two actual fixed Op2 existence certificates, in the named frame
    used by conjunction. These proofs contain no representation matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceClosureBinaryFixed SourceFiniteNameParameters SourceFiniteParameters SourceParameterGraphs
 SourceNamedFiniteCalibration SourceNamedQuantifierRules SourceZFRProvability SourceDifferenceProfile
 OldNamedSyntaxBridge.
From OldZFC Require Z_cl Z_prim.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition named_difference_parameters x y i :sf_term :=match i with
 |0=>$1|1=>$7|2=>$2|3=>$(x)|4=>$(y)|_=>$(i)end.
Definition named_difference_certificate x y :sf_form :=(source_closure_binary_law 2)[named_difference_parameters x y].
Definition named_difference_successor :sf_form :=isolated_formula(OldZFC.Z_base.Succ0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 7)).
Definition named_difference_closure :sf_form :=isolated_formula(OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 7)(@OC.var OB.sig_empty 2)).
Definition named_difference_matrix x y r :sf_form :=($(r) ∈' $2) ∧source_difference_operation $(x) $(y) $(r).
Definition named_difference_exists x y r :sf_form :=∃(source_finite_closing r(named_difference_matrix x y r)).
Theorem source_zfr_named_difference_certificate M x y :source_zfr_provable M(code_numeral M(sf_encode(named_difference_certificate x y))).
Proof.
 set(rho:=fun i=>code_numeral M(sf_index(named_difference_parameters x y i))).
 apply(source_zfr_closure_difference M rho(code_numeral M(sf_encode(named_difference_certificate x y)))).
 destruct(find_bounded(source_closure_binary_law 2))as(bound&HB).
 apply(proj2(source_parameter_graph_ext M bound(source_closure_binary_law 2) HB
   (source_finite_parameter_names 5)(fun i=>CEconst(sf_index(named_difference_parameters x y i)))
   rho(fun _=>zeroM M) ltac:(intros[|[|[|[|[|i]]]]]v HI;reflexivity)
   (code_numeral M(sf_encode(named_difference_certificate x y))))).
 exact(source_parameter_substitution_calibration M(source_closure_binary_law 2)(named_difference_parameters x y)).
Qed.
Lemma named_difference_first_shape :named_difference_certificate 3 4=
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5).
Proof. reflexivity. Qed.
Lemma named_difference_second_shape :named_difference_certificate 3 5=
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($5 ∈' $2)→named_difference_exists 3 5 0).
Proof. reflexivity. Qed.
Theorem source_zfr_named_difference_first M :source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($4 ∈' $2)→named_difference_exists 3 4 5))).
Proof. rewrite <-named_difference_first_shape. exact(source_zfr_named_difference_certificate M 3 4). Qed.
Theorem source_zfr_named_difference_second M :source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($3 ∈' $2)→($5 ∈' $2)→named_difference_exists 3 5 0))).
Proof. rewrite <-named_difference_second_shape. exact(source_zfr_named_difference_certificate M 3 5). Qed.
Theorem named_difference_first_quantifier M :source_named_quantifier M false(code_numeral M 5)
 (code_numeral M(sf_encode(named_difference_matrix 3 4 5)))
 (code_numeral M(sf_encode(named_difference_exists 3 4 5))).
Proof. exact(source_finite_named_quantifier_calibration M false 5(named_difference_matrix 3 4 5)). Qed.
Theorem named_difference_second_quantifier M :source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode(named_difference_matrix 3 5 0)))
 (code_numeral M(sf_encode(named_difference_exists 3 5 0))).
Proof. exact(source_finite_named_quantifier_calibration M false 0(named_difference_matrix 3 5 0)). Qed.
Print Assumptions source_zfr_named_difference_first.
Print Assumptions source_zfr_named_difference_second.
Print Assumptions named_difference_first_quantifier.
Print Assumptions named_difference_second_quantifier.

