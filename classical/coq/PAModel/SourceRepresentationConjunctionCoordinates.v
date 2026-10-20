(** A genuine finite numerical map normalizes the conjunction frame.
    Carrier1 becomes0, successor7 becomes1, and closure container2 stays2. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceFiniteParameters SourceFiniteNameParameters SourceNamedFiniteCalibration SourceNamedDifferenceCertificates
 SourceRepresentationClosureRecipe SourceDefinabilityPrimitives NumericalRenamingMaps NumericalRenaming FixedSourceBounds.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition RNC_coordinate_name i:=match i with
 |0=>0|1=>0|2=>2|3=>3|4=>4|5=>5|6=>6|7=>1|_=>i end.
Definition RNC_coordinate_substitution i:sf_term:=$(RNC_coordinate_name i).
Lemma RNC_coordinate_tail i :(8<=i)%nat ->RNC_coordinate_name i=i.
Proof. intro H. destruct i as[|[|[|[|[|[|[|[|i]]]]]]]];try lia;reflexivity. Qed.
Lemma RNC_coordinate_successor :named_difference_successor[RNC_coordinate_substitution]=source_def_successor01.
Proof. reflexivity. Qed.
Lemma RNC_coordinate_closure :named_difference_closure[RNC_coordinate_substitution]=representation_closure_condition.
Proof. reflexivity. Qed.

Theorem source_representation_conjunction_coordinates_total M :exists b c,
 renaming_lookup M b c(code_numeral M 8)(zeroM M)(code_numeral M 1)(zeroM M) /\
 renaming_lookup M b c(code_numeral M 8)(zeroM M)(code_numeral M 2)(code_numeral M 2) /\
 renaming_lookup M b c(code_numeral M 8)(zeroM M)(code_numeral M 7)(code_numeral M 1) /\
 numerical_renaming M(code_numeral M(sf_encode named_difference_successor))b c(code_numeral M 8)(zeroM M)
  (code_numeral M(sf_encode source_def_successor01)) /\
 numerical_renaming M(code_numeral M(sf_encode named_difference_closure))b c(code_numeral M 8)(zeroM M)
  (code_numeral M(sf_encode representation_closure_condition)).
Proof.
 destruct(source_finite_names_total M 8(fun i=>code_numeral M(RNC_coordinate_name i))(zeroM M))as(b&c&HNames).
 assert(HMap:forall i v,code_relation M(fun _=>zeroM M)(CEconst(RNC_coordinate_name i))v ->
   renaming_lookup M b c(code_numeral M 8)(zeroM M)(code_numeral M i)v).
 { intros i v HV. change(v=code_numeral M(RNC_coordinate_name i))in HV. subst v.
   destruct(Nat.lt_ge_cases i 8)as[HI|HI];[exact(HNames i HI)|].
   rewrite(RNC_coordinate_tail i HI).
   apply(proj2(renaming_lookup_outside M b c(code_numeral M 8)(zeroM M)(code_numeral M i)(code_numeral M i)
    ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M i 8))in H;lia))).
   symmetry. apply coding_add_zero_r. }
 exists b,c. split;[exact(HNames 1 ltac:(lia))|]. split;[exact(HNames 2 ltac:(lia))|].
 split;[exact(HNames 7 ltac:(lia))|]. split.
 - apply(source_finite_parameter_renaming M named_difference_successor(fun i=>CEconst(RNC_coordinate_name i))
    (fun _=>zeroM M)b c(code_numeral M 8)(zeroM M)_ HMap).
   rewrite <-RNC_coordinate_successor.
   exact(source_parameter_substitution_calibration M named_difference_successor RNC_coordinate_substitution).
 - apply(source_finite_parameter_renaming M named_difference_closure(fun i=>CEconst(RNC_coordinate_name i))
    (fun _=>zeroM M)b c(code_numeral M 8)(zeroM M)_ HMap).
   rewrite <-RNC_coordinate_closure.
   exact(source_parameter_substitution_calibration M named_difference_closure RNC_coordinate_substitution).
Qed.

Print Assumptions source_representation_conjunction_coordinates_total.
