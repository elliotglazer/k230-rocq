(** Numeral calibration of the literal three-role difference operation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceFiniteParameters
 SourceFiniteParameterProofs SourceParameterGraphs SourceNamedFiniteCalibration SourceDifferenceProfile
 SourceRepresentationDifferencePoints SourceRepresentationDifferencePadding.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition difference_numeral_substitution x y r i :sf_term :=match i with
 |0=>$(x)|1=>$(y)|2=>$(r)|_=>$(i)end.
Lemma difference_operation_substitution x y r :
 (source_difference_operation $0 $1 $2)[difference_numeral_substitution x y r]=
 source_difference_operation $(x) $(y) $(r).
Proof. reflexivity. Qed.
Theorem source_difference_operation_numeral_graph M x y r :
 code_relation M(difference_values M(code_numeral M x)(code_numeral M y)(code_numeral M r))
 source_difference_operation_expression(code_numeral M(sf_encode(source_difference_operation $(x) $(y) $(r)))).
Proof.
 unfold source_difference_operation_expression.
 apply(proj2(source_parameter_graph_ext M 3(source_difference_operation $0 $1 $2)
  source_difference_operation_bounded source_three_parameter_names
  (fun i=>CEconst(sf_index(difference_numeral_substitution x y r i)))
  (difference_values M(code_numeral M x)(code_numeral M y)(code_numeral M r))(fun _=>zeroM M)
  ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)_)).
 rewrite <-difference_operation_substitution.
 exact(source_parameter_substitution_calibration M(source_difference_operation $0 $1 $2)
  (difference_numeral_substitution x y r)).
Qed.
Print Assumptions source_difference_operation_numeral_graph.
