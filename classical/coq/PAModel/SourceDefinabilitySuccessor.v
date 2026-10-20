(** Exact fixed successor swapping and its actual singleton substitution. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceBoundMonotone SourceDefinabilityPrimitives NumericalSubstitutionMaps
 NumericalSubstitution NumericalInstantiation SubstitutionSource SourceSubstitutionBounds.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition source_def_succ10 :sf_form :=source_def_successor01[$1..].
Definition source_def_succ_exists :sf_form :=∃source_def_succ10.
Definition source_def_empty_exists :sf_form :=∃source_def_empty.
Theorem source_def_successor_swap M :numerical_instantiation M
 (code_numeral M(sf_encode source_def_successor01))(code_numeral M 1)
 (code_numeral M(sf_encode source_def_succ10)).
Proof.
 destruct(substitution_singleton_total M(code_numeral M 1))as(b&c&HH&HT).
 exists b,c. split;[exact HH|].
 exact(fixed_source_singleton_substitution M(fun _=>zeroM M) source_def_successor01($1) b c _ _
   HH(source_formula_numeral_graph M source_def_successor01)
   (source_formula_numeral_graph M source_def_succ10)).
Qed.
Theorem source_def_succ10_bound M :source_bounded M(code_numeral M(sf_encode source_def_succ10))(code_numeral M 2).
Proof.
 apply(numerical_instantiation_bounded M(code_numeral M(sf_encode source_def_successor01))
  (code_numeral M 1)(code_numeral M(sf_encode source_def_succ10))(code_numeral M 2)).
 - apply(source_bounded_monotone M _ (code_numeral M 2)(code_numeral M 3)(numerical_def_successor_bound M)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
 - apply coding_lt_succ_cancel,coding_zero_lt_succ.
 - apply source_def_successor_swap.
Qed.
Theorem source_def_succ_exists_graph M :sf_relation M SFEx
 (code_numeral M(sf_encode source_def_succ10))(zeroM M)
 (code_numeral M(sf_encode source_def_succ_exists)).
Proof. exact(sf_make_numeral M SFEx(sf_encode source_def_succ10) 0). Qed.
Theorem source_def_empty_exists_graph M :sf_relation M SFEx
 (code_numeral M(sf_encode source_def_empty))(zeroM M)
 (code_numeral M(sf_encode source_def_empty_exists)).
Proof. exact(sf_make_numeral M SFEx(sf_encode source_def_empty) 0). Qed.
Print Assumptions source_def_successor_swap.
Print Assumptions source_def_succ10_bound.

