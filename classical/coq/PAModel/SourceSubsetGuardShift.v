(** The emitted closure's literal subset guard, shifted into the next
    binder scope, is the three-parameter subset shell at B=5,X=3,U=1. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceNumeralLift ZFCFiniteSourceCodes SetSchemaConstructors SourceEmittedClosureRecipe
  SourceFiniteParameters SourceFiniteParameterProofs SourceSubsetClosedPoint
  NumericalRenaming SourceQuantifierRules.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition source_emitted_subset_guard :sf_form :=∀($0 ∈' $1 → $0 ∈' $3).

Theorem source_emitted_subset_guard_shift M env guard shifted :
  code_relation M env E_native_subset02 guard ->source_formula_shift M guard shifted ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names (source_point_raw_subset $2 $1)) shifted.
Proof.
  intros HG HS.
  assert (HG0:code_relation M (fun _=>zeroM M) E_native_subset02 guard) by exact HG.
  pose proof(source_formula_numeral_graph M source_emitted_subset_guard) as HGuard.
  change (code_relation M (fun _=>zeroM M) E_native_subset02
    (code_numeral M(sf_encode source_emitted_subset_guard))) in HGuard.
  rewrite(code_relation_functional M E_native_subset02 (fun _=>zeroM M)
    guard (code_numeral M(sf_encode source_emitted_subset_guard)) HG0 HGuard) in HS.
  rewrite(numerical_renaming_functional M (code_numeral M(sf_encode source_emitted_subset_guard))
    (zeroM M)(zeroM M)(zeroM M)(succM M(zeroM M)) shifted
    (code_numeral M(sf_encode(subst_form ↑ source_emitted_subset_guard)))
    HS (source_formula_numeral_shift M source_emitted_subset_guard)).
  set (E:=source_parameter_expression source_three_parameter_names (source_point_raw_subset $2 $1)).
  pose proof(code_relation_numeral M (schema_env3 5 3 1) E) as HT.
  assert (HE:code_value (schema_env3 5 3 1) E=sf_encode(subst_form ↑ source_emitted_subset_guard)).
  { unfold E,source_point_raw_subset,source_emitted_subset_guard.
    cbn[source_parameter_expression source_parameter_up source_three_parameter_names].
    rewrite !sf_make_value. reflexivity. }
  rewrite HE in HT.
  apply(proj1(code_relation_ext M E
    (fun i=>code_numeral M(schema_env3 5 3 1 i))
    (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    _ ltac:(intros[|[|i]];reflexivity))). exact HT.
Qed.

Print Assumptions source_emitted_subset_guard_shift.
