(** Internally finite assignment tables shifted in their values only.
    This differs from binder lifting, which also inserts an index-zero row. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming NumericalRenamingMaps RenamingSubstitution
 SourceBounded SourceQuantifierRules SourceBoundedMapComposition SourceSubstitutionComposition.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_parameter_value_shift M count pb pc qb qc:=forall i v,
 coding_lt M i count ->beta M pb pc i v ->beta M qb qc i(succM M v).
Definition source_parameter_value_shift_formula(count pb pc qb qc:term):form:=
 ∀∀(Peano.sless $1 count`[↑]`[↑] →
  beta_formula pb`[↑]`[↑] pc`[↑]`[↑] $1 $0 →
  beta_formula qb`[↑]`[↑] qc`[↑]`[↑] $1(σ $0)).
Local Opaque holds beta_formula.
Theorem source_parameter_value_shift_formula_correct M rho count pb pc qb qc:
 holds M rho(source_parameter_value_shift_formula count pb pc qb qc)<->
 source_parameter_value_shift M(evalM M rho count)(evalM M rho pb)(evalM M rho pc)
  (evalM M rho qb)(evalM M rho qc).
Proof.
 unfold source_parameter_value_shift_formula,source_parameter_value_shift.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
 unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Lemma source_zero_prefix_shift_lookup M i:
 substitution_lookup M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)i(succM M i).
Proof.
 apply substitution_lookup_outside;[apply coding_not_lt_zero|].
 exists i. split;[symmetry;apply Arithmetic.add_zero|].
 cbn[code_numeral]. now rewrite Arithmetic.add_succ,Arithmetic.add_zero.
Qed.
Theorem source_parameter_value_shift_total M count pb pc:exists qb qc,
 source_parameter_value_shift M count pb pc qb qc.
Proof.
 destruct(bounded_substitution_composition_map M pb pc count(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)count)as(qb&qc&HQ).
 exists qb,qc. intros i v HI HV.
 apply(proj1(substitution_lookup_inside M qb qc count(zeroM M)i(succM M v)HI)).
 apply(proj2(HQ i(succM M v)HI)). exists v. split.
 - exact(proj2(substitution_lookup_inside M pb pc count(zeroM M)i v HI)HV).
 - apply source_zero_prefix_shift_lookup.
Qed.
Theorem source_parameter_value_shift_substitution M count phi assigned shifted pb pc qb qc:
 source_bounded M phi count ->numerical_substitution M phi pb pc count(zeroM M)assigned ->
 source_formula_shift M assigned shifted ->source_parameter_value_shift M count pb pc qb qc ->
 numerical_substitution M phi qb qc count(zeroM M)shifted.
Proof.
 intros BF HA HS HQ.
 apply(numerical_substitution_composition M phi count pb pc count(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)qb qc count(zeroM M)assigned shifted BF HA
  (proj1(numerical_renaming_empty_substitution M assigned(zeroM M)(zeroM M)(code_numeral M 1)shifted)HS)).
 intros i j v HI HJ HV.
 assert(E:v=succM M j)by(eapply substitution_lookup_functional;[exact HV|apply source_zero_prefix_shift_lookup]).
 subst v. apply(proj2(substitution_lookup_inside M qb qc count(zeroM M)i(succM M j)HI)).
 exact(HQ i j HI(proj1(substitution_lookup_inside M pb pc count(zeroM M)i j HI)HJ)).
Qed.
Print Assumptions source_parameter_value_shift_formula_correct.
Print Assumptions source_parameter_value_shift_total.
Print Assumptions source_parameter_value_shift_substitution.
