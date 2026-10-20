(** PA-definable proof invariant for eliminating an internally finite Dn. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalSourceFull SetFormulaCodes SourceBounded
 SourceRoleReopening SourceDn SourceDnAssignments NumericalContextRenaming.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Definition source_dn_parameter_proofs M count pb pc X gb gc gn:=forall i value member,
 coding_lt M i count ->beta M pb pc i value ->sf_relation M SFMember value X member ->
 source_full_prv M gb gc gn member.
Definition source_dn_parameter_proofs_formula(count pb pc X gb gc gn:term):form:=
 ∀∀∀(Peano.sless $2(context_lift3 count) →beta_formula(context_lift3 pb)(context_lift3 pc)$2 $1 →
 sf_formula SFMember $1(context_lift3 X)$0 →source_full_prv_formula(context_lift3 gb)(context_lift3 gc)(context_lift3 gn)$0).
Local Opaque holds beta_formula sf_formula source_full_prv_formula.
Theorem source_dn_parameter_proofs_formula_correct M rho count pb pc X gb gc gn:
 holds M rho(source_dn_parameter_proofs_formula count pb pc X gb gc gn)<->
 source_dn_parameter_proofs M(evalM M rho count)(evalM M rho pb)(evalM M rho pc)(evalM M rho X)
 (evalM M rho gb)(evalM M rho gc)(evalM M rho gn).
Proof.
 unfold source_dn_parameter_proofs_formula,source_dn_parameter_proofs.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct.
 setoid_rewrite source_full_prv_formula_correct. setoid_rewrite context_eval_lift3. reflexivity.
Qed.
Definition source_dn_elimination_at M count:=forall body dn d X rb rc pc pb pC ab ac result gb gc gn,
 source_bounded M body(succM M(succM M count)) ->source_dn M count body dn ->
 source_role_reopening M X d rb rc ->numerical_substitution M dn rb rc(code_numeral M 2)(code_numeral M 2)pc ->
 source_dn_assignment M count pb pC d X ab ac ->
 numerical_substitution M body ab ac(succM M(succM M count))(zeroM M)result ->
 source_full_prv M gb gc gn pc ->source_dn_parameter_proofs M count pb pC X gb gc gn ->
 source_full_prv M gb gc gn result.
Definition source_dn_elimination_formula:form:=
 ∀∀∀∀∀∀∀∀∀∀∀∀∀∀∀(
 source_bounded_accept_formula $14(σ(σ $15)) →source_dn_formula $15 $14 $13 →
 (substitution_lookup_formula $10 $9(num 2)zero zero $12 ∧substitution_lookup_formula $10 $9(num 2)zero(num 1)$11) →
 numerical_substitution_formula $13 $10 $9(num 2)(num 2)$8 →
 source_dn_assignment_formula $15 $7 $6 $12 $11 $5 $4 →
 numerical_substitution_formula $14 $5 $4(σ(σ $15))zero $3 →
 source_full_prv_formula $2 $1 $0 $8 →source_dn_parameter_proofs_formula $15 $7 $6 $11 $2 $1 $0 →
 source_full_prv_formula $2 $1 $0 $3).
Local Opaque source_bounded_accept_formula source_dn_formula substitution_lookup_formula
 numerical_substitution_formula source_dn_assignment_formula source_dn_parameter_proofs_formula.
Theorem source_dn_elimination_definable M:Definable1 M(source_dn_elimination_at M).
Proof.
 exists source_dn_elimination_formula,(fun _=>zeroM M). intro count.
 unfold source_dn_elimination_formula,source_dn_elimination_at,source_role_reopening.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp. setoid_rewrite holds_and.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite substitution_lookup_formula_correct. setoid_rewrite numerical_substitution_formula_correct.
 setoid_rewrite source_dn_assignment_formula_correct. setoid_rewrite source_full_prv_formula_correct.
 setoid_rewrite source_dn_parameter_proofs_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Print Assumptions source_dn_parameter_proofs_formula_correct.
Print Assumptions source_dn_elimination_definable.
