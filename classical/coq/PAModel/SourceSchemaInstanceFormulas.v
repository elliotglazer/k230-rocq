(** Public arithmetic formulas for the open numerical schema-instance
    graphs, including arbitrary model-valued matrices and closure lengths. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SourceBounded
  NumericalZFCAxioms NumericalZFCClosure NumericalCoreAxioms NumericalZFRAxioms
  NumericalTheories SourceSetTheoryDescriptors SchemaRenamingDescriptors SetSchemaConstructors NumericalSetClosure.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_separation_instance_formula (phi n z:term) : form :=
  source_bounded_accept_formula phi (σ n) ∧
  ∃∃ (schema_renaming_formula SepBody (code_lift2 phi) $1 ∧
    (sf_separation_constructor_formula $1 $0 ∧ all_prefix_formula (code_lift2 n) $0 (code_lift2 z))).
Definition source_replacement_instance_formula (phi n z:term) : form :=
  source_bounded_accept_formula phi (σ (σ n)) ∧
  ∃∃∃∃ (schema_renaming_formula RepA (lift4 phi) $3 ∧
    (schema_renaming_formula RepB (lift4 phi) $2 ∧
    (schema_renaming_formula RepC (lift4 phi) $1 ∧
    (sf_replacement_constructor_formula $3 $2 $1 $0 ∧ all_prefix_formula (lift4 n) $0 (lift4 z))))).
Local Opaque holds source_bounded_accept_formula schema_renaming_formula
  sf_separation_constructor_formula sf_replacement_constructor_formula all_prefix_formula.

Theorem source_separation_instance_formula_correct M rho phi n z :
  holds M rho (source_separation_instance_formula phi n z) <->
  numerical_separation_instance M (evalM M rho phi) (evalM M rho n) (evalM M rho z).
Proof.
  unfold source_separation_instance_formula,numerical_separation_instance.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite schema_renaming_formula_correct.
  setoid_rewrite sf_separation_constructor_correct. setoid_rewrite all_prefix_formula_correct.
  unfold evalM,code_lift2. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_replacement_instance_formula_correct M rho phi n z :
  holds M rho (source_replacement_instance_formula phi n z) <->
  numerical_replacement_instance M (evalM M rho phi) (evalM M rho n) (evalM M rho z).
Proof.
  unfold source_replacement_instance_formula,numerical_replacement_instance.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite schema_renaming_formula_correct.
  setoid_rewrite sf_replacement_constructor_correct. setoid_rewrite all_prefix_formula_correct.
  unfold evalM,lift4. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_separation_instance_zfr_axiom M phi n z :
  numerical_separation_instance M phi n z -> theory_axiom M ZFRSourceDescriptor z.
Proof.
  intro H. apply ZFRSourceDescriptor_axiom. left. right. left.
  split;[exact (numerical_separation_instance_closed M phi n z H)|]. now exists phi,n.
Qed.
Theorem source_replacement_instance_zfr_axiom M phi n z :
  numerical_replacement_instance M phi n z -> theory_axiom M ZFRSourceDescriptor z.
Proof.
  intro H. apply ZFRSourceDescriptor_axiom. left. right. right.
  split;[exact (numerical_replacement_instance_closed M phi n z H)|]. now exists phi,n.
Qed.

Print Assumptions source_separation_instance_formula_correct.
Print Assumptions source_replacement_instance_formula_correct.
Print Assumptions source_separation_instance_zfr_axiom.
Print Assumptions source_replacement_instance_zfr_axiom.
