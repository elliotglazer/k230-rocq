(** ZFR here is precisely the current ZFc source predicate plus the fixed
    ZFCFoundation source graph. Choice is not included. No old-library
    identification or interpretation claim is made in this definition. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalCoreAxioms NumericalZFCAxioms ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  FixedSourceBounds SourceBounded StandardModel SetFormulaCodes SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_zfr_source_axiom M z :=
  numerical_zfc_core_source_axiom M z \/ zfc_source_graph M ZFCFoundation z.
Definition numerical_zfr_source_axiom_formula (z:term) : form :=
  numerical_zfc_core_source_axiom_formula z ∨ zfc_source_graph_formula ZFCFoundation z.
Local Opaque holds numerical_zfc_core_source_axiom_formula zfc_source_graph_formula.

Theorem numerical_zfr_source_axiom_formula_correct M rho z :
  holds M rho (numerical_zfr_source_axiom_formula z) <->
  numerical_zfr_source_axiom M (evalM M rho z).
Proof.
  unfold numerical_zfr_source_axiom_formula,numerical_zfr_source_axiom.
  rewrite holds_or,numerical_zfc_core_source_axiom_formula_correct,
    zfc_source_graph_formula_correct. reflexivity.
Qed.

Theorem numerical_zfr_source_axiom_unary :
  bounded 1 (numerical_zfr_source_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem numerical_zfr_source_axiom_closed M z :
  numerical_zfr_source_axiom M z -> source_bounded M z (zeroM M).
Proof.
  intros [H|H].
  - exact (numerical_zfc_core_source_axiom_closed M z H).
  - exact (zfc_source_graph_closed M ZFCFoundation z H).
Qed.

Theorem numerical_core_source_axiom_in_zfr M z :
  numerical_zfc_core_source_axiom M z -> numerical_zfr_source_axiom M z.
Proof. now left. Qed.

Theorem numerical_zfr_source_axiom_in_zfc M z :
  numerical_zfr_source_axiom M z -> numerical_zfc_source_axiom M z.
Proof.
  intros [H|H].
  - exact (numerical_zfc_core_source_axiom_in_zfc M z H).
  - left. now exists ZFCFoundation.
Qed.

Definition standard_zfr_source_axiom (psi:sf_form) :=
  standard_zfc_core_source_axiom psi \/ psi=source_foundation.

Theorem numerical_zfr_source_axiom_standard_exact z :
  numerical_zfr_source_axiom natModel z <->
  exists psi:sf_form,standard_zfr_source_axiom psi /\ sf_encode psi=z.
Proof.
  unfold numerical_zfr_source_axiom,standard_zfr_source_axiom. split.
  - intros [H|H].
    + destruct (proj1 (numerical_zfc_core_source_axiom_standard_exact z) H)
        as [psi [HA HC]]. exists psi. auto.
    + exists source_foundation. split;[now right|].
      unfold zfc_source_graph in H. rewrite code_relation_natModel,
        zfc_fixed_source_expression_value in H. symmetry. exact H.
  - intros [psi [[HA|HA] HC]].
    + left. apply numerical_zfc_core_source_axiom_standard_exact. exists psi. auto.
    + right. subst psi. unfold zfc_source_graph.
      rewrite code_relation_natModel,zfc_fixed_source_expression_value.
      symmetry. exact HC.
Qed.

Print Assumptions numerical_zfr_source_axiom_formula_correct.
Print Assumptions numerical_zfr_source_axiom_unary.
Print Assumptions numerical_zfr_source_axiom_closed.
Print Assumptions numerical_zfr_source_axiom_in_zfc.
Print Assumptions numerical_zfr_source_axiom_standard_exact.
