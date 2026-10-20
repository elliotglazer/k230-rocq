(** Unary axiom descriptors for the existing current-library core and ZFC
    predicates and for core plus fixed Foundation. They do not change the
    source proof calculus or the meaning of existing provability predicates. *)
From PAModel Require Import Model NumericalTheories NumericalContexts NumericalSourceFull
  NumericalCoreAxioms NumericalZFCAxioms NumericalZFRAxioms ClosedSourceQuotation
  CoreConsistencyReduction SourceZFCProvability SourceAxiomContexts SourceDescriptorProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition CoreSourceDescriptor : NumericalTheory :=
  {| theory_formula:=numerical_zfc_core_source_axiom_formula $0;
     theory_bounded:=numerical_zfc_core_source_axiom_unary |}.
Definition ZFRSourceDescriptor : NumericalTheory :=
  {| theory_formula:=numerical_zfr_source_axiom_formula $0;
     theory_bounded:=numerical_zfr_source_axiom_unary |}.
Definition ZFCSourceDescriptor : NumericalTheory :=
  {| theory_formula:=numerical_zfc_source_axiom_formula $0;
     theory_bounded:=numerical_zfc_source_axiom_unary |}.

Theorem CoreSourceDescriptor_axiom M f :
  theory_axiom M CoreSourceDescriptor f <-> numerical_zfc_core_source_axiom M f.
Proof. apply numerical_zfc_core_source_axiom_formula_correct. Qed.
Theorem ZFRSourceDescriptor_axiom M f :
  theory_axiom M ZFRSourceDescriptor f <-> numerical_zfr_source_axiom M f.
Proof. apply numerical_zfr_source_axiom_formula_correct. Qed.
Theorem ZFCSourceDescriptor_axiom M f :
  theory_axiom M ZFCSourceDescriptor f <-> numerical_zfc_source_axiom M f.
Proof. apply numerical_zfc_source_axiom_formula_correct. Qed.

Theorem source_core_descriptor_context M b c n :
  source_axiom_context M CoreSourceDescriptor b c n <-> source_core_context M b c n.
Proof.
  split.
  - intros [_ H] f HF. apply CoreSourceDescriptor_axiom. exact (H f HF).
  - intro H. split;[exact (source_core_context_closed M b c n H)|].
    intros f HF. apply CoreSourceDescriptor_axiom. exact (H f HF).
Qed.

Theorem source_zfc_descriptor_context M b c n :
  source_axiom_context M ZFCSourceDescriptor b c n <-> source_zfc_context M b c n.
Proof.
  split.
  - intros [_ H] f HF. apply ZFCSourceDescriptor_axiom. exact (H f HF).
  - intro H. split;[exact (source_zfc_context_closed M b c n H)|].
    intros f HF. apply ZFCSourceDescriptor_axiom. exact (H f HF).
Qed.

Theorem source_core_descriptor_provable M f :
  source_descriptor_provable M CoreSourceDescriptor f <-> source_core_provable M f.
Proof.
  unfold source_descriptor_provable,source_core_provable.
  setoid_rewrite source_core_descriptor_context. reflexivity.
Qed.

Theorem source_zfc_descriptor_provable M f :
  source_descriptor_provable M ZFCSourceDescriptor f <-> source_zfc_provable M f.
Proof.
  unfold source_descriptor_provable,source_zfc_provable.
  setoid_rewrite source_zfc_descriptor_context. reflexivity.
Qed.

Print Assumptions CoreSourceDescriptor_axiom.
Print Assumptions ZFRSourceDescriptor_axiom.
Print Assumptions ZFCSourceDescriptor_axiom.
Print Assumptions source_core_descriptor_context.
Print Assumptions source_zfc_descriptor_context.
Print Assumptions source_core_descriptor_provable.
Print Assumptions source_zfc_descriptor_provable.
