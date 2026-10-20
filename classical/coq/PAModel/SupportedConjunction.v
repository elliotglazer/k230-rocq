(** Stable support for each component of an assumed conjunction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence ProofTemplates TemplateCD TemplatePropositional NumericalVacuitySteps NamedLeibnizSteps
  QuotationPayloads SetFormulaCodes ContextSupport.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma supported_conjunction_left_implies M a b f :
  quotation_binary M SFAnd a b f -> numerical_implies M f a.
Proof.
  intro HF. apply (proj1 (numerical_implies_expression M
    (a .: b .: fun _=>zeroM M) (E_wa (CEvar 0) (CEvar 1)) (CEvar 0) f a HF eq_refl)).
  apply ns_proof_template,template_discharge,template_deduction.
  apply (template_der_andl nil _ (CEvar 0) (CEvar 1)),dhyp. cbn;auto.
Qed.
Lemma supported_conjunction_right_implies M a b f :
  quotation_binary M SFAnd a b f -> numerical_implies M f b.
Proof.
  intro HF. apply (proj1 (numerical_implies_expression M
    (a .: b .: fun _=>zeroM M) (E_wa (CEvar 0) (CEvar 1)) (CEvar 1) f b HF eq_refl)).
  apply ns_proof_template,template_discharge,template_deduction.
  apply (template_der_andr nil _ (CEvar 0) (CEvar 1)),dhyp. cbn;auto.
Qed.
Lemma context_support_conjunction_left M cb cc cn a b f :
  quotation_binary M SFAnd a b f -> context_support M cb cc cn f -> context_support M cb cc cn a.
Proof. intros HF HS. exact (context_support_implies M cb cc cn f a HS (supported_conjunction_left_implies M a b f HF)). Qed.
Lemma context_support_conjunction_right M cb cc cn a b f :
  quotation_binary M SFAnd a b f -> context_support M cb cc cn f -> context_support M cb cc cn b.
Proof. intros HF HS. exact (context_support_implies M cb cc cn f b HS (supported_conjunction_right_implies M a b f HF)). Qed.
Print Assumptions context_support_conjunction_left.
Print Assumptions context_support_conjunction_right.
