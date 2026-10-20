(** Stable support quantifies over actual internally coded extensions of
    the local context. It never weakens an arbitrary contextual derivation. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs NumericalContexts
  NumericalEnvironments ContextualProofs ContextualLogic ContextualPropositional
  ContextSupport NumericalEquivalence ProofTemplates TemplateCD TemplatePropositional QuotientAtomTemplates
  QuotationPayloads SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition stable_context_support M b c n f :=
  forall d e m,context_included M b c n d e m -> contextually_provable M d e m f.
Definition stable_context_support_formula (b c n f : term) : form :=
  ∀∀∀ (context_included_formula (lift3 b) (lift3 c) (lift3 n) $2 $1 $0 →
    contextually_provable_formula $2 $1 $0 (lift3 f)).
Local Opaque holds context_included_formula contextually_provable_formula.
Lemma stable_context_support_formula_correct M rho b c n f :
  holds M rho (stable_context_support_formula b c n f) <->
  stable_context_support M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold stable_context_support_formula,stable_context_support.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_included_formula_correct.
  setoid_rewrite contextually_provable_formula_correct.
  setoid_rewrite lift3_correct. reflexivity.
Qed.
Lemma stable_context_support_definable M b c n :
  Definable1 M (stable_context_support M b c n).
Proof.
  exists (stable_context_support_formula $1 $2 $3 $0),(b .: c .: n .: fun _=>zeroM M).
  intro f. symmetry. apply stable_context_support_formula_correct.
Qed.

Theorem stable_context_support_global M b c n f :
  numerically_provable M f -> stable_context_support M b c n f.
Proof. intros HF d e m HI. now apply contextual_global. Qed.
Theorem stable_context_support_member M b c n f :
  context_member M b c n f -> stable_context_support M b c n f.
Proof. intros HF d e m HI. apply contextual_hyp,HI,HF. Qed.
Theorem stable_context_support_of_support M b c n f :
  context_support M b c n f -> stable_context_support M b c n f.
Proof.
  intros HF d e m HI. apply context_support_provable.
  exact (context_support_included M b c n d e m f HI HF).
Qed.
Theorem stable_context_support_here M b c n f :
  stable_context_support M b c n f -> contextually_provable M b c n f.
Proof. intro HF. apply HF,context_included_refl. Qed.
Theorem stable_context_support_included M b c n d e m f :
  context_included M b c n d e m -> stable_context_support M b c n f ->
  stable_context_support M d e m f.
Proof.
  intros HI HF p q l HJ. apply HF.
  exact (context_included_trans M b c n d e m p q l HI HJ).
Qed.
Theorem stable_context_support_cons M b c n h d e m f :
  environment_cons M b c n h d e m -> stable_context_support M b c n f ->
  stable_context_support M d e m f.
Proof.
  intros HC HF. apply (stable_context_support_included M b c n d e m f);[|exact HF].
  intros a HA. apply (proj2 (context_member_cons M b c n h d e m a HC)). now right.
Qed.
Theorem stable_context_support_mp M b c n a f h :
  implication_graph M a f h -> stable_context_support M b c n a ->
  stable_context_support M b c n h -> stable_context_support M b c n f.
Proof.
  intros HH HA HHs d e m HI.
  exact (contextual_mp M d e m a f h (HA d e m HI) (HHs d e m HI) HH).
Qed.
Theorem stable_context_support_implies M b c n a f :
  numerical_implies M a f -> stable_context_support M b c n a ->
  stable_context_support M b c n f.
Proof.
  intros HAF HA.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (a .: f .: fun _=>zeroM M)) as [h HH].
  apply (stable_context_support_mp M b c n a f h HH HA).
  apply stable_context_support_global,HAF,HH.
Qed.
Theorem stable_context_support_equivalent M b c n a f :
  numerical_equivalent M a f -> stable_context_support M b c n a ->
  stable_context_support M b c n f.
Proof. intros [HAF _]. now apply stable_context_support_implies. Qed.

Theorem stable_context_support_derivation M b c n rho inputs e :
  (forall d,In d inputs -> forall f,code_relation M rho d f -> stable_context_support M b c n f) ->
  template_derivation nil inputs e ->
  forall f,code_relation M rho e f -> stable_context_support M b c n f.
Proof.
  intros HS HP f HF d q l HI.
  apply (contextual_propositional_sound M d q l rho inputs e);[|exact HP|exact HF].
  intros a HA v HV. exact (HS a HA v HV d q l HI).
Qed.
Theorem stable_context_support_conjunction M b c n a f h :
  quotation_binary M SFAnd a f h -> stable_context_support M b c n a ->
  stable_context_support M b c n f -> stable_context_support M b c n h.
Proof.
  intros HH HA HF d e m HI.
  exact (contextual_conjunction_intro M d e m a f h (HA d e m HI) (HF d e m HI) HH).
Qed.
Theorem stable_context_support_conjunction_left M b c n a f h :
  quotation_binary M SFAnd a f h -> stable_context_support M b c n h ->
  stable_context_support M b c n a.
Proof.
  intros HH HS d e m HI. exact (contextual_conjunction_left M d e m a f h HH (HS d e m HI)).
Qed.
Theorem stable_context_support_conjunction_right M b c n a f h :
  quotation_binary M SFAnd a f h -> stable_context_support M b c n h ->
  stable_context_support M b c n f.
Proof.
  intros HH HS d e m HI. exact (contextual_conjunction_right M d e m a f h HH (HS d e m HI)).
Qed.

Print Assumptions stable_context_support_formula_correct.
Print Assumptions stable_context_support_definable.
Print Assumptions stable_context_support_of_support.
Print Assumptions stable_context_support_cons.
Print Assumptions stable_context_support_mp.
Print Assumptions stable_context_support_derivation.
Print Assumptions stable_context_support_conjunction.
