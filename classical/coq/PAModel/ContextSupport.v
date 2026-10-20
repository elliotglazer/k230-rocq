(** Stable realizers for assumptions in a target context. A supported
    formula is a K theorem or follows by one globally proved implication
    from a context member. This support is preserved when a local assumption
    is added, without any invalid unrestricted contextual generalization. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence NumericalContexts NumericalEnvironments ContextualProofs.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_support M b c n f := numerically_provable M f \/
  exists h,context_member M b c n h /\ numerical_implies M h f.
Definition context_support_formula (b c n f : term) : form :=
  numerically_provable_formula f ∨
  ∃ (context_member_formula b`[↑] c`[↑] n`[↑] $0 ∧ numerical_implies_formula $0 f`[↑]).
Local Opaque holds numerically_provable_formula context_member_formula numerical_implies_formula.
Lemma context_support_formula_correct M rho b c n f :
  holds M rho (context_support_formula b c n f) <->
  context_support M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold context_support_formula,context_support.
  rewrite holds_or,holds_ex. setoid_rewrite holds_and.
  rewrite numerically_provable_formula_correct.
  setoid_rewrite context_member_formula_correct. setoid_rewrite numerical_implies_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem context_support_member M b c n f : context_member M b c n f -> context_support M b c n f.
Proof.
  intro HF. right. exists f. split;[exact HF|exact (proj1 (numerical_equivalent_refl M f))].
Qed.
Theorem context_support_provable M b c n f : context_support M b c n f -> contextually_provable M b c n f.
Proof.
  intros [HF|[h [HH HF]]].
  - now apply contextual_global.
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (h .: f .: fun _=>zeroM M)) as [imp HI].
    exact (contextual_mp M b c n h f imp (contextual_hyp M b c n h HH)
      (contextual_global M b c n imp (HF imp HI)) HI).
Qed.
Theorem context_support_implies M b c n a f :
  context_support M b c n a -> numerical_implies M a f -> context_support M b c n f.
Proof.
  intros [HA|[h [HH HA]]] HAF.
  - left. exact (numerical_implies_apply M a f HAF HA).
  - right. exists h. split;[exact HH|exact (numerical_implies_trans M h a f HA HAF)].
Qed.
Theorem context_support_equivalent M b c n a f :
  context_support M b c n a -> numerical_equivalent M a f -> context_support M b c n f.
Proof. intros HA [HAF _]. exact (context_support_implies M b c n a f HA HAF). Qed.
Theorem context_support_included M b c n d e m f :
  context_included M b c n d e m -> context_support M b c n f -> context_support M d e m f.
Proof.
  intros H [HF|[h [HH HF]]];[now left|]. right. exists h. split;[exact (H h HH)|exact HF].
Qed.
Theorem context_support_cons M b c n h d e m f :
  environment_cons M b c n h d e m -> context_support M b c n f -> context_support M d e m f.
Proof.
  intros HC HF. apply (context_support_included M b c n d e m f);[|exact HF].
  intros q HQ. apply (proj2 (context_member_cons M b c n h d e m q HC)). now right.
Qed.

Print Assumptions context_support_formula_correct.
Print Assumptions context_support_cons.
