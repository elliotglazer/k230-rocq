From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalContexts
  NumericalSourceFull SourceRelativization.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_images M domain b c n tb tc tn := forall f g,
  context_member M b c n f -> source_relativization M domain f g -> source_full_prv M tb tc tn g.
Definition source_context_images_formula (domain b c n tb tc tn:term) : form :=
  ∀∀ (context_member_formula (code_lift2 b) (code_lift2 c) (code_lift2 n) $1 →
    source_relativization_formula (code_lift2 domain) $1 $0 →
    source_full_prv_formula (code_lift2 tb) (code_lift2 tc) (code_lift2 tn) $0).
Local Opaque holds context_member_formula source_relativization_formula source_full_prv_formula.

Theorem source_context_images_formula_correct M rho domain b c n tb tc tn :
  holds M rho (source_context_images_formula domain b c n tb tc tn) <->
  source_context_images M (evalM M rho domain) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho tb) (evalM M rho tc) (evalM M rho tn).
Proof.
  unfold source_context_images_formula,source_context_images.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Print Assumptions source_context_images_formula_correct.
