(** Source assumption contexts recognized by an arbitrary unary arithmetic
    axiom descriptor. NumericalTheory supplies only that formula, not a calculus. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalTheories
  NumericalContexts SourceBounded ContextCombination SourceClosedContextShift.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_axiom_context M T b c n :=
  context_bounded M b c n (zeroM M) /\
  forall f,context_member M b c n f -> theory_axiom M T f.
Definition source_axiom_context_formula T (b c n:term) : form :=
  context_bounded_formula b c n zero ∧
    ∀ (context_member_formula b`[↑] c`[↑] n`[↑] $0 → theory_axiom_instance T $0).
Local Opaque holds context_bounded_formula context_member_formula theory_axiom_instance.

Theorem source_axiom_context_formula_correct M T rho b c n :
  holds M rho (source_axiom_context_formula T b c n) <->
  source_axiom_context M T (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold source_axiom_context_formula,source_axiom_context.
  rewrite holds_and. setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_bounded_formula_correct. setoid_rewrite context_member_formula_correct.
  setoid_rewrite theory_axiom_instance_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_axiom_context_empty M T :
  source_axiom_context M T (zeroM M) (zeroM M) (zeroM M).
Proof.
  split;[apply context_bounded_empty|]. intros f HF. exfalso.
  exact (context_empty M (zeroM M) (zeroM M) f HF).
Qed.

Theorem source_axiom_context_union M T b c n d e m u v l :
  source_axiom_context M T b c n -> source_axiom_context M T d e m ->
  context_union M b c n d e m u v l -> source_axiom_context M T u v l.
Proof.
  intros [HB HA] [HD HE] HU. split.
  - exact (source_context_union_bounded M b c n d e m u v l (zeroM M) HU HB HD).
  - intros f HF. apply (proj2 HU f) in HF. destruct HF as [HF|HF];auto.
Qed.

Print Assumptions source_axiom_context_formula_correct.
Print Assumptions source_axiom_context_union.
