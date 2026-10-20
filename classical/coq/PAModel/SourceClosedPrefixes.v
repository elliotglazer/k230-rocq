(** Introducing and eliminating arbitrary internally finite universal
    prefixes in a closed source context. The induction predicate is PA-definable. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalSetClosure NumericalContexts SourceBounded SourceBoundMonotone
  SourceClosedContextShift SetFormulaCodes NumericalSourceFull SourceUniversalPropositional.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_full_all_intro_closed M b c n a all :
  context_bounded M b c n (zeroM M) -> sf_relation M SFAll a (zeroM M) all ->
  source_full_prv M b c n a -> source_full_prv M b c n all.
Proof.
  intros HClosed HAll HP.
  destruct (source_full_prv_wellformed M b c n a HP) as [k [HBound HCtx]].
  apply (full_source_AllI M b c n a all b c);[|exact HP| |exact HAll].
  - exists k. split;[|exact HCtx].
    apply (proj2 (source_bounded_accept_unary M SFAll a all k (or_introl eq_refl) HAll)).
    apply (source_bounded_monotone M a k (succM M k) HBound).
    apply coding_lt_succ_cases. left. apply coding_lt_succ.
  - exact (source_closed_context_shift_self M b c n HClosed).
Qed.

Definition source_closed_prefix_at M b c l n := forall body result,
  all_prefix M n body result ->
  (source_full_prv M b c l body <-> source_full_prv M b c l result).
Definition source_closed_prefix_formula : form :=
  ∀∀(all_prefix_formula $2 $1 $0 →
    ((source_full_prv_formula $3 $4 $5 $1 → source_full_prv_formula $3 $4 $5 $0) ∧
     (source_full_prv_formula $3 $4 $5 $0 → source_full_prv_formula $3 $4 $5 $1))).
Local Opaque holds all_prefix_formula source_full_prv_formula.

Lemma source_closed_prefix_definable M b c l :
  Definable1 M (source_closed_prefix_at M b c l).
Proof.
  exists source_closed_prefix_formula,(b .: c .: l .: fun _=>zeroM M). intro n.
  unfold source_closed_prefix_at,source_closed_prefix_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_imp.
  setoid_rewrite all_prefix_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  reflexivity.
Qed.

Theorem source_full_closed_prefix M b c l :
  context_bounded M b c l (zeroM M) -> forall n,source_closed_prefix_at M b c l n.
Proof.
  intro HClosed. apply (definable_induction M (source_closed_prefix_at M b c l)
    (source_closed_prefix_definable M b c l)).
  - intros body result HP. apply all_prefix_zero_forward in HP. now subst result.
  - intros n IH body result HP.
    destruct (all_prefix_succ_forward M n body result HP) as [previous [HPrevious HAll]].
    split.
    + intro PB. apply (source_full_all_intro_closed M b c l previous result HClosed HAll).
      exact (proj1 (IH body previous HPrevious) PB).
    + intro PR. apply (proj2 (IH body previous HPrevious)).
      exact (source_full_all_shift M b c l previous result b c HAll PR
        (source_closed_context_shift_self M b c l HClosed)).
Qed.

Theorem source_full_prefix_eliminate M b c l n body result :
  context_bounded M b c l (zeroM M) -> all_prefix M n body result ->
  source_full_prv M b c l result -> source_full_prv M b c l body.
Proof. intros HC HP. exact (proj2 (source_full_closed_prefix M b c l HC n body result HP)). Qed.

Theorem source_full_prefix_introduce M b c l n body result :
  context_bounded M b c l (zeroM M) -> all_prefix M n body result ->
  source_full_prv M b c l body -> source_full_prv M b c l result.
Proof. intros HC HP. exact (proj1 (source_full_closed_prefix M b c l HC n body result HP)). Qed.

Print Assumptions source_full_all_intro_closed.
Print Assumptions source_closed_prefix_definable.
Print Assumptions source_full_closed_prefix.
Print Assumptions source_full_prefix_eliminate.
Print Assumptions source_full_prefix_introduce.
