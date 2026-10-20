(** The feasibility milestone: numerical proof-search soundness in arbitrary
    PA models. In particular, N need not be a standard model element. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs KernelSafety SearchStep RunSyntax.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_run_preserves_invariant M b c N s0 :
  numerical_run_from M b c N s0 -> invariant M s0 ->
  forall s, state_at M b c N s -> invariant M s.
Proof.
  intros [Hstart Hstep] Hinitial.
  assert (H : forall k, coding_lt M k (succM M N) -> safe_at M b c k).
  { apply (definable_induction M
      (fun k => coding_lt M k (succM M N) -> safe_at M b c k)
      (safe_at_definable M b c N)).
    - intros _ s Hs.
      pose proof (state_at_functional M b c (zeroM M) s s0 Hs Hstart) as E.
      now subst s.
    - intros k IH Hbound s Hs.
      assert (Hk : coding_lt M k N) by
        (apply coding_lt_succ_cancel; exact Hbound).
      assert (Hk' : coding_lt M k (succM M N)) by
        (apply coding_lt_succ_cases; now left).
      destruct (state_at_total M b c k) as [previous Hp].
      apply (invariant_step M previous s (IH Hk' previous Hp)).
      exact (Hstep k previous s Hk Hp Hs). }
  exact (H N (coding_lt_succ M N)).
Qed.

Theorem uniform_numerical_search_sound M b c N :
  numerical_run M b c N -> halt_at M b c N ->
  numerically_provable M (code_numeral M 1).
Proof.
  intros Hrun [s [Hs Hhalt]].
  apply (invariant_halt M s); [|exact Hhalt].
  exact (numerical_run_preserves_invariant M b c N (seed_state M)
    Hrun (invariant_seed M) s Hs).
Qed.

Definition numerical_search_soundness_sentence : form :=
  ∀∀∀ ((run_formula $2 $1 $0 ∧ halt_at_formula $2 $1 $0) →
    numerically_provable_formula (num 1)).

Local Opaque holds run_formula halt_at_formula numerically_provable_formula.

Theorem numerical_search_soundness_sentence_valid M rho :
  holds M rho numerical_search_soundness_sentence.
Proof.
  unfold numerical_search_soundness_sentence.
  rewrite holds_all. intro b. rewrite holds_all. intro c. rewrite holds_all. intro N.
  rewrite holds_imp, holds_and, run_formula_correct, halt_at_formula_correct,
    numerically_provable_formula_correct.
  intros [Hrun Hhalt]. exact (uniform_numerical_search_sound M b c N Hrun Hhalt).
Qed.
