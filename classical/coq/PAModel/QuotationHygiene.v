(** Freshness invariant for the numerical quotient translator. Totality of
    the raw translation does not require this invariant; any later semantic
    or proof-preservation theorem must avoid capturing live variable names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NumericalEnvironments.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition environment_below M b c n k :=
  forall i v, environment_lookup M b c n i v -> coding_lt M v k.
Definition environment_below_formula (b c n k : term) : form :=
  ∀∀ (environment_lookup_formula (code_lift2 b) (code_lift2 c)
    (code_lift2 n) $1 $0 → Peano.sless $0 (code_lift2 k)).

Local Opaque holds environment_lookup_formula Peano.sless.
Lemma environment_below_formula_correct M rho b c n k :
  holds M rho (environment_below_formula b c n k) <->
  environment_below M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho k).
Proof.
  unfold environment_below_formula,environment_below.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite environment_lookup_formula_correct. setoid_rewrite less_formula_correct.
  repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Definition quotation_safe M b c n k t := coding_lt M t k /\ environment_below M b c n k.
Definition quotation_safe_formula (b c n k t : term) : form :=
  Peano.sless t k ∧ environment_below_formula b c n k.

Lemma quotation_safe_formula_correct M rho b c n k t :
  holds M rho (quotation_safe_formula b c n k t) <->
  quotation_safe M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho k) (evalM M rho t).
Proof.
  unfold quotation_safe_formula,quotation_safe.
  rewrite holds_and,less_formula_correct,environment_below_formula_correct. reflexivity.
Qed.

Lemma environment_below_empty M b c k : coding_lt M (zeroM M) k ->
  environment_below M b c (zeroM M) k.
Proof.
  intros H i v Hv. apply environment_empty in Hv. now subst v.
Qed.

Lemma environment_below_cons M b c n k d e m :
  environment_below M b c n k -> environment_cons M b c n k d e m ->
  environment_below M d e m (succM M k).
Proof.
  intros Hsafe Hcons i v Hv.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [Hi|[j Hi]]; subst i.
  - apply (environment_cons_head M b c n k d e m v Hcons) in Hv.
    subst v. apply coding_lt_succ.
  - apply (environment_cons_tail M b c n k d e m j v Hcons) in Hv.
    exact (coding_lt_trans M v k (succM M k) (Hsafe j v Hv) (coding_lt_succ M k)).
Qed.

Theorem quotation_safe_cons M b c n k t d e m :
  quotation_safe M b c n k t -> environment_cons M b c n k d e m ->
  quotation_safe M d e m (succM M k) t.
Proof.
  intros [Ht Henv] Hcons. split.
  - exact (coding_lt_trans M t k (succM M k) Ht (coding_lt_succ M k)).
  - exact (environment_below_cons M b c n k d e m Henv Hcons).
Qed.

Theorem quotation_safe_empty M :
  quotation_safe M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) (zeroM M).
Proof.
  split; [apply coding_lt_succ|]. apply environment_below_empty. apply coding_lt_succ.
Qed.

Print Assumptions environment_below_formula_correct.
Print Assumptions quotation_safe_formula_correct.
Print Assumptions environment_below_cons.
Print Assumptions quotation_safe_cons.
Print Assumptions quotation_safe_empty.
