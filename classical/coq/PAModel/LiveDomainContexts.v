(** Domain assumptions for live entries only. The context has length n;
    the default-zero value of the environment is not an assumption. A
    proof interpretation using this context must bound every index it uses. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions CodeDescent NumericalProofs NumericalEnvironments NumericalContexts
  DomainContexts ContextualProofs FormulaFreshConstructors QuotationHygiene SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition live_domain_context M b c n domain d e :=
  forall i f, coding_lt M i n -> beta M d e i f -> domain_context_entry M b c n domain i f.
Definition live_domain_context_formula (b c n domain d e : term) : form :=
  ∀∀ (Peano.sless $1 (code_lift2 n) → beta_formula (code_lift2 d) (code_lift2 e) $1 $0 →
    domain_context_entry_formula (code_lift2 b) (code_lift2 c) (code_lift2 n)
      (code_lift2 domain) $1 $0).
Local Opaque holds Peano.sless beta_formula domain_context_entry_formula.
Lemma live_domain_context_formula_correct M rho b c n domain d e :
  holds M rho (live_domain_context_formula b c n domain d e) <->
  live_domain_context M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho domain) (evalM M rho d) (evalM M rho e).
Proof.
  unfold live_domain_context_formula,live_domain_context.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite domain_context_entry_formula_correct.
  repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Theorem live_domain_context_total M b c n domain :
  exists d e, live_domain_context M b c n domain d e.
Proof.
  destruct (domain_context_total M b c n domain) as [d [e H]].
  exists d,e. intros i f Hi Hf. apply (H i f); [|exact Hf].
  apply (proj2 (coding_lt_succ_cases M i n)). now left.
Qed.

Theorem live_domain_context_member_exact M b c n domain d e f :
  live_domain_context M b c n domain d e ->
  (context_member M d e n f <-> exists i x,
    coding_lt M i n /\ environment_lookup M b c n i x /\ membership_graph M domain x f).
Proof.
  intro H. split.
  - intros [i [Hi Hf]]. destruct (H i f Hi Hf) as [x [Hx Ha]].
    exists i,x. auto.
  - intros [i [x [Hi [Hx Ha]]]]. destruct (beta_total M d e i) as [g Hg].
    assert (g=f).
    { apply (domain_context_entry_functional M b c n domain i g f).
      - exact (H i g Hi Hg).
      - exists x. auto. }
    subst g. exists i. auto.
Qed.

Theorem live_domain_context_assumption M b c n domain d e i x f :
  live_domain_context M b c n domain d e -> coding_lt M i n ->
  environment_lookup M b c n i x -> membership_graph M domain x f ->
  contextually_provable M d e n f.
Proof.
  intros H Hi Hx Hf. apply contextual_hyp.
  apply (proj2 (live_domain_context_member_exact M b c n domain d e f H)).
  exists i,x. auto.
Qed.

Theorem live_domain_context_cons M b c n domain d e x domx b' c' n' d' e' len :
  live_domain_context M b c n domain d e ->
  environment_cons M b c n x b' c' n' -> membership_graph M domain x domx ->
  environment_cons M d e n domx d' e' len ->
  live_domain_context M b' c' n' domain d' e'.
Proof.
  intros H HE Hdom HD i f Hi Hf.
  assert (Elen : len=n') by (rewrite (proj1 HE); exact (proj1 HD)).
  assert (Hlookup : environment_lookup M d' e' len i f).
  { apply (proj2 (environment_lookup_inside M d' e' len i f ltac:(now rewrite Elen))).
    exact Hf. }
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [->|[j ->]].
  - pose proof (proj1 (environment_cons_head M d e n domx d' e' len f HD) Hlookup) as E.
    subst f. exists x. split; [exact (proj1 (proj2 HE))|exact Hdom].
  - pose proof (proj1 (environment_cons_tail M d e n domx d' e' len j f HD) Hlookup) as Htail.
    assert (Hj : coding_lt M j n).
    { rewrite (proj1 HE) in Hi. exact (proj1 (coding_lt_succ_cancel M j n) Hi). }
    apply (proj1 (environment_lookup_inside M d e n j f Hj)) in Htail.
    destruct (H j f Hj Htail) as [u [Hu Ha]]. exists u. split.
    + exact (proj2 (proj2 HE) j u Hu).
    + exact Ha.
Qed.

Theorem live_domain_context_fresh M b c n domain d e y :
  live_domain_context M b c n domain d e -> domain<>y ->
  (forall i x, coding_lt M i n -> environment_lookup M b c n i x -> x<>y) ->
  context_fresh M d e n y.
Proof.
  intros H HD HE f Hf.
  destruct (proj1 (live_domain_context_member_exact M b c n domain d e f H) Hf)
    as [i [x [Hi [Hx Ha]]]].
  exact (formula_fresh_membership_intro M domain x f y Ha HD (HE i x Hi Hx)).
Qed.

Theorem live_domain_context_safe_fresh M b c n domain d e k :
  live_domain_context M b c n domain d e -> quotation_safe M b c n k domain ->
  context_fresh M d e n k.
Proof.
  intros H [HD HE]. apply (live_domain_context_fresh M b c n domain d e k H).
  - exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) domain k HD).
  - intros i x Hi Hx. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x k (HE i x Hx)).
Qed.

Theorem live_domain_context_empty M b c domain d e f :
  live_domain_context M b c (zeroM M) domain d e -> ~context_member M d e (zeroM M) f.
Proof. intros _. apply context_empty. Qed.

Theorem live_domain_context_formula_bound : bounded 6
  (live_domain_context_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions live_domain_context_formula_correct.
Print Assumptions live_domain_context_total.
Print Assumptions live_domain_context_member_exact.
Print Assumptions live_domain_context_assumption.
Print Assumptions live_domain_context_cons.
Print Assumptions live_domain_context_safe_fresh.
Print Assumptions live_domain_context_empty.
Print Assumptions live_domain_context_formula_bound.
