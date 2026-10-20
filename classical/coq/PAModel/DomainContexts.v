(** Finite domain assumptions for a relativized source interpretation.
    Each live environment entry gets its membership assumption, and one
    additional entry covers the default value zero outside the environment.
    Nothing here asserts that these domain assumptions are K theorems.
    In particular the default entry cannot be discharged when the domain
    name is itself zero. The final interpretation must instead use a
    live-entry context and a bound on the proof's variable indices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalEnvironments
  NumericalContexts InternalRecursion ProofClosure ContextualProofs SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition domain_context_entry M b c n domain i f := exists x,
  environment_lookup M b c n i x /\ membership_graph M domain x f.
Definition domain_context_entry_formula (b c n domain i f : term) : form :=
  ∃ (environment_lookup_formula b`[↑] c`[↑] n`[↑] i`[↑] $0 ∧
    tagged_pair_formula 1 domain`[↑] $0 f`[↑]).

Local Opaque holds environment_lookup_formula tagged_pair_formula.
Lemma domain_context_entry_formula_correct M rho b c n domain i f :
  holds M rho (domain_context_entry_formula b c n domain i f) <->
  domain_context_entry M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho domain) (evalM M rho i) (evalM M rho f).
Proof.
  unfold domain_context_entry_formula,domain_context_entry,membership_graph.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite tagged_pair_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma domain_context_entry_total M b c n domain i :
  exists f, domain_context_entry M b c n domain i f.
Proof.
  destruct (environment_lookup_total M b c n i) as [x Hx].
  destruct (tagged_pair_total M 1 domain x) as [f Hf].
  exists f,x. auto.
Qed.

Lemma domain_context_entry_functional M b c n domain i f g :
  domain_context_entry M b c n domain i f ->
  domain_context_entry M b c n domain i g -> f=g.
Proof.
  intros [x [Hx Hf]] [y [Hy Hg]].
  assert (x=y) by (exact (environment_lookup_functional M b c n i x y Hx Hy)).
  subst y. exact (tagged_pair_functional M 1 domain x f g Hf Hg).
Qed.

Definition domain_context M b c n domain d e :=
  forall i f, coding_lt M i (succM M n) -> beta M d e i f ->
    domain_context_entry M b c n domain i f.
Definition domain_context_formula (b c n domain d e : term) : form :=
  ∀∀ (Peano.sless $1 (σ (code_lift2 n)) →
    beta_formula (code_lift2 d) (code_lift2 e) $1 $0 →
    domain_context_entry_formula (code_lift2 b) (code_lift2 c) (code_lift2 n)
      (code_lift2 domain) $1 $0).

Local Opaque domain_context_entry_formula beta_formula Peano.sless.
Local Lemma domain_eval_succ M rho t :
  evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.
Lemma domain_context_formula_correct M rho b c n domain d e :
  holds M rho (domain_context_formula b c n domain d e) <->
  domain_context M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho domain) (evalM M rho d) (evalM M rho e).
Proof.
  unfold domain_context_formula,domain_context.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite domain_context_entry_formula_correct.
  setoid_rewrite domain_eval_succ.
  repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.

(** In a recursion step the slots before parameters are value,index,c,b. *)
Definition domain_context_step_formula : form :=
  domain_context_entry_formula $4 $5 $6 $7 $1 $0.
Lemma domain_context_step_correct M b c n domain d e i f :
  recursion_step M domain_context_step_formula
    (b .: c .: n .: domain .: fun _ => zeroM M) d e i f <->
  domain_context_entry M b c n domain i f.
Proof.
  unfold recursion_step,domain_context_step_formula.
  rewrite domain_context_entry_formula_correct. reflexivity.
Qed.

Theorem domain_context_total M b c n domain :
  exists d e, domain_context M b c n domain d e.
Proof.
  assert (HT : forall d e i, exists f, recursion_step M domain_context_step_formula
    (b .: c .: n .: domain .: fun _ => zeroM M) d e i f).
  { intros d e i. destruct (domain_context_entry_total M b c n domain i) as [f Hf].
    exists f. now apply domain_context_step_correct. }
  assert (HP : forall d e d' e' i, prefix M d e d' e' i -> forall f,
    (recursion_step M domain_context_step_formula
      (b .: c .: n .: domain .: fun _ => zeroM M) d e i f <->
     recursion_step M domain_context_step_formula
      (b .: c .: n .: domain .: fun _ => zeroM M) d' e' i f)).
  { intros. rewrite !domain_context_step_correct. reflexivity. }
  destruct (recursion_table_total M domain_context_step_formula
    (b .: c .: n .: domain .: fun _ => zeroM M) HT HP (succM M n)) as [d [e H]].
  exists d,e. intros i f Hi Hf.
  exact (proj1 (domain_context_step_correct M b c n domain d e i f) (H i f Hi Hf)).
Qed.

Theorem domain_context_at M b c n domain d e i x f :
  domain_context M b c n domain d e -> coding_lt M i (succM M n) ->
  environment_lookup M b c n i x -> membership_graph M domain x f ->
  context_member M d e (succM M n) f.
Proof.
  intros HC Hi Hx Hf. destruct (beta_total M d e i) as [g Hg].
  assert (f=g).
  { apply (domain_context_entry_functional M b c n domain i f g).
    - exists x. auto.
    - exact (HC i g Hi Hg). }
  subst g. exists i. auto.
Qed.

Lemma domain_default_lookup M b c n :
  environment_lookup M b c n n (zeroM M).
Proof.
  assert (Hn : ~coding_lt M n n).
  { intro H. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) n n H eq_refl). }
  exact (proj2 (environment_lookup_outside M b c n n (zeroM M) Hn) eq_refl).
Qed.

Theorem domain_context_covers_lookup M b c n domain d e i x f :
  domain_context M b c n domain d e ->
  environment_lookup M b c n i x -> membership_graph M domain x f ->
  context_member M d e (succM M n) f.
Proof.
  intros HC Hx Hf. destruct (environment_lt_cases M i n) as [Hi|Hi].
  - apply (domain_context_at M b c n domain d e i x f HC).
    + apply (proj2 (coding_lt_succ_cases M i n)). now left.
    + exact Hx.
    + exact Hf.
  - apply (proj1 (environment_lookup_outside M b c n i x Hi)) in Hx.
    subst x. apply (domain_context_at M b c n domain d e n (zeroM M) f HC
      (coding_lt_succ M n) (domain_default_lookup M b c n) Hf).
Qed.

Theorem domain_context_member_exact M b c n domain d e f :
  domain_context M b c n domain d e ->
  (context_member M d e (succM M n) f <->
    exists i x, environment_lookup M b c n i x /\ membership_graph M domain x f).
Proof.
  intro HC. split.
  - intros [i [Hi Hf]]. destruct (HC i f Hi Hf) as [x Hx]. exists i,x. exact Hx.
  - intros [i [x [Hx Hf]]]. exact (domain_context_covers_lookup M b c n domain d e i x f HC Hx Hf).
Qed.

Theorem domain_context_assumption M b c n domain d e i x f :
  domain_context M b c n domain d e ->
  environment_lookup M b c n i x -> membership_graph M domain x f ->
  contextually_provable M d e (succM M n) f.
Proof.
  intros HC Hx Hf. apply contextual_hyp.
  exact (domain_context_covers_lookup M b c n domain d e i x f HC Hx Hf).
Qed.

Theorem domain_context_formula_bound : bounded 6
  (domain_context_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions domain_context_formula_correct.
Print Assumptions domain_context_total.
Print Assumptions domain_context_member_exact.
Print Assumptions domain_context_assumption.
Print Assumptions domain_context_formula_bound.
