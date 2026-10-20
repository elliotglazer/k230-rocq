(** Actual internal run states, their ordinary PA formulas, and the
    definable invariant needed for induction over arbitrary model lengths. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs StackSafety SearchStep KernelSafety.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition state_index M (i : carrier M) (j : nat) :=
  addM M (mulM M (code_numeral M 6) i) (code_numeral M j).
Definition state_index_term (i : term) (j : nat) : term := (num 6 ⊗ i) ⊕ num j.

Definition state_at M b c i (s : search_state (carrier M)) : Prop :=
  beta M b c (state_index M i 0) (search_pl s) /\
  beta M b c (state_index M i 1) (search_np s) /\
  beta M b c (state_index M i 2) (search_tw s) /\
  beta M b c (state_index M i 3) (search_ws s) /\
  beta M b c (state_index M i 4) (search_d s) /\
  beta M b c (state_index M i 5) (search_h s).

Lemma state_at_total M b c i : exists s, state_at M b c i s.
Proof.
  destruct (beta_total M b c (state_index M i 0)) as [pl Hpl].
  destruct (beta_total M b c (state_index M i 1)) as [np Hnp].
  destruct (beta_total M b c (state_index M i 2)) as [tw Htw].
  destruct (beta_total M b c (state_index M i 3)) as [ws Hws].
  destruct (beta_total M b c (state_index M i 4)) as [d Hd].
  destruct (beta_total M b c (state_index M i 5)) as [h Hh].
  exists (mkSearchState (carrier M) pl np tw ws d h).
  exact (conj Hpl (conj Hnp (conj Htw (conj Hws (conj Hd Hh))))).
Qed.

Lemma state_at_functional M b c i s t :
  state_at M b c i s -> state_at M b c i t -> s=t.
Proof.
  destruct s,t. unfold state_at; cbn.
  intros (H0&H1&H2&H3&H4&H5) (K0&K1&K2&K3&K4&K5).
  f_equal; eapply beta_unique; eassumption.
Qed.

Definition state_at_formula (b c i pl np tw ws d h : term) : form :=
  beta_formula b c (state_index_term i 0) pl ∧
  (beta_formula b c (state_index_term i 1) np ∧
  (beta_formula b c (state_index_term i 2) tw ∧
  (beta_formula b c (state_index_term i 3) ws ∧
  (beta_formula b c (state_index_term i 4) d ∧
   beta_formula b c (state_index_term i 5) h)))).

Lemma state_index_term_correct M rho i j :
  evalM M rho (state_index_term i j) = state_index M (evalM M rho i) j.
Proof.
  change (addM M (mulM M (evalM M rho (num 6)) (evalM M rho i))
    (evalM M rho (num j)) = state_index M (evalM M rho i) j).
  rewrite !code_eval_num. reflexivity.
Qed.

Theorem state_at_formula_correct M rho b c i pl np tw ws d h :
  holds M rho (state_at_formula b c i pl np tw ws d h) <->
  state_at M (evalM M rho b) (evalM M rho c) (evalM M rho i)
    (mkSearchState (carrier M) (evalM M rho pl) (evalM M rho np)
      (evalM M rho tw) (evalM M rho ws) (evalM M rho d) (evalM M rho h)).
Proof.
  unfold state_at_formula,state_at. rewrite !holds_and, !beta_formula_correct.
  rewrite !state_index_term_correct. reflexivity.
Qed.

Fixpoint run_lift (n : nat) (t : term) : term :=
  match n with 0 => t | S k => (run_lift k t)`[↑] end.

Lemma eval_run_lift6 M rho a b c d e f t :
  evalM M (f .: e .: d .: c .: b .: a .: rho) (run_lift 6 t) = evalM M rho t.
Proof. unfold evalM; cbn [run_lift]. now rewrite !eval_up. Qed.

Lemma eval_run_lift13 M rho a b c d e f g h i j k l m t :
  evalM M (m .: l .: k .: j .: i .: h .: g .: f .: e .: d .: c .: b .: a .: rho)
    (run_lift 13 t) = evalM M rho t.
Proof. unfold evalM; cbn [run_lift]. now rewrite !eval_up. Qed.

Definition invariant_formula (tw ws h : term) : form :=
  numerically_provable_formula tw ∧
    (numerically_provable_formula h ∧ good_stack_formula ws).

Lemma invariant_formula_correct M rho tw ws h :
  holds M rho (invariant_formula tw ws h) <->
  (numerically_provable M (evalM M rho tw) /\
  numerically_provable M (evalM M rho h) /\ good_stack M (evalM M rho ws)).
Proof.
  unfold invariant_formula. rewrite !holds_and,
    !numerically_provable_formula_correct, good_stack_formula_correct.
  reflexivity.
Qed.

Definition safe_at M b c k : Prop :=
  forall s, state_at M b c k s -> invariant M s.

Definition safe_at_formula (b c k : term) : form :=
  ∀∀∀∀∀∀
    (state_at_formula (run_lift 6 b) (run_lift 6 c) (run_lift 6 k)
      $5 $4 $3 $2 $1 $0 → invariant_formula $3 $2 $0).

Local Opaque holds state_at_formula invariant_formula.

Theorem safe_at_formula_correct M rho b c k :
  holds M rho (safe_at_formula b c k) <->
  safe_at M (evalM M rho b) (evalM M rho c) (evalM M rho k).
Proof.
  unfold safe_at_formula. repeat setoid_rewrite holds_all.
  setoid_rewrite holds_imp. setoid_rewrite state_at_formula_correct.
  setoid_rewrite invariant_formula_correct. setoid_rewrite eval_run_lift6.
  split.
  - intros H [pl np tw ws d h] Hs. exact (H pl np tw ws d h Hs).
  - intros H pl np tw ws d h Hs. exact (H (mkSearchState (carrier M) pl np tw ws d h) Hs).
Qed.

Theorem safe_at_definable M b c N :
  Definable1 M (fun k => coding_lt M k (succM M N) -> safe_at M b c k).
Proof.
  exists (Peano.sless $0 (σ $3) → safe_at_formula $1 $2 $0),
    (b .: c .: N .: (fun _ => zeroM M)).
  intro k. rewrite holds_imp, less_formula_correct, safe_at_formula_correct. reflexivity.
Qed.

Definition numerical_run_from M b c N (s0 : search_state (carrier M)) : Prop :=
  state_at M b c (zeroM M) s0 /\
  forall i s t, coding_lt M i N -> state_at M b c i s ->
    state_at M b c (succM M i) t -> enumerator_step M s t.

Definition numerical_run M b c N := numerical_run_from M b c N (seed_state M).


Definition term_state_value M rho (s : search_state term) : search_state (carrier M) :=
  mkSearchState (carrier M) (evalM M rho (search_pl s)) (evalM M rho (search_np s))
    (evalM M rho (search_tw s)) (evalM M rho (search_ws s))
    (evalM M rho (search_d s)) (evalM M rho (search_h s)).

Definition term_state_env (s t : search_state term) (i : nat) : term :=
  match i with
  | 0 => search_pl s | 1 => search_np s | 2 => search_tw s
  | 3 => search_ws s | 4 => search_d s | 5 => search_h s
  | 6 => search_pl t | 7 => search_np t | 8 => search_tw t
  | 9 => search_ws t | 10 => search_d t | 11 => search_h t
  | _ => zero
  end.

Definition state_step_formula (s t : search_state term) : form :=
  search_formula search_step_pred (term_state_env s t).

Lemma state_step_formula_correct M rho s t :
  holds M rho (state_step_formula s t) <->
  enumerator_step M (term_state_value M rho s) (term_state_value M rho t).
Proof.
  unfold state_step_formula. rewrite search_formula_correct.
  etransitivity; [|apply search_step_relation_correct].
  apply search_relation_ext. intro i.
  do 12 (destruct i as [|i]; [reflexivity|]). reflexivity.
Qed.

Definition state_halt_formula (s : search_state term) : form :=
  search_formula search_halt_pred
    (term_state_env s (mkSearchState term zero zero zero zero zero zero)).

Lemma state_halt_formula_correct M rho s :
  holds M rho (state_halt_formula s) <-> enumerator_halt M (term_state_value M rho s).
Proof.
  unfold state_halt_formula. rewrite search_formula_correct.
  etransitivity; [|apply (search_halt_relation_correct M (term_state_value M rho s)
    (mkSearchState (carrier M) (zeroM M) (zeroM M) (zeroM M) (zeroM M) (zeroM M) (zeroM M)))].
  apply search_relation_ext. intro i.
  do 12 (destruct i as [|i]; [reflexivity|]). reflexivity.
Qed.

Local Opaque state_step_formula state_halt_formula.

Definition run_transition_formula (b c N : term) : form :=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀
   (Peano.sless $12 (run_lift 13 N) →
    (state_at_formula (run_lift 13 b) (run_lift 13 c) $12 $11 $10 $9 $8 $7 $6 →
     (state_at_formula (run_lift 13 b) (run_lift 13 c) (σ $12) $5 $4 $3 $2 $1 $0 →
      state_step_formula (mkSearchState term $11 $10 $9 $8 $7 $6)
        (mkSearchState term $5 $4 $3 $2 $1 $0)))).

Lemma run_transition_formula_correct M rho b c N :
  holds M rho (run_transition_formula b c N) <->
  (forall i s t, coding_lt M i (evalM M rho N) ->
    state_at M (evalM M rho b) (evalM M rho c) i s ->
    state_at M (evalM M rho b) (evalM M rho c) (succM M i) t -> enumerator_step M s t).
Proof.
  unfold run_transition_formula. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct.
  setoid_rewrite state_at_formula_correct.
  setoid_rewrite state_step_formula_correct.
  setoid_rewrite eval_run_lift13.
  split.
  - intros H i [pl np tw ws d h] [pl' np' tw' ws' d' h'] Hi Hs Ht.
    exact (H i pl np tw ws d h pl' np' tw' ws' d' h' Hi Hs Ht).
  - intros H i pl np tw ws d h pl' np' tw' ws' d' h' Hi Hs Ht.
    exact (H i (mkSearchState (carrier M) pl np tw ws d h)
      (mkSearchState (carrier M) pl' np' tw' ws' d' h') Hi Hs Ht).
Qed.

Definition run_formula (b c N : term) : form :=
  state_at_formula b c zero zero (num 3) zero zero (num 3) zero ∧
    run_transition_formula b c N.

Theorem run_formula_correct M rho b c N :
  holds M rho (run_formula b c N) <->
  numerical_run M (evalM M rho b) (evalM M rho c) (evalM M rho N).
Proof.
  unfold run_formula,numerical_run,numerical_run_from.
  rewrite holds_and,state_at_formula_correct,run_transition_formula_correct.
  rewrite !code_eval_num. reflexivity.
Qed.

Definition halt_at M b c N : Prop :=
  exists s, state_at M b c N s /\ enumerator_halt M s.

Definition halt_at_formula (b c N : term) : form :=
  ∃∃∃∃∃∃
    (state_at_formula (run_lift 6 b) (run_lift 6 c) (run_lift 6 N)
      $5 $4 $3 $2 $1 $0 ∧ state_halt_formula (mkSearchState term $5 $4 $3 $2 $1 $0)).

Theorem halt_at_formula_correct M rho b c N :
  holds M rho (halt_at_formula b c N) <->
  halt_at M (evalM M rho b) (evalM M rho c) (evalM M rho N).
Proof.
  unfold halt_at_formula. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite state_at_formula_correct.
  setoid_rewrite state_halt_formula_correct. setoid_rewrite eval_run_lift6.
  split.
  - intros [pl [np [tw [ws [d [h H]]]]]].
    exists (mkSearchState (carrier M) pl np tw ws d h). exact H.
  - intros [[pl np tw ws d h] H]. exists pl,np,tw,ws,d,h. exact H.
Qed.

Print Assumptions state_at_total.
Print Assumptions state_at_functional.
Print Assumptions safe_at_definable.
Print Assumptions run_formula_correct.
Print Assumptions halt_at_formula_correct.
