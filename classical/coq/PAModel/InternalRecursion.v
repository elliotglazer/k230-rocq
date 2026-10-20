(** Arithmetic recursion by an internally finite table. The next value is
    specified by an ordinary PA formula whose free slots are value, index,
    beta modulus, beta dividend, and parameters. Prefix invariance prevents
    the step from inspecting future entries. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension CodeExpressions NumericalProofs ProofClosure CourseOfValues.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition recursion_step M theta rho b c n v :=
  holds M (v .: n .: c .: b .: rho) theta.

Definition recursion_prefix M theta rho b c n :=
  forall i v, coding_lt M i n -> beta M b c i v ->
    recursion_step M theta rho b c i v.

Definition recursion_step_skip_bound theta :=
  theta[($0 .: $1 .: $2 .: $3 .: fun i => var (5+i))].

Definition recursion_exists_formula theta :=
  ∃∃∀∀ (Peano.sless $1 $4 → beta_formula $3 $2 $1 $0 →
    recursion_step_skip_bound theta).

Lemma recursion_step_skip_bound_correct M theta rho b c n i v :
  holds M (v .: i .: c .: b .: n .: rho) (recursion_step_skip_bound theta) <->
  recursion_step M theta rho b c i v.
Proof.
  unfold recursion_step_skip_bound,recursion_step,holds.
  rewrite sat_comp. apply sat_ext. intros [|[|[|[|j]]]]; reflexivity.
Qed.

Local Opaque holds recursion_step_skip_bound beta_formula Peano.sless.

Lemma recursion_exists_formula_correct M theta rho n :
  holds M (n .: rho) (recursion_exists_formula theta) <->
  exists b c, recursion_prefix M theta rho b c n.
Proof.
  unfold recursion_exists_formula,recursion_prefix.
  repeat setoid_rewrite holds_exists. repeat setoid_rewrite holds_forall.
  repeat setoid_rewrite holds_imp. setoid_rewrite holds_sless.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite recursion_step_skip_bound_correct. reflexivity.
Qed.

Lemma recursion_exists_definable M theta rho :
  Definable1 M (fun n => exists b c, recursion_prefix M theta rho b c n).
Proof.
  exists (recursion_exists_formula theta),rho.
  intro n. symmetry. apply recursion_exists_formula_correct.
Qed.

Definition sequence_agreement_formula : form :=
  Peano.sless $0 $5 → ∀∀ (beta_formula $3 $4 $2 $1 →
    beta_formula $5 $6 $2 $0 → $1 == $0).

Lemma sequence_agreement_definable M b c d e n :
  Definable1 M (fun i => coding_lt M i n -> forall v w,
    beta M b c i v -> beta M d e i w -> v=w).
Proof.
  exists sequence_agreement_formula,
    (b .: c .: d .: e .: n .: fun _ => zeroM M).
  intro i. unfold sequence_agreement_formula.
  rewrite holds_imp,holds_sless. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite beta_formula_correct.
  reflexivity.
Qed.

Section Recursion.
Variable M : Model.
Variable theta : form.
Variable rho : nat -> carrier M.
Hypothesis step_total : forall b c n, exists v, recursion_step M theta rho b c n v.
Hypothesis step_prefix : forall b c b' c' n,
  prefix M b c b' c' n -> forall v,
  (recursion_step M theta rho b c n v <-> recursion_step M theta rho b' c' n v).

Theorem recursion_table_total n : exists b c, recursion_prefix M theta rho b c n.
Proof.
  apply (definable_induction M
    (fun n => exists b c, recursion_prefix M theta rho b c n)
    (recursion_exists_definable M theta rho)).
  - exists (zeroM M),(zeroM M). intros i v Hi.
    exfalso. exact (coding_not_lt_zero M i Hi).
  - intros k [b [c Hseq]].
    destruct (step_total b c k) as [v Hv].
    destruct (beta_extension M b c k v) as [b' [c' [Hp Hnew]]].
    exists b',c'. intros i u Hi Hu.
    destruct (proj1 (coding_lt_succ_cases M i k) Hi) as [Hik|Heq].
    + assert (Hpi : prefix M b c b' c' i).
      { intros j t Hj Ht. apply Hp; [exact (coding_lt_trans M j i k Hj Hik)|exact Ht]. }
      apply (proj1 (step_prefix b c b' c' i Hpi u)).
      apply (Hseq i u Hik). exact (prefix_back M b c b' c' k Hp i u Hik Hu).
    + subst i. assert (u=v) by (eapply beta_unique; eassumption).
      subst u. exact (proj1 (step_prefix b c b' c' k Hp v) Hv).
Qed.

Definition recursion_graph n v := exists b c,
  recursion_prefix M theta rho b c (succM M n) /\ beta M b c n v.

Theorem recursion_graph_total n : exists v, recursion_graph n v.
Proof.
  destruct (recursion_table_total (succM M n)) as [b [c Hseq]].
  destruct (beta_total M b c n) as [v Hv]. exists v,b,c. auto.
Qed.

End Recursion.

Section Uniqueness.
Variable M : Model.
Variable theta : form.
Variable rho : nat -> carrier M.
Hypothesis step_functional : forall b c n v w,
  recursion_step M theta rho b c n v -> recursion_step M theta rho b c n w -> v=w.
Hypothesis step_prefix : forall b c b' c' n,
  prefix M b c b' c' n -> forall v,
  (recursion_step M theta rho b c n v <-> recursion_step M theta rho b' c' n v).

Theorem recursion_prefix_unique b c d e n :
  recursion_prefix M theta rho b c n -> recursion_prefix M theta rho d e n ->
  forall i v w, coding_lt M i n -> beta M b c i v -> beta M d e i w -> v=w.
Proof.
  intros Hbc Hde.
  assert (H : forall i, coding_lt M i n -> forall v w,
    beta M b c i v -> beta M d e i w -> v=w).
  { apply (definable_strong_induction M _ (sequence_agreement_definable M b c d e n)).
    intros i IH Hin v w Hv Hw.
    assert (Hpi : prefix M b c d e i).
    { intros j u Hj Hju. destruct (beta_total M d e j) as [t Ht].
      assert (u=t) by exact
        (IH j Hj (coding_lt_trans M j i n Hj Hin) u t Hju Ht).
      now subst t. }
    apply (step_functional b c i v w).
    - exact (Hbc i v Hin Hv).
    - apply (proj2 (step_prefix b c d e i Hpi w)). exact (Hde i w Hin Hw). }
  intros i v w Hi. exact (H i Hi v w).
Qed.

Theorem recursion_graph_functional n v w :
  recursion_graph M theta rho n v -> recursion_graph M theta rho n w -> v=w.
Proof.
  intros [b [c [Hbc Hv]]] [d [e [Hde Hw]]].
  exact (recursion_prefix_unique b c d e (succM M n) Hbc Hde n v w
    (coding_lt_succ M n) Hv Hw).
Qed.

End Uniqueness.

Definition recursion_prefix_formula theta (b c n : term) : form :=
  ∀∀ (Peano.sless $1 (code_lift2 n) →
    beta_formula (code_lift2 b) (code_lift2 c) $1 $0 →
    theta[($0 .: $1 .: code_lift2 c .: code_lift2 b .: fun j => var (2+j))]).

Local Transparent holds.
Lemma recursion_prefix_predicate_correct M theta rho b c i v :
  holds M (v .: i .: rho)
    theta[($0 .: $1 .: code_lift2 c .: code_lift2 b .: fun j => var (2+j))] <->
  recursion_step M theta rho (evalM M rho b) (evalM M rho c) i v.
Proof.
  unfold holds,recursion_step. rewrite sat_comp. apply sat_ext.
  intros [|[|[|[|j]]]]; try reflexivity; apply code_eval_lift2.
Qed.
Local Opaque holds.

Lemma recursion_prefix_formula_correct M theta rho b c n :
  holds M rho (recursion_prefix_formula theta b c n) <->
  recursion_prefix M theta rho (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold recursion_prefix_formula,recursion_prefix.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite code_eval_lift2.
  setoid_rewrite recursion_prefix_predicate_correct. reflexivity.
Qed.

Definition recursion_parameter_lift2 theta :=
  theta[($0 .: $1 .: $2 .: $3 .: fun j => var (6+j))].

Local Transparent holds.
Lemma recursion_parameter_lift2_correct M theta rho b c n v x y :
  recursion_step M (recursion_parameter_lift2 theta) (y .: x .: rho) b c n v <->
  recursion_step M theta rho b c n v.
Proof.
  unfold recursion_step,recursion_parameter_lift2,holds.
  rewrite sat_comp. apply sat_ext. intros [|[|[|[|j]]]]; reflexivity.
Qed.
Local Opaque holds.

Lemma recursion_prefix_parameter_lift2 M theta rho b c n x y :
  recursion_prefix M (recursion_parameter_lift2 theta) (y .: x .: rho) b c n <->
  recursion_prefix M theta rho b c n.
Proof.
  unfold recursion_prefix. setoid_rewrite recursion_parameter_lift2_correct. reflexivity.
Qed.

Definition recursion_graph_formula theta (n v : term) : form :=
  ∃∃ (recursion_prefix_formula (recursion_parameter_lift2 theta)
    $1 $0 (σ (code_lift2 n)) ∧
    beta_formula $1 $0 (code_lift2 n) (code_lift2 v)).

Local Opaque recursion_prefix_formula.

Local Lemma recursion_eval_succ M rho t :
  evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.

Theorem recursion_graph_formula_correct M theta rho n v :
  holds M rho (recursion_graph_formula theta n v) <->
  recursion_graph M theta rho (evalM M rho n) (evalM M rho v).
Proof.
  unfold recursion_graph_formula,recursion_graph.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite recursion_prefix_formula_correct.
  setoid_rewrite recursion_prefix_parameter_lift2.
  setoid_rewrite beta_formula_correct.
  setoid_rewrite recursion_eval_succ.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Print Assumptions recursion_table_total.
Print Assumptions recursion_graph_total.
Print Assumptions recursion_graph_functional.
Print Assumptions recursion_graph_formula_correct.
