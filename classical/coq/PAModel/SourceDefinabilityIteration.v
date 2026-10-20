(** Exact arbitrary internal iterations for canonical EnvF and NumF syntax.
    The boolean distinguishes environment-extension from numeral-successor. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension CodeExpressions NumericalProofs ProofClosure InternalRecursion
  SentenceBounds StandardModel SetFormulaCodes SourceDefinabilityStep SourceDefinabilityPrimitives.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Definition def_recursion_step M environment body b c n v : Prop :=
  (n = zeroM M /\ v = body) \/
  exists k p, n = succM M k /\ beta M b c k p /\
    source_def_step M environment p v.

(** The step environment is value,index,modulus,dividend,body,parameters. *)
Definition def_recursion_step_formula (environment:bool) : pa_form :=
  (($1 == zero) ∧ ($0 == $4)) ∨
  ∃∃ ($3 == σ $1 ∧ beta_formula $5 $4 $1 $0 ∧
    source_def_step_formula environment $0 $2).

Local Opaque beta_formula source_def_step_formula.

Lemma def_recursion_step_formula_correct M environment rho b c n v :
  recursion_step M (def_recursion_step_formula environment) rho b c n v <->
  def_recursion_step M environment (rho 0) b c n v.
Proof.
  unfold recursion_step,def_recursion_step_formula,def_recursion_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite source_def_step_formula_correct.
  change (((n = zeroM M /\ v = rho 0) \/
    (exists k p, (n = succM M k /\ beta M b c k p) /\
      source_def_step M environment p v)) <->
    ((n = zeroM M /\ v = rho 0) \/
    exists k p, n = succM M k /\ beta M b c k p /\
      source_def_step M environment p v)).
  split.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
Qed.

Lemma def_recursion_step_total M environment body b c n : exists v, def_recursion_step M environment body b c n v.
Proof.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) n) as [H0|[k Hk]].
  - exists body. left. auto.
  - destruct (beta_total M b c k) as [p Hp].
    destruct (source_def_step_total M environment p) as [v Hv].
    exists v. right. exists k,p. auto.
Qed.

Lemma def_recursion_step_functional M environment body b c n v w :
  def_recursion_step M environment body b c n v -> def_recursion_step M environment body b c n w -> v=w.
Proof.
  intros [[H0 ->]|[k [p [Hk [Hp Hv]]]]]
    [[H0' ->]|[j [q [Hj [Hq Hw]]]]].
  - reflexivity.
  - exfalso. apply (zero_ne_succ M j). congruence.
  - exfalso. apply (zero_ne_succ M k). congruence.
  - assert (k=j) by (apply (succ_injective M); congruence). subst j.
    assert (p=q) by (eapply beta_unique; eassumption). subst q.
    eapply source_def_step_functional; eassumption.
Qed.

Lemma def_recursion_step_prefix M environment body b c b' c' n :
  prefix M b c b' c' n -> forall v,
  (def_recursion_step M environment body b c n v <-> def_recursion_step M environment body b' c' n v).
Proof.
  intro Hpre. intro v. split; intros [Hz|[k [p [-> [Hp Hv]]]]].
  - now left.
  - right. exists k,p. split; [reflexivity|]. split; [|exact Hv].
    exact (Hpre k p (coding_lt_succ M k) Hp).
  - now left.
  - right. exists k,p. split; [reflexivity|]. split; [|exact Hv].
    exact (prefix_back M b c b' c' (succM M k) Hpre k p
      (coding_lt_succ M k) Hp).
Qed.

Definition source_def_iteration M environment n body result : Prop :=
  exists b c,
    (forall i v, coding_lt M i (succM M n) -> beta M b c i v ->
      def_recursion_step M environment body b c i v) /\ beta M b c n result.

Lemma source_def_recursion_graph M environment rho n result :
  recursion_graph M (def_recursion_step_formula environment) rho n result <->
  source_def_iteration M environment n (rho 0) result.
Proof.
  unfold recursion_graph,recursion_prefix,source_def_iteration.
  setoid_rewrite def_recursion_step_formula_correct. reflexivity.
Qed.

Theorem source_def_iteration_total M environment n body : exists result, source_def_iteration M environment n body result.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Htotal : forall b c i, exists v,
    recursion_step M (def_recursion_step_formula environment) rho b c i v).
  { intros b c i. setoid_rewrite def_recursion_step_formula_correct. apply def_recursion_step_total. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M (def_recursion_step_formula environment) rho b c i v <->
     recursion_step M (def_recursion_step_formula environment) rho b' c' i v)).
  { intros b c b' c' i Hp v. rewrite !def_recursion_step_formula_correct.
    now apply def_recursion_step_prefix. }
  destruct (recursion_graph_total M (def_recursion_step_formula environment) rho Htotal Hprefix n) as [v Hv].
  exists v. apply source_def_recursion_graph in Hv. exact Hv.
Qed.

Theorem source_def_iteration_functional M environment n body v w :
  source_def_iteration M environment n body v -> source_def_iteration M environment n body w -> v=w.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Hfun : forall b c i v w,
    recursion_step M (def_recursion_step_formula environment) rho b c i v ->
    recursion_step M (def_recursion_step_formula environment) rho b c i w -> v=w).
  { intros b c i v' w'. rewrite !def_recursion_step_formula_correct.
    apply def_recursion_step_functional. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M (def_recursion_step_formula environment) rho b c i v <->
     recursion_step M (def_recursion_step_formula environment) rho b' c' i v)).
  { intros b c b' c' i Hp v'. rewrite !def_recursion_step_formula_correct.
    now apply def_recursion_step_prefix. }
  change (source_def_iteration M environment n (rho 0) v -> source_def_iteration M environment n (rho 0) w -> v=w).
  rewrite <- !source_def_recursion_graph.
  exact (recursion_graph_functional M (def_recursion_step_formula environment) rho Hfun Hprefix n v w).
Qed.

Definition source_def_iteration_formula (environment:bool) (n body result : pa_term) : pa_form :=
  ∃ ($0 == body`[↑] ∧ recursion_graph_formula (def_recursion_step_formula environment)
    n`[↑] result`[↑]).

Lemma def_iteration_eval_shift M rho x t :
  evalM M (x .: rho) t`[↑] = evalM M rho t.
Proof. unfold evalM. apply eval_up. Qed.

Lemma def_iteration_equality_correct M rho (t u : pa_term) :
  holds M rho (t == u) <-> evalM M rho t = evalM M rho u.
Proof. reflexivity. Qed.

Theorem source_def_iteration_formula_correct M environment rho n body result :
  holds M rho (source_def_iteration_formula environment n body result) <->
  source_def_iteration M environment (evalM M rho n) (evalM M rho body) (evalM M rho result).
Proof.
  unfold source_def_iteration_formula. rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite recursion_graph_formula_correct.
  setoid_rewrite source_def_recursion_graph.
  setoid_rewrite def_iteration_equality_correct.
  setoid_rewrite def_iteration_eval_shift.
  change ((exists x, x = evalM M rho body /\
    source_def_iteration M environment (evalM M rho n) x (evalM M rho result)) <->
    source_def_iteration M environment (evalM M rho n) (evalM M rho body) (evalM M rho result)).
  split; [intros [x [-> H]]; exact H|intro H; eexists; auto].
Qed.

Theorem source_def_iteration_result_definable M environment n body :
  Definable1 M (fun result => source_def_iteration M environment n body result).
Proof.
  exists (source_def_iteration_formula environment $1 $2 $0), (n .: body .: fun _ => zeroM M).
  intro result. symmetry. apply source_def_iteration_formula_correct.
Qed.

Theorem source_def_iteration_length_definable M environment body result :
  Definable1 M (fun n => source_def_iteration M environment n body result).
Proof.
  exists (source_def_iteration_formula environment $0 $1 $2), (body .: result .: fun _ => zeroM M).
  intro n. symmetry. apply source_def_iteration_formula_correct.
Qed.

Lemma source_def_iteration_zero_forward M environment body result :
  source_def_iteration M environment (zeroM M) body result -> result=body.
Proof.
  intros [b [c [Hsteps Hres]]].
  specialize (Hsteps (zeroM M) result (coding_lt_succ M (zeroM M)) Hres).
  destruct Hsteps as [[_ H]|[k [p [H _]]]]; [exact H|].
  exfalso. exact (zero_ne_succ M k H).
Qed.

Theorem source_def_iteration_zero M environment body result :
  source_def_iteration M environment (zeroM M) body result <-> result=body.
Proof.
  split; [apply source_def_iteration_zero_forward|intro H; subst result].
  destruct (source_def_iteration_total M environment (zeroM M) body) as [v Hv].
  pose proof (source_def_iteration_zero_forward M environment body v Hv) as ->. exact Hv.
Qed.

Lemma source_def_iteration_succ_forward M environment n body result :
  source_def_iteration M environment (succM M n) body result ->
  exists previous, source_def_iteration M environment n body previous /\
    source_def_step M environment previous result.
Proof.
  intros [b [c [Hsteps Hres]]].
  pose proof (Hsteps (succM M n) result (coding_lt_succ M (succM M n)) Hres) as Hstep.
  destruct Hstep as [[H _]|[k [p [Hk [Hp Hv]]]]].
  - exfalso. apply (zero_ne_succ M n). symmetry. exact H.
  - assert (n=k) by (apply (succ_injective M); exact Hk). subst k.
    exists p. split; [|exact Hv].
    exists b,c. split; [|exact Hp]. intros i v Hi Hiv.
    apply Hsteps; [|exact Hiv]. apply coding_lt_succ_cases. now left.
Qed.

Theorem source_def_iteration_succ M environment n body result :
  source_def_iteration M environment (succM M n) body result <->
  exists previous, source_def_iteration M environment n body previous /\
    source_def_step M environment previous result.
Proof.
  split; [apply source_def_iteration_succ_forward|].
  intros [p [Hp Hr]].
  destruct (source_def_iteration_total M environment (succM M n) body) as [v Hv].
  destruct (source_def_iteration_succ_forward M environment n body v Hv) as [q [Hq Hrv]].
  assert (p=q) by (eapply source_def_iteration_functional; eassumption). subst q.
  assert (result=v) by (eapply source_def_step_functional; eassumption).
  now subst result.
Qed.


Print Assumptions source_def_iteration_total.
Print Assumptions source_def_iteration_functional.
Print Assumptions source_def_iteration_formula_correct.
Print Assumptions source_def_iteration_zero.
Print Assumptions source_def_iteration_succ.
