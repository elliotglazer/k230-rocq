(** Arbitrary internally many iterations of the exact guarded Dn step.
    Totality and functionality use internally coded numerical recursion. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension CodeExpressions NumericalProofs ProofClosure InternalRecursion
  SentenceBounds StandardModel SetFormulaCodes SourceDnStep.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Definition dn_recursion_step M body b c n v : Prop :=
  (n = zeroM M /\ v = body) \/
  exists k p, n = succM M k /\ beta M b c k p /\
    source_dn_successor M p v.

(** The step environment is value,index,modulus,dividend,body,parameters. *)
Definition dn_recursion_step_formula : pa_form :=
  (($1 == zero) ∧ ($0 == $4)) ∨
  ∃∃ ($3 == σ $1 ∧ beta_formula $5 $4 $1 $0 ∧
    source_dn_successor_formula $0 $2).

Local Opaque beta_formula source_dn_successor_formula.

Lemma dn_recursion_step_formula_correct M rho b c n v :
  recursion_step M dn_recursion_step_formula rho b c n v <->
  dn_recursion_step M (rho 0) b c n v.
Proof.
  unfold recursion_step,dn_recursion_step_formula,dn_recursion_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite source_dn_successor_formula_correct.
  change (((n = zeroM M /\ v = rho 0) \/
    (exists k p, (n = succM M k /\ beta M b c k p) /\
      source_dn_successor M p v)) <->
    ((n = zeroM M /\ v = rho 0) \/
    exists k p, n = succM M k /\ beta M b c k p /\
      source_dn_successor M p v)).
  split.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
Qed.

Lemma dn_recursion_step_total M body b c n : exists v, dn_recursion_step M body b c n v.
Proof.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) n) as [H0|[k Hk]].
  - exists body. left. auto.
  - destruct (beta_total M b c k) as [p Hp].
    destruct (source_dn_successor_total M p) as [v Hv].
    exists v. right. exists k,p. auto.
Qed.

Lemma dn_recursion_step_functional M body b c n v w :
  dn_recursion_step M body b c n v -> dn_recursion_step M body b c n w -> v=w.
Proof.
  intros [[H0 ->]|[k [p [Hk [Hp Hv]]]]]
    [[H0' ->]|[j [q [Hj [Hq Hw]]]]].
  - reflexivity.
  - exfalso. apply (zero_ne_succ M j). congruence.
  - exfalso. apply (zero_ne_succ M k). congruence.
  - assert (k=j) by (apply (succ_injective M); congruence). subst j.
    assert (p=q) by (eapply beta_unique; eassumption). subst q.
    eapply source_dn_successor_functional; eassumption.
Qed.

Lemma dn_recursion_step_prefix M body b c b' c' n :
  prefix M b c b' c' n -> forall v,
  (dn_recursion_step M body b c n v <-> dn_recursion_step M body b' c' n v).
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

Definition source_dn M n body result : Prop :=
  exists b c,
    (forall i v, coding_lt M i (succM M n) -> beta M b c i v ->
      dn_recursion_step M body b c i v) /\ beta M b c n result.

Lemma source_dn_recursion_graph M rho n result :
  recursion_graph M dn_recursion_step_formula rho n result <->
  source_dn M n (rho 0) result.
Proof.
  unfold recursion_graph,recursion_prefix,source_dn.
  setoid_rewrite dn_recursion_step_formula_correct. reflexivity.
Qed.

Theorem source_dn_total M n body : exists result, source_dn M n body result.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Htotal : forall b c i, exists v,
    recursion_step M dn_recursion_step_formula rho b c i v).
  { intros b c i. setoid_rewrite dn_recursion_step_formula_correct. apply dn_recursion_step_total. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M dn_recursion_step_formula rho b c i v <->
     recursion_step M dn_recursion_step_formula rho b' c' i v)).
  { intros b c b' c' i Hp v. rewrite !dn_recursion_step_formula_correct.
    now apply dn_recursion_step_prefix. }
  destruct (recursion_graph_total M dn_recursion_step_formula rho Htotal Hprefix n) as [v Hv].
  exists v. apply source_dn_recursion_graph in Hv. exact Hv.
Qed.

Theorem source_dn_functional M n body v w :
  source_dn M n body v -> source_dn M n body w -> v=w.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Hfun : forall b c i v w,
    recursion_step M dn_recursion_step_formula rho b c i v ->
    recursion_step M dn_recursion_step_formula rho b c i w -> v=w).
  { intros b c i v' w'. rewrite !dn_recursion_step_formula_correct.
    apply dn_recursion_step_functional. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M dn_recursion_step_formula rho b c i v <->
     recursion_step M dn_recursion_step_formula rho b' c' i v)).
  { intros b c b' c' i Hp v'. rewrite !dn_recursion_step_formula_correct.
    now apply dn_recursion_step_prefix. }
  change (source_dn M n (rho 0) v -> source_dn M n (rho 0) w -> v=w).
  rewrite <- !source_dn_recursion_graph.
  exact (recursion_graph_functional M dn_recursion_step_formula rho Hfun Hprefix n v w).
Qed.

Definition source_dn_formula (n body result : pa_term) : pa_form :=
  ∃ ($0 == body`[↑] ∧ recursion_graph_formula dn_recursion_step_formula
    n`[↑] result`[↑]).

Lemma closure_eval_shift M rho x t :
  evalM M (x .: rho) t`[↑] = evalM M rho t.
Proof. unfold evalM. apply eval_up. Qed.

Lemma closure_equality_correct M rho (t u : pa_term) :
  holds M rho (t == u) <-> evalM M rho t = evalM M rho u.
Proof. reflexivity. Qed.

Theorem source_dn_formula_correct M rho n body result :
  holds M rho (source_dn_formula n body result) <->
  source_dn M (evalM M rho n) (evalM M rho body) (evalM M rho result).
Proof.
  unfold source_dn_formula. rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite recursion_graph_formula_correct.
  setoid_rewrite source_dn_recursion_graph.
  setoid_rewrite closure_equality_correct.
  setoid_rewrite closure_eval_shift.
  change ((exists x, x = evalM M rho body /\
    source_dn M (evalM M rho n) x (evalM M rho result)) <->
    source_dn M (evalM M rho n) (evalM M rho body) (evalM M rho result)).
  split; [intros [x [-> H]]; exact H|intro H; eexists; auto].
Qed.

Theorem source_dn_result_definable M n body :
  Definable1 M (fun result => source_dn M n body result).
Proof.
  exists (source_dn_formula $1 $2 $0), (n .: body .: fun _ => zeroM M).
  intro result. symmetry. apply source_dn_formula_correct.
Qed.

Theorem source_dn_length_definable M body result :
  Definable1 M (fun n => source_dn M n body result).
Proof.
  exists (source_dn_formula $0 $1 $2), (body .: result .: fun _ => zeroM M).
  intro n. symmetry. apply source_dn_formula_correct.
Qed.

Lemma source_dn_zero_forward M body result :
  source_dn M (zeroM M) body result -> result=body.
Proof.
  intros [b [c [Hsteps Hres]]].
  specialize (Hsteps (zeroM M) result (coding_lt_succ M (zeroM M)) Hres).
  destruct Hsteps as [[_ H]|[k [p [H _]]]]; [exact H|].
  exfalso. exact (zero_ne_succ M k H).
Qed.

Theorem source_dn_zero M body result :
  source_dn M (zeroM M) body result <-> result=body.
Proof.
  split; [apply source_dn_zero_forward|intro H; subst result].
  destruct (source_dn_total M (zeroM M) body) as [v Hv].
  pose proof (source_dn_zero_forward M body v Hv) as ->. exact Hv.
Qed.

Lemma source_dn_succ_forward M n body result :
  source_dn M (succM M n) body result ->
  exists previous, source_dn M n body previous /\
    source_dn_successor M previous result.
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

Theorem source_dn_succ M n body result :
  source_dn M (succM M n) body result <->
  exists previous, source_dn M n body previous /\
    source_dn_successor M previous result.
Proof.
  split; [apply source_dn_succ_forward|].
  intros [p [Hp Hr]].
  destruct (source_dn_total M (succM M n) body) as [v Hv].
  destruct (source_dn_succ_forward M n body v Hv) as [q [Hq Hrv]].
  assert (p=q) by (eapply source_dn_functional; eassumption). subst q.
  assert (result=v) by (eapply source_dn_successor_functional; eassumption).
  now subst result.
Qed.


Print Assumptions source_dn_total.
Print Assumptions source_dn_functional.
Print Assumptions source_dn_formula_correct.
Print Assumptions source_dn_zero.
Print Assumptions source_dn_succ.
