(** Iterated universal closure in arbitrary PA models. The length is a model
    element, and the recursion is certified by an internally finite beta
    table. The host-natural iteration below is only a calibration theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension CodeExpressions NumericalProofs ProofClosure InternalRecursion
  SentenceBounds StandardModel SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
Unset Implicit Arguments.

Definition all_step M body b c n v : Prop :=
  (n = zeroM M /\ v = body) \/
  exists k p, n = succM M k /\ beta M b c k p /\
    sf_relation M SFAll p (zeroM M) v.

(** The step environment is value,index,modulus,dividend,body,parameters. *)
Definition all_step_formula : pa_form :=
  (($1 == zero) ∧ ($0 == $4)) ∨
  ∃∃ ($3 == σ $1 ∧ beta_formula $5 $4 $1 $0 ∧
    sf_formula SFAll $0 zero $2).

Local Opaque beta_formula sf_formula.

Lemma all_step_formula_correct M rho b c n v :
  recursion_step M all_step_formula rho b c n v <->
  all_step M (rho 0) b c n v.
Proof.
  unfold recursion_step,all_step_formula,all_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct.
  change (((n = zeroM M /\ v = rho 0) \/
    (exists k p, (n = succM M k /\ beta M b c k p) /\
      sf_relation M SFAll p (zeroM M) v)) <->
    ((n = zeroM M /\ v = rho 0) \/
    exists k p, n = succM M k /\ beta M b c k p /\
      sf_relation M SFAll p (zeroM M) v)).
  split.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
  - intros [H|[k [p H]]].
    + now left.
    + right. exists k,p. tauto.
Qed.

Lemma all_step_total M body b c n : exists v, all_step M body b c n v.
Proof.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) n) as [H0|[k Hk]].
  - exists body. left. auto.
  - destruct (beta_total M b c k) as [p Hp].
    destruct (sf_relation_total M SFAll p (zeroM M)) as [v Hv].
    exists v. right. exists k,p. auto.
Qed.

Lemma all_step_functional M body b c n v w :
  all_step M body b c n v -> all_step M body b c n w -> v=w.
Proof.
  intros [[H0 ->]|[k [p [Hk [Hp Hv]]]]]
    [[H0' ->]|[j [q [Hj [Hq Hw]]]]].
  - reflexivity.
  - exfalso. apply (zero_ne_succ M j). congruence.
  - exfalso. apply (zero_ne_succ M k). congruence.
  - assert (k=j) by (apply (succ_injective M); congruence). subst j.
    assert (p=q) by (eapply beta_unique; eassumption). subst q.
    eapply sf_relation_functional; eassumption.
Qed.

Lemma all_step_prefix M body b c b' c' n :
  prefix M b c b' c' n -> forall v,
  (all_step M body b c n v <-> all_step M body b' c' n v).
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

Definition all_prefix M n body result : Prop :=
  exists b c,
    (forall i v, coding_lt M i (succM M n) -> beta M b c i v ->
      all_step M body b c i v) /\ beta M b c n result.

Lemma all_prefix_recursion_graph M rho n result :
  recursion_graph M all_step_formula rho n result <->
  all_prefix M n (rho 0) result.
Proof.
  unfold recursion_graph,recursion_prefix,all_prefix.
  setoid_rewrite all_step_formula_correct. reflexivity.
Qed.

Theorem all_prefix_total M n body : exists result, all_prefix M n body result.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Htotal : forall b c i, exists v,
    recursion_step M all_step_formula rho b c i v).
  { intros b c i. setoid_rewrite all_step_formula_correct. apply all_step_total. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M all_step_formula rho b c i v <->
     recursion_step M all_step_formula rho b' c' i v)).
  { intros b c b' c' i Hp v. rewrite !all_step_formula_correct.
    now apply all_step_prefix. }
  destruct (recursion_graph_total M all_step_formula rho Htotal Hprefix n) as [v Hv].
  exists v. apply all_prefix_recursion_graph in Hv. exact Hv.
Qed.

Theorem all_prefix_functional M n body v w :
  all_prefix M n body v -> all_prefix M n body w -> v=w.
Proof.
  set (rho := body .: fun _ => zeroM M).
  assert (Hfun : forall b c i v w,
    recursion_step M all_step_formula rho b c i v ->
    recursion_step M all_step_formula rho b c i w -> v=w).
  { intros b c i v' w'. rewrite !all_step_formula_correct.
    apply all_step_functional. }
  assert (Hprefix : forall b c b' c' i,
    prefix M b c b' c' i -> forall v,
    (recursion_step M all_step_formula rho b c i v <->
     recursion_step M all_step_formula rho b' c' i v)).
  { intros b c b' c' i Hp v'. rewrite !all_step_formula_correct.
    now apply all_step_prefix. }
  change (all_prefix M n (rho 0) v -> all_prefix M n (rho 0) w -> v=w).
  rewrite <- !all_prefix_recursion_graph.
  exact (recursion_graph_functional M all_step_formula rho Hfun Hprefix n v w).
Qed.

Definition all_prefix_formula (n body result : pa_term) : pa_form :=
  ∃ ($0 == body`[↑] ∧ recursion_graph_formula all_step_formula
    n`[↑] result`[↑]).

Lemma closure_eval_shift M rho x t :
  evalM M (x .: rho) t`[↑] = evalM M rho t.
Proof. unfold evalM. apply eval_up. Qed.

Lemma closure_equality_correct M rho (t u : pa_term) :
  holds M rho (t == u) <-> evalM M rho t = evalM M rho u.
Proof. reflexivity. Qed.

Theorem all_prefix_formula_correct M rho n body result :
  holds M rho (all_prefix_formula n body result) <->
  all_prefix M (evalM M rho n) (evalM M rho body) (evalM M rho result).
Proof.
  unfold all_prefix_formula. rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite recursion_graph_formula_correct.
  setoid_rewrite all_prefix_recursion_graph.
  setoid_rewrite closure_equality_correct.
  setoid_rewrite closure_eval_shift.
  change ((exists x, x = evalM M rho body /\
    all_prefix M (evalM M rho n) x (evalM M rho result)) <->
    all_prefix M (evalM M rho n) (evalM M rho body) (evalM M rho result)).
  split; [intros [x [-> H]]; exact H|intro H; eexists; auto].
Qed.

Theorem all_prefix_result_definable M n body :
  Definable1 M (fun result => all_prefix M n body result).
Proof.
  exists (all_prefix_formula $1 $2 $0), (n .: body .: fun _ => zeroM M).
  intro result. symmetry. apply all_prefix_formula_correct.
Qed.

Theorem all_prefix_length_definable M body result :
  Definable1 M (fun n => all_prefix M n body result).
Proof.
  exists (all_prefix_formula $0 $1 $2), (body .: result .: fun _ => zeroM M).
  intro n. symmetry. apply all_prefix_formula_correct.
Qed.

Lemma all_prefix_zero_forward M body result :
  all_prefix M (zeroM M) body result -> result=body.
Proof.
  intros [b [c [Hsteps Hres]]].
  specialize (Hsteps (zeroM M) result (coding_lt_succ M (zeroM M)) Hres).
  destruct Hsteps as [[_ H]|[k [p [H _]]]]; [exact H|].
  exfalso. exact (zero_ne_succ M k H).
Qed.

Theorem all_prefix_zero M body result :
  all_prefix M (zeroM M) body result <-> result=body.
Proof.
  split; [apply all_prefix_zero_forward|intro H; subst result].
  destruct (all_prefix_total M (zeroM M) body) as [v Hv].
  pose proof (all_prefix_zero_forward M body v Hv) as ->. exact Hv.
Qed.

Lemma all_prefix_succ_forward M n body result :
  all_prefix M (succM M n) body result ->
  exists previous, all_prefix M n body previous /\
    sf_relation M SFAll previous (zeroM M) result.
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

Theorem all_prefix_succ M n body result :
  all_prefix M (succM M n) body result <->
  exists previous, all_prefix M n body previous /\
    sf_relation M SFAll previous (zeroM M) result.
Proof.
  split; [apply all_prefix_succ_forward|].
  intros [p [Hp Hr]].
  destruct (all_prefix_total M (succM M n) body) as [v Hv].
  destruct (all_prefix_succ_forward M n body v Hv) as [q [Hq Hrv]].
  assert (p=q) by (eapply all_prefix_functional; eassumption). subst q.
  assert (result=v) by (eapply sf_relation_functional; eassumption).
  now subst result.
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Fixpoint source_all_prefix (n : nat) (phi : sf_form) : sf_form :=
  match n with 0 => phi | S k => quant All (source_all_prefix k phi) end.

Lemma source_all_prefix_forall_times n phi :
  source_all_prefix n phi = forall_times n phi.
Proof. unfold forall_times. induction n; cbn; congruence. Qed.

Theorem all_prefix_source_calibration n phi :
  all_prefix natModel n (sf_encode phi) (sf_encode (source_all_prefix n phi)).
Proof.
  induction n as [|n IH].
  - apply all_prefix_zero. reflexivity.
  - apply all_prefix_succ. eexists. split; [exact IH|].
    unfold sf_relation. rewrite code_relation_natModel. reflexivity.
Qed.

Theorem all_prefix_standard_iff n phi result :
  all_prefix natModel n (sf_encode phi) result <->
  result = sf_encode (source_all_prefix n phi).
Proof.
  split.
  - intro H. eapply all_prefix_functional; [exact H|apply all_prefix_source_calibration].
  - intros ->. apply all_prefix_source_calibration.
Qed.

Corollary all_prefix_forall_times n phi result :
  all_prefix natModel n (sf_encode phi) result <->
  result = sf_encode (forall_times n phi).
Proof. rewrite all_prefix_standard_iff, source_all_prefix_forall_times. reflexivity. Qed.

Lemma all_prefix_formula_bounded : bounded 3 (all_prefix_formula $2 $1 $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions all_prefix_total.
Print Assumptions all_prefix_functional.
Print Assumptions all_prefix_formula_correct.
Print Assumptions all_prefix_zero.
Print Assumptions all_prefix_succ.
Print Assumptions all_prefix_source_calibration.
Print Assumptions all_prefix_standard_iff.
Print Assumptions all_prefix_formula_bounded.
Print Assumptions all_prefix_result_definable.
Print Assumptions all_prefix_length_definable.
Print Assumptions all_prefix_forall_times.
