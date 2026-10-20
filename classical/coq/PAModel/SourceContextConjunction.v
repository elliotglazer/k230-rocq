(** An actual internally finite conjunction of source context entries.
    Its length and every source code may be nonstandard PA-model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
  CodeExpressions NumericalProofs ProofClosure InternalRecursion SentenceBounds SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_context_conjunction_step M sb sc b c n v :=
  (n=zeroM M /\sf_relation M SFImpl (zeroM M)(zeroM M) v) \/
  exists k p h,n=succM M k /\beta M b c k p /\beta M sb sc k h /\sf_relation M SFAnd p h v.
Definition source_context_conjunction_step_formula :form :=
  (($1==zero) ∧sf_formula SFImpl zero zero $0) ∨
  ∃∃∃ ($4==σ $2 ∧beta_formula $6 $5 $2 $1 ∧
    beta_formula $7 $8 $2 $0 ∧sf_formula SFAnd $1 $0 $3).
Local Opaque beta_formula sf_formula.

Lemma source_context_conjunction_step_correct M rho b c n v :
  recursion_step M source_context_conjunction_step_formula rho b c n v <->
  source_context_conjunction_step M (rho 0)(rho 1) b c n v.
Proof.
  unfold recursion_step,source_context_conjunction_step_formula,source_context_conjunction_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct.
  change (((n=zeroM M /\sf_relation M SFImpl (zeroM M)(zeroM M) v) \/
    (exists k p h,((n=succM M k /\beta M b c k p) /\beta M (rho 0)(rho 1) k h) /\sf_relation M SFAnd p h v)) <->
    ((n=zeroM M /\sf_relation M SFImpl (zeroM M)(zeroM M) v) \/
    exists k p h,n=succM M k /\beta M b c k p /\beta M (rho 0)(rho 1) k h /\sf_relation M SFAnd p h v)).
  split;intros [H|[k [p [h H]]]];[now left|right;exists k,p,h;tauto|now left|right;exists k,p,h;tauto].
Qed.

Lemma source_context_conjunction_step_total M sb sc b c n :
  exists v,source_context_conjunction_step M sb sc b c n v.
Proof.
  destruct (@Peano.zero_or_succ (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) n) as [->|[k ->]].
  - destruct (sf_relation_total M SFImpl (zeroM M)(zeroM M)) as [v HV]. exists v. left. auto.
  - destruct (beta_total M b c k) as [p HP]. destruct (beta_total M sb sc k) as [h HH].
    destruct (sf_relation_total M SFAnd p h) as [v HV]. exists v. right. exists k,p,h. auto.
Qed.

Lemma source_context_conjunction_step_functional M sb sc b c n v w :
  source_context_conjunction_step M sb sc b c n v ->
  source_context_conjunction_step M sb sc b c n w ->v=w.
Proof.
  intros [[H0 HV]|[k [p [h [E [HP [HH HV]]]]]]]
    [[H0' HW]|[j [q [g [E' [HQ [HG HW]]]]]]].
  - exact (sf_relation_functional M SFImpl (zeroM M)(zeroM M) v w HV HW).
  - exfalso. apply (zero_ne_succ M j). congruence.
  - exfalso. apply (zero_ne_succ M k). congruence.
  - assert (k=j) by (apply (succ_injective M);congruence). subst j.
    assert (p=q) by (eapply beta_unique;eassumption). subst q.
    assert (h=g) by (eapply beta_unique;eassumption). subst g.
    exact (sf_relation_functional M SFAnd p h v w HV HW).
Qed.

Lemma source_context_conjunction_step_prefix M sb sc b c b' c' n :
  prefix M b c b' c' n ->forall v,
    (source_context_conjunction_step M sb sc b c n v <->
      source_context_conjunction_step M sb sc b' c' n v).
Proof.
  intros HPre v. split;intros [HZ|[k [p [h [-> [HP [HH HV]]]]]]].
  - now left.
  - right. exists k,p,h. split;[reflexivity|]. split;[|auto].
    exact (HPre k p (coding_lt_succ M k) HP).
  - now left.
  - right. exists k,p,h. split;[reflexivity|]. split;[|auto].
    exact (prefix_back M b c b' c' (succM M k) HPre k p (coding_lt_succ M k) HP).
Qed.

Definition source_context_conjunction M sb sc n result :=exists b c,
  (forall i v,coding_lt M i (succM M n) ->beta M b c i v ->
    source_context_conjunction_step M sb sc b c i v) /\beta M b c n result.

Lemma source_context_conjunction_recursion M rho n result :
  recursion_graph M source_context_conjunction_step_formula rho n result <->
  source_context_conjunction M (rho 0)(rho 1) n result.
Proof.
  unfold recursion_graph,recursion_prefix,source_context_conjunction.
  setoid_rewrite source_context_conjunction_step_correct. reflexivity.
Qed.

Theorem source_context_conjunction_total M sb sc n :
  exists result,source_context_conjunction M sb sc n result.
Proof.
  set (rho:=sb .: sc .: fun _=>zeroM M).
  assert (HT:forall b c i,exists v,recursion_step M source_context_conjunction_step_formula rho b c i v).
  { intros b c i. setoid_rewrite source_context_conjunction_step_correct. apply source_context_conjunction_step_total. }
  assert (HP:forall b c b' c' i,prefix M b c b' c' i ->forall v,
    (recursion_step M source_context_conjunction_step_formula rho b c i v <->
     recursion_step M source_context_conjunction_step_formula rho b' c' i v)).
  { intros b c b' c' i HP v. repeat setoid_rewrite source_context_conjunction_step_correct.
    exact (source_context_conjunction_step_prefix M sb sc b c b' c' i HP v). }
  destruct (recursion_graph_total M source_context_conjunction_step_formula rho HT HP n) as [v HV].
  exists v. exact (proj1 (source_context_conjunction_recursion M rho n v) HV).
Qed.

Theorem source_context_conjunction_functional M sb sc n f g :
  source_context_conjunction M sb sc n f ->source_context_conjunction M sb sc n g ->f=g.
Proof.
  set (rho:=sb .: sc .: fun _=>zeroM M).
  assert (HF:forall b c i v w,recursion_step M source_context_conjunction_step_formula rho b c i v ->
    recursion_step M source_context_conjunction_step_formula rho b c i w ->v=w).
  { intros b c i v w. repeat setoid_rewrite source_context_conjunction_step_correct.
    exact (source_context_conjunction_step_functional M sb sc b c i v w). }
  assert (HP:forall b c b' c' i,prefix M b c b' c' i ->forall v,
    (recursion_step M source_context_conjunction_step_formula rho b c i v <->
     recursion_step M source_context_conjunction_step_formula rho b' c' i v)).
  { intros b c b' c' i HP v. repeat setoid_rewrite source_context_conjunction_step_correct.
    exact (source_context_conjunction_step_prefix M sb sc b c b' c' i HP v). }
  change (source_context_conjunction M (rho 0)(rho 1) n f ->source_context_conjunction M (rho 0)(rho 1) n g ->f=g).
  rewrite <- !source_context_conjunction_recursion.
  exact (recursion_graph_functional M source_context_conjunction_step_formula rho HF HP n f g).
Qed.

Definition source_context_conjunction_formula (sb sc n result:term) :form :=
  ∃∃ ($0==sb`[↑]`[↑] ∧$1==sc`[↑]`[↑] ∧
    recursion_graph_formula source_context_conjunction_step_formula n`[↑]`[↑] result`[↑]`[↑]).
Lemma source_context_conjunction_eval_lift2 M rho x y t :
  evalM M (x .: y .: rho) t`[↑]`[↑]=evalM M rho t.
Proof. unfold evalM. now rewrite !eval_up. Qed.
Lemma source_context_conjunction_equality_correct M rho t u :
  holds M rho (t==u) <->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Theorem source_context_conjunction_formula_correct M rho sb sc n result :
  holds M rho (source_context_conjunction_formula sb sc n result) <->
  source_context_conjunction M (evalM M rho sb)(evalM M rho sc)(evalM M rho n)(evalM M rho result).
Proof.
  unfold source_context_conjunction_formula. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite recursion_graph_formula_correct.
  setoid_rewrite source_context_conjunction_recursion.
  setoid_rewrite source_context_conjunction_equality_correct.
  setoid_rewrite source_context_conjunction_eval_lift2.
  change ((exists x y,(y=evalM M rho sb /\x=evalM M rho sc) /\
    source_context_conjunction M y x (evalM M rho n)(evalM M rho result)) <->
    source_context_conjunction M (evalM M rho sb)(evalM M rho sc)(evalM M rho n)(evalM M rho result)).
  split;[intros [x [y [[-> ->] H]]];exact H|intro H;exists (evalM M rho sc),(evalM M rho sb);auto].
Qed.

Theorem source_context_conjunction_zero M sb sc result :
  source_context_conjunction M sb sc (zeroM M) result <->
    sf_relation M SFImpl (zeroM M)(zeroM M) result.
Proof.
  assert (Forward:forall result,source_context_conjunction M sb sc (zeroM M) result ->
    sf_relation M SFImpl (zeroM M)(zeroM M) result).
  { intros f [b [c [HSteps HF]]].
    specialize (HSteps (zeroM M) f (coding_lt_succ M (zeroM M)) HF).
    destruct HSteps as [[_ H]|[k [p [h [E _]]]]];[exact H|]. exfalso. exact (zero_ne_succ M k E). }
  split;[apply Forward|intro H].
  destruct (source_context_conjunction_total M sb sc (zeroM M)) as [g HG].
  pose proof (sf_relation_functional M SFImpl (zeroM M)(zeroM M) g result (Forward g HG) H) as ->. exact HG.
Qed.

Theorem source_context_conjunction_succ M sb sc n result :
  source_context_conjunction M sb sc (succM M n) result <->
  exists p h,source_context_conjunction M sb sc n p /\beta M sb sc n h /\sf_relation M SFAnd p h result.
Proof.
  assert (Forward:forall f,source_context_conjunction M sb sc (succM M n) f ->
    exists p h,source_context_conjunction M sb sc n p /\beta M sb sc n h /\sf_relation M SFAnd p h f).
  { intros f [b [c [HSteps HF]]].
    pose proof (HSteps (succM M n) f (coding_lt_succ M (succM M n)) HF) as HStep.
    destruct HStep as [[E _]|[k [p [h [E [HP [HH HV]]]]]]].
    - exfalso. apply (zero_ne_succ M n). symmetry. exact E.
    - assert (n=k) by (apply (succ_injective M);exact E). subst k.
      exists p,h. split;[|auto]. exists b,c. split;[|exact HP].
      intros i v HI HV'. apply HSteps;[|exact HV']. apply coding_lt_succ_cases. now left. }
  split;[apply Forward|]. intros [p [h [HP [HH HV]]]].
  destruct (source_context_conjunction_total M sb sc (succM M n)) as [g HG].
  destruct (Forward g HG) as [q [j [HQ [HJ HVG]]]].
  assert (p=q) by (eapply source_context_conjunction_functional;eassumption). subst q.
  assert (h=j) by (eapply beta_unique;eassumption). subst j.
  pose proof (sf_relation_functional M SFAnd p h g result HVG HV) as ->. exact HG.
Qed.

Print Assumptions source_context_conjunction_total.
Print Assumptions source_context_conjunction_functional.
Print Assumptions source_context_conjunction_formula_correct.
Print Assumptions source_context_conjunction_zero.
Print Assumptions source_context_conjunction_succ.
