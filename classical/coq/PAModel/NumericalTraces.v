(** Internally finite derivation traces for numerical computations.
    A row is one number, which can encode both the input and output of a
    recursive call. Rules may inspect zero, one, or two previous rows.
    All indices and trace lengths belong to the arbitrary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension BetaPacking CodeExpressions NumericalProofs ProofClosure
  TheoryProofInduction CourseOfValues.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Record NumericalRules : Type := {
  rule_base_formula : form;
  rule_base_bound : bounded 1 rule_base_formula;
  rule_unary_formula : form;
  rule_unary_bound : bounded 2 rule_unary_formula;
  rule_binary_formula : form;
  rule_binary_bound : bounded 3 rule_binary_formula
}.

Definition trace_base M R v :=
  holds M (v .: fun _ => zeroM M) (rule_base_formula R).
Definition trace_unary M R v p :=
  holds M (v .: p .: fun _ => zeroM M) (rule_unary_formula R).
Definition trace_binary M R v p q :=
  holds M (v .: p .: q .: fun _ => zeroM M) (rule_binary_formula R).

Definition trace_base_instance R (v : term) := (rule_base_formula R)[v..].
Definition trace_unary_instance R (v p : term) :=
  (rule_unary_formula R)[v .: p..].
Definition trace_binary_instance R (v p q : term) :=
  (rule_binary_formula R)[v .: p .: q..].

Lemma trace_base_instance_correct M R rho v :
  holds M rho (trace_base_instance R v) <-> trace_base M R (evalM M rho v).
Proof.
  unfold trace_base_instance, trace_base, holds. rewrite sat_comp.
  apply (bound_ext _ (rule_base_bound R)). intros [|i] Hi; [reflexivity|lia].
Qed.
Lemma trace_unary_instance_correct M R rho v p :
  holds M rho (trace_unary_instance R v p) <->
  trace_unary M R (evalM M rho v) (evalM M rho p).
Proof.
  unfold trace_unary_instance, trace_unary, holds. rewrite sat_comp.
  apply (bound_ext _ (rule_unary_bound R)).
  intros [|[|i]] Hi; try reflexivity; lia.
Qed.
Lemma trace_binary_instance_correct M R rho v p q :
  holds M rho (trace_binary_instance R v p q) <->
  trace_binary M R (evalM M rho v) (evalM M rho p) (evalM M rho q).
Proof.
  unfold trace_binary_instance, trace_binary, holds. rewrite sat_comp.
  apply (bound_ext _ (rule_binary_bound R)).
  intros [|[|[|i]]] Hi; try reflexivity; lia.
Qed.

Definition trace_justified M R b c i v :=
  trace_base M R v \/
  (exists j p, coding_lt M j i /\ beta M b c j p /\ trace_unary M R v p) \/
  (exists j k p q, coding_lt M j i /\ coding_lt M k i /\
    beta M b c j p /\ beta M b c k q /\ trace_binary M R v p q).

Definition trace_justified_formula R (b c i v : term) : form :=
  trace_base_instance R v ∨
  ((∃∃ (Peano.sless $1 (code_lift2 i) ∧
     beta_formula (code_lift2 b) (code_lift2 c) $1 $0 ∧
     trace_unary_instance R (code_lift2 v) $0)) ∨
   (∃∃∃∃ (Peano.sless $3 (lift4 i) ∧ Peano.sless $2 (lift4 i) ∧
     beta_formula (lift4 b) (lift4 c) $3 $1 ∧
     beta_formula (lift4 b) (lift4 c) $2 $0 ∧
     trace_binary_instance R (lift4 v) $1 $0))).

Local Opaque holds trace_base_instance trace_unary_instance
  trace_binary_instance beta_formula Peano.sless.

Lemma trace_justified_formula_correct M R rho b c i v :
  holds M rho (trace_justified_formula R b c i v) <->
  trace_justified M R (evalM M rho b) (evalM M rho c)
    (evalM M rho i) (evalM M rho v).
Proof.
  unfold trace_justified_formula,trace_justified.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  rewrite trace_base_instance_correct.
  setoid_rewrite trace_unary_instance_correct.
  setoid_rewrite trace_binary_instance_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite beta_formula_correct.
  repeat setoid_rewrite code_eval_lift2. try setoid_rewrite lift4_correct.
  split; intros [H|[H|H]].
  - now left.
  - right; left. destruct H as [j [p H]]. exists j,p. tauto.
  - right; right. destruct H as [j [k [p [q H]]]]. exists j,k,p,q. tauto.
  - now left.
  - right; left. destruct H as [j [p H]]. exists j,p. tauto.
  - right; right. destruct H as [j [k [p [q H]]]]. exists j,k,p,q. tauto.
Qed.

Definition trace_sequence M R b c n :=
  forall i v, coding_lt M i n -> beta M b c i v -> trace_justified M R b c i v.
Definition trace_sequence_formula R (b c n : term) : form :=
  ∀∀ (Peano.sless $1 (code_lift2 n) →
    beta_formula (code_lift2 b) (code_lift2 c) $1 $0 →
    trace_justified_formula R (code_lift2 b) (code_lift2 c) $1 $0).

Local Opaque trace_justified_formula.
Lemma trace_sequence_formula_correct M R rho b c n :
  holds M rho (trace_sequence_formula R b c n) <->
  trace_sequence M R (evalM M rho b) (evalM M rho c) (evalM M rho n).
Proof.
  unfold trace_sequence_formula,trace_sequence.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite beta_formula_correct.
  setoid_rewrite trace_justified_formula_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Definition trace_derives M R v := exists b c n,
  trace_sequence M R b c (succM M n) /\ beta M b c n v.
Definition trace_derives_formula R (v : term) : form :=
  ∃∃∃ (trace_sequence_formula R $2 $1 (σ $0) ∧
    beta_formula $2 $1 $0 (lift3 v)).

Local Opaque trace_sequence_formula.
Lemma trace_derives_formula_correct M R rho v :
  holds M rho (trace_derives_formula R v) <-> trace_derives M R (evalM M rho v).
Proof.
  unfold trace_derives_formula,trace_derives.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite trace_sequence_formula_correct.
  setoid_rewrite beta_formula_correct. setoid_rewrite lift3_correct. reflexivity.
Qed.

Lemma trace_derives_definable M R : Definable1 M (trace_derives M R).
Proof.
  exists (trace_derives_formula R $0),(fun _ => zeroM M).
  intro v. symmetry. apply trace_derives_formula_correct.
Qed.

Section Closure.
Variable M : Model.
Variable R : NumericalRules.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).

Lemma trace_lt_cases i n : coding_lt M i n \/ ~coding_lt M i n.
Proof.
  destruct (@Peano.trichotomy D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i n) as [Hlt|[Heq|Hgt]].
  - now left.
  - right. intro H. exact (@Peano.lt_neq D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) i n H Heq).
  - right. intro H. pose proof (coding_lt_trans M i n i H Hgt) as Hii.
    exact (@Peano.lt_neq D (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) i i Hii eq_refl).
Qed.

Lemma trace_justified_transport b c b' c' i i' (f : D -> D) v :
  (forall j, coding_lt M j i -> coding_lt M (f j) i') ->
  (forall j t, coding_lt M j i -> beta M b c j t -> beta M b' c' (f j) t) ->
  trace_justified M R b c i v -> trace_justified M R b' c' i' v.
Proof.
  intros Hlt Hr [Ha|[Hu|Hb]].
  - now left.
  - right; left. destruct Hu as [j [p [Hj [Hp H]]]].
    exists (f j),p. split; [now apply Hlt|]. split; [now apply Hr|exact H].
  - right; right. destruct Hb as [j [k [p [q [Hj [Hk [Hp [Hq H]]]]]]]].
    exists (f j),(f k),p,q. split; [now apply Hlt|].
    split; [now apply Hlt|]. split; [now apply Hr|]. split; [now apply Hr|exact H].
Qed.

Lemma trace_sequence_transfer b c b' c' n :
  prefix M b c b' c' n -> trace_sequence M R b c n -> trace_sequence M R b' c' n.
Proof.
  intros Hp Hseq i v Hi Hv.
  apply (trace_justified_transport b c b' c' i i (fun j => j) v).
  - auto.
  - intros j t Hj Ht. apply Hp; [eapply coding_lt_trans; eassumption|exact Ht].
  - apply Hseq; [exact Hi|]. exact (prefix_back M b c b' c' n Hp i v Hi Hv).
Qed.

Lemma trace_sequence_append b c b' c' n v :
  trace_sequence M R b c n -> prefix M b c b' c' n -> beta M b' c' n v ->
  trace_justified M R b' c' n v -> trace_sequence M R b' c' (S n).
Proof.
  intros Hseq Hp Hv Hj i u Hi Hu.
  destruct (proj1 (coding_lt_succ_cases M i n) Hi) as [Hin| ->].
  - exact (trace_sequence_transfer b c b' c' n Hp Hseq i u Hin Hu).
  - assert (u=v) by (eapply beta_unique; eassumption). now subst u.
Qed.

Theorem trace_derives_base v : trace_base M R v -> trace_derives M R v.
Proof.
  intro Ha. exists v,v,O. split; [|apply beta_singleton].
  intros i u Hi Hu.
  destruct (proj1 (coding_lt_succ_cases M i O) Hi) as [Hin| ->].
  - exfalso. exact (coding_not_lt_zero M i Hin).
  - assert (u=v) by (eapply beta_unique; [exact Hu|apply beta_singleton]).
    subst u. now left.
Qed.

Theorem trace_derives_unary v p :
  trace_derives M R p -> trace_unary M R v p -> trace_derives M R v.
Proof.
  intros [b [c [n [Hseq Hp]]]] Hu.
  destruct (beta_extension M b c (S n) v) as [b' [c' [Hpre Hv]]].
  exists b',c',(S n). split; [|exact Hv].
  apply (trace_sequence_append b c b' c' (S n) v Hseq Hpre Hv).
  right; left. exists n,p. split; [apply coding_lt_succ|].
  split; [apply Hpre; [apply coding_lt_succ|exact Hp]|exact Hu].
Qed.

Lemma trace_sequence_concatenate b c l d e n b' c' :
  trace_sequence M R b c l -> trace_sequence M R d e n ->
  prefix M b c b' c' l ->
  (forall j v, coding_lt M j n -> beta M d e j v -> beta M b' c' (l+j) v) ->
  trace_sequence M R b' c' (l+n).
Proof.
  intros Hleft Hright Hl Hr i v Hi Hv.
  destruct (trace_lt_cases i l) as [Hil|Hil].
  - exact (trace_sequence_transfer b c b' c' l Hl Hleft i v Hil Hv).
  - destruct (coding_difference M i l Hil) as [j ->].
    assert (Hj : coding_lt M j n) by (eapply lt_add_cancel; exact Hi).
    destruct (beta_total M d e j) as [u Hu].
    assert (E : u=v) by (eapply beta_unique; [exact (Hr j u Hj Hu)|exact Hv]).
    subst u. apply (trace_justified_transport d e b' c' j (l+j) (fun k => l+k) v).
    + intros k Hk. now apply coding_lt_add_left.
    + intros k t Hk Ht. apply Hr; [eapply coding_lt_trans; eassumption|exact Ht].
    + exact (Hright j v Hj Hu).
Qed.

Theorem trace_derives_binary v p q :
  trace_derives M R p -> trace_derives M R q ->
  trace_binary M R v p q -> trace_derives M R v.
Proof.
  intros [b [c [i [Hi Hp]]]] [d [e [j [Hj Hq]]]] Hbin.
  destruct (beta_concatenate M b c (S i) d e (S j)) as [t [u [Hl Hr]]].
  set (n := S i + S j).
  assert (Hseq : trace_sequence M R t u n).
  { apply (trace_sequence_concatenate b c (S i) d e (S j) t u Hi Hj Hl Hr). }
  assert (Hin : coding_lt M i n) by (apply lt_left_sum; apply coding_lt_succ).
  assert (Hjn : coding_lt M (S i+j) n) by (apply coding_lt_add_left; apply coding_lt_succ).
  assert (Hpt : beta M t u i p) by (apply Hl; [apply coding_lt_succ|exact Hp]).
  assert (Hqt : beta M t u (S i+j) q) by (apply Hr; [apply coding_lt_succ|exact Hq]).
  destruct (beta_extension M t u n v) as [t' [u' [Hpre Hv]]].
  exists t',u',n. split; [|exact Hv].
  apply (trace_sequence_append t u t' u' n v Hseq Hpre Hv).
  right; right. exists i,(S i+j),p,q.
  split; [exact Hin|]. split; [exact Hjn|].
  split; [exact (Hpre i p Hin Hpt)|]. split; [exact (Hpre (S i+j) q Hjn Hqt)|exact Hbin].
Qed.

Theorem trace_derives_induction (P : D -> Prop) :
  Definable1 M P ->
  (forall v, trace_base M R v -> P v) ->
  (forall v p, P p -> trace_unary M R v p -> P v) ->
  (forall v p q, P p -> P q -> trace_binary M R v p q -> P v) ->
  forall v, trace_derives M R v -> P v.
Proof.
  intros Hdef Hbase Hun Hbin v [b [c [n [Hseq Hlast]]]].
  assert (Hall : forall i, coding_lt M i (S n) -> forall v, beta M b c i v -> P v).
  { apply (definable_strong_induction M _ (proof_line_property_definable M P b c n Hdef)).
    intros i IH Hi u Hu. destruct (Hseq i u Hi Hu) as [Hb|[Hone|Htwo]].
    - exact (Hbase u Hb).
    - destruct Hone as [j [p [Hj [Hp Hr]]]]. apply (Hun u p).
      + exact (IH j Hj (coding_lt_trans M j i (S n) Hj Hi) p Hp).
      + exact Hr.
    - destruct Htwo as [j [k [p [q [Hj [Hk [Hp [Hq Hr]]]]]]]].
      apply (Hbin u p q).
      + exact (IH j Hj (coding_lt_trans M j i (S n) Hj Hi) p Hp).
      + exact (IH k Hk (coding_lt_trans M k i (S n) Hk Hi) q Hq).
      + exact Hr. }
  exact (Hall n (coding_lt_succ M n) v Hlast).
Qed.

(** Every entry in an internally finite trace itself has a trace: keep the
    same beta code and truncate its length immediately after that entry. *)
Theorem trace_sequence_member b c n i v :
  trace_sequence M R b c n -> coding_lt M i n -> beta M b c i v ->
  trace_derives M R v.
Proof.
  intros Hseq Hi Hv. exists b,c,i. split; [|exact Hv].
  intros j u Hj Hu. apply (Hseq j u); [|exact Hu].
  exact (coding_le_lt_trans M j i n Hj Hi).
Qed.

Theorem trace_derives_inv v : trace_derives M R v ->
  trace_base M R v \/
  (exists p, trace_derives M R p /\ trace_unary M R v p) \/
  (exists p q, trace_derives M R p /\ trace_derives M R q /\ trace_binary M R v p q).
Proof.
  intros [b [c [n [Hseq Hv]]]].
  destruct (Hseq n v (coding_lt_succ M n) Hv) as [Hb|[Hu|Hbin]].
  - now left.
  - right; left. destruct Hu as [j [p [Hj [Hp Hr]]]]. exists p. split; [|exact Hr].
    apply (trace_sequence_member b c (S n) j p Hseq); [|exact Hp].
    exact (coding_lt_trans M j n (S n) Hj (coding_lt_succ M n)).
  - right; right. destruct Hbin as [j [k [p [q [Hj [Hk [Hp [Hq Hr]]]]]]]].
    exists p,q. split.
    + apply (trace_sequence_member b c (S n) j p Hseq); [|exact Hp].
      exact (coding_lt_trans M j n (S n) Hj (coding_lt_succ M n)).
    + split; [|exact Hr].
      apply (trace_sequence_member b c (S n) k q Hseq); [|exact Hq].
      exact (coding_lt_trans M k n (S n) Hk (coding_lt_succ M n)).
Qed.

Theorem trace_derives_unfold v : trace_derives M R v <->
  trace_base M R v \/
  (exists p, trace_derives M R p /\ trace_unary M R v p) \/
  (exists p q, trace_derives M R p /\ trace_derives M R q /\ trace_binary M R v p q).
Proof.
  split; [apply trace_derives_inv|]. intros [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hbin]]]]]].
  - now apply trace_derives_base.
  - exact (trace_derives_unary v p Hp Hu).
  - exact (trace_derives_binary v p q Hp Hq Hbin).
Qed.
End Closure.

Print Assumptions trace_derives_formula_correct.
Print Assumptions trace_derives_definable.
Print Assumptions trace_derives_base.
Print Assumptions trace_derives_unary.
Print Assumptions trace_derives_binary.
Print Assumptions trace_derives_induction.
Print Assumptions trace_sequence_member.
Print Assumptions trace_derives_inv.
Print Assumptions trace_derives_unfold.
