(** Internally finite de Bruijn environments in arbitrary ordinary PA models.
    An environment is the triple (b,c,n): the first n beta entries, followed
    by zero. Lengths, indices, entries and codes all belong to the carrier.
    Cons uses existing beta packing, not external finite iteration or choice. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  BetaExtension BetaPacking.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition environment_lookup (M : Model)
    (b c n i v : carrier M) : Prop :=
  (coding_lt M i n /\ beta M b c i v) \/
  (~coding_lt M i n /\ v = zeroM M).

Definition environment_lookup_formula (b c n i v : term) : form :=
  (Peano.sless i n ∧ beta_formula b c i v) ∨
  ((Peano.sless i n → ⊥) ∧ v == zero).

Theorem environment_lookup_formula_correct (M : Model) rho b c n i v :
  holds M rho (environment_lookup_formula b c n i v) <->
  environment_lookup M (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho i) (evalM M rho v).
Proof.
  unfold environment_lookup_formula,environment_lookup.
  match goal with |- _ <-> ?rhs =>
    change (((holds M rho (Peano.sless i n) /\ holds M rho (beta_formula b c i v)) \/
      (~holds M rho (Peano.sless i n) /\ evalM M rho v = zeroM M)) <-> rhs)
  end.
  rewrite holds_sless,beta_formula_correct. reflexivity.
Qed.

Lemma environment_lookup_definable (M : Model) b c n i :
  Definable1 M (fun v => environment_lookup M b c n i v).
Proof.
  exists (environment_lookup_formula $4 $3 $2 $1 $0),
    (i .: n .: c .: b .: fun _ => zeroM M).
  intro v. symmetry. apply environment_lookup_formula_correct.
Qed.

Section Environments.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).

Lemma environment_lt_cases i n : coding_lt M i n \/ ~coding_lt M i n.
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

Theorem environment_lookup_total b c n i :
  exists v, environment_lookup M b c n i v.
Proof.
  destruct (environment_lt_cases i n) as [Hi|Hi].
  - destruct (beta_total M b c i) as [v Hv]. exists v. now left.
  - exists Z. right. auto.
Qed.

Theorem environment_lookup_functional b c n i v w :
  environment_lookup M b c n i v -> environment_lookup M b c n i w -> v=w.
Proof.
  intros [[Hi Hv]|[Hi Hv]] [[Hi' Hw]|[Hi' Hw]]; try contradiction.
  - exact (beta_unique M b c i v w Hv Hw).
  - congruence.
Qed.

Lemma environment_lookup_inside b c n i v : coding_lt M i n ->
  (environment_lookup M b c n i v <-> beta M b c i v).
Proof. intro Hi. unfold environment_lookup. tauto. Qed.

Lemma environment_lookup_outside b c n i v : ~coding_lt M i n ->
  (environment_lookup M b c n i v <-> v=Z).
Proof. intro Hi. unfold environment_lookup. tauto. Qed.

Lemma environment_empty b c i v : environment_lookup M b c Z i v <-> v=Z.
Proof. apply environment_lookup_outside. apply coding_not_lt_zero. Qed.

Definition environment_equivalent (b c n d e m : D) : Prop :=
  forall i v, environment_lookup M b c n i v <-> environment_lookup M d e m i v.

Theorem environment_lookup_extensional b c d e n :
  (forall i v, coding_lt M i n -> (beta M b c i v <-> beta M d e i v)) ->
  environment_equivalent b c n d e n.
Proof.
  intros H i v. destruct (environment_lt_cases i n) as [Hi|Hi].
  - rewrite !environment_lookup_inside by exact Hi. exact (H i v Hi).
  - rewrite !environment_lookup_outside by exact Hi. reflexivity.
Qed.

(** Codes for cons need not be unique. The graph specifies their complete
    extensional behavior, and its output length is uniquely S n. *)
Definition environment_cons (b c n x b' c' n' : D) : Prop :=
  n'=S n /\ environment_lookup M b' c' n' Z x /\
  forall i v, environment_lookup M b c n i v ->
    environment_lookup M b' c' n' (S i) v.

Theorem environment_cons_total b c n x :
  exists b' c' n', environment_cons b c n x b' c' n'.
Proof.
  destruct (beta_concatenate M x x (S Z) b c n) as [b' [c' [Hhead Htail]]].
  exists b',c',(S n). split; [reflexivity|]. split.
  - left. split; [apply coding_zero_lt_succ|].
    apply Hhead; [apply coding_zero_lt_succ|apply beta_singleton].
  - intros i v [[Hi Hv]|[Hi Hv]].
    + left. split; [apply coding_lt_succ_cancel; exact Hi|].
      pose proof (Htail i v Hi Hv) as H.
      rewrite (Arithmetic.add_succ M Z i), (Arithmetic.add_zero M i) in H.
      exact H.
    + right. split; [|exact Hv].
      intro H. apply Hi. apply (proj1 (coding_lt_succ_cancel M i n)). exact H.
Qed.

Theorem environment_cons_head b c n x b' c' n' v :
  environment_cons b c n x b' c' n' ->
  (environment_lookup M b' c' n' Z v <-> v=x).
Proof.
  intros [_ [Hx _]]. split.
  - intro Hv. eapply environment_lookup_functional; eassumption.
  - intro H. now subst v.
Qed.

Theorem environment_cons_tail b c n x b' c' n' i v :
  environment_cons b c n x b' c' n' ->
  (environment_lookup M b' c' n' (S i) v <-> environment_lookup M b c n i v).
Proof.
  intros [_ [_ Htail]]. split; [|apply Htail].
  intro Hv. destruct (environment_lookup_total b c n i) as [w Hw].
  assert (v=w).
  { eapply environment_lookup_functional; [exact Hv|apply Htail; exact Hw]. }
  now subst v.
Qed.

Theorem environment_cons_extensional b c n d e m x b' c' n' d' e' m' :
  environment_equivalent b c n d e m ->
  environment_cons b c n x b' c' n' -> environment_cons d e m x d' e' m' ->
  environment_equivalent b' c' n' d' e' m'.
Proof.
  intros Heq Hc Hd i v.
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [Hi|[j Hi]]; subst i.
  - rewrite (environment_cons_head b c n x b' c' n' v Hc),
      (environment_cons_head d e m x d' e' m' v Hd). reflexivity.
  - rewrite (environment_cons_tail b c n x b' c' n' j v Hc),
      (environment_cons_tail d e m x d' e' m' j v Hd). apply Heq.
Qed.

End Environments.

Definition environment_lift2 (t : term) : term := t`[↑]`[↑].

Lemma environment_eval_lift2 (M : Model) rho x y t :
  evalM M (y .: x .: rho) (environment_lift2 t) = evalM M rho t.
Proof. unfold evalM,environment_lift2. now rewrite !eval_up. Qed.

Definition environment_cons_formula (b c n x b' c' n' : term) : form :=
  (n' == σ n) ∧ (environment_lookup_formula b' c' n' zero x ∧
    ∀∀ (environment_lookup_formula (environment_lift2 b) (environment_lift2 c)
      (environment_lift2 n) $1 $0 →
      environment_lookup_formula (environment_lift2 b') (environment_lift2 c')
      (environment_lift2 n') (σ $1) $0)).

Theorem environment_cons_formula_correct (M : Model) rho b c n x b' c' n' :
  holds M rho (environment_cons_formula b c n x b' c' n') <->
  environment_cons M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho x) (evalM M rho b') (evalM M rho c') (evalM M rho n').
Proof.
  unfold environment_cons_formula,environment_cons.
  match goal with |- _ <-> ?rhs =>
  change ((evalM M rho n'=succM M (evalM M rho n) /\
    holds M rho (environment_lookup_formula b' c' n' zero x) /\
    (forall i v,
      holds M (v .: i .: rho) (environment_lookup_formula (environment_lift2 b)
        (environment_lift2 c) (environment_lift2 n) $1 $0) ->
      holds M (v .: i .: rho) (environment_lookup_formula (environment_lift2 b')
        (environment_lift2 c') (environment_lift2 n') (σ $1) $0))) <-> rhs)
  end.
  rewrite environment_lookup_formula_correct.
  setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.

(** Closed arity presentations. Slots are the listed arguments in reverse
    order, as usual for successive existential quantifiers. *)
Definition environment_lookup5 : form := environment_lookup_formula $4 $3 $2 $1 $0.
Definition environment_cons7 : form := environment_cons_formula $6 $5 $4 $3 $2 $1 $0.

Theorem environment_cons7_correct (M : Model) rho b c n x b' c' n' :
  holds M (n' .: c' .: b' .: x .: n .: c .: b .: rho) environment_cons7 <->
  environment_cons M b c n x b' c' n'.
Proof. apply environment_cons_formula_correct. Qed.
