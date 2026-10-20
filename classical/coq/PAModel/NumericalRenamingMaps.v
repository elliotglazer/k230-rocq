(** Internal finite-prefix renamings.  After the prefix the map is i+delta.
    Binder lifting preserves delta and changes the prefix to 0,S(old entries).
    Neither prefix lengths nor indices are restricted to standard numerals. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension BetaPacking NumericalEnvironments NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition renaming_lookup M b c n delta i v :=
  (coding_lt M i n /\ beta M b c i v) \/
  (~coding_lt M i n /\ v=addM M i delta).
Definition renaming_lookup_formula (b c n delta i v : term) : form :=
  (Peano.sless i n ∧ beta_formula b c i v) ∨
  ((Peano.sless i n → ⊥) ∧ v == (i ⊕ delta)).
Lemma renaming_lookup_formula_correct M rho b c n delta i v :
  holds M rho (renaming_lookup_formula b c n delta i v) <->
  renaming_lookup M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho delta) (evalM M rho i) (evalM M rho v).
Proof.
  unfold renaming_lookup_formula,renaming_lookup.
  match goal with |- _ <-> ?rhs => change
    (((holds M rho (Peano.sless i n) /\ holds M rho (beta_formula b c i v)) \/
      (~holds M rho (Peano.sless i n) /\ evalM M rho v=addM M (evalM M rho i) (evalM M rho delta))) <-> rhs)
  end. rewrite holds_sless,beta_formula_correct. reflexivity.
Qed.

Section Maps.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).

Lemma renaming_lookup_total b c n delta i : exists v, renaming_lookup M b c n delta i v.
Proof.
  destruct (environment_lt_cases M i n) as [Hi|Hi].
  - destruct (beta_total M b c i) as [v Hv]. exists v. left. auto.
  - exists (addM M i delta). right. auto.
Qed.
Lemma renaming_lookup_functional b c n delta i v w :
  renaming_lookup M b c n delta i v -> renaming_lookup M b c n delta i w -> v=w.
Proof.
  intros [[Hi Hv]|[Hi Hv]] [[Hj Hw]|[Hj Hw]]; try contradiction.
  - exact (beta_unique M b c i v w Hv Hw).
  - congruence.
Qed.
Lemma renaming_lookup_inside b c n delta i v : coding_lt M i n ->
  (renaming_lookup M b c n delta i v <-> beta M b c i v).
Proof. intro Hi. unfold renaming_lookup. tauto. Qed.
Lemma renaming_lookup_outside b c n delta i v : ~coding_lt M i n ->
  (renaming_lookup M b c n delta i v <-> v=addM M i delta).
Proof. intro Hi. unfold renaming_lookup. tauto. Qed.

Definition renaming_equivalent (b c n d e m delta : D) :=
  forall i v, renaming_lookup M b c n delta i v <-> renaming_lookup M d e m delta i v.
Lemma renaming_equivalent_refl b c n delta : renaming_equivalent b c n b c n delta.
Proof. intros i v. reflexivity. Qed.
Lemma renaming_equivalent_lookup_determinacy b c n d e m delta i v w :
  renaming_equivalent b c n d e m delta -> renaming_lookup M b c n delta i v ->
  renaming_lookup M d e m delta i w -> v=w.
Proof.
  intros H Hv Hw. apply (renaming_lookup_functional d e m delta i v w); [|exact Hw].
  now apply H.
Qed.

Definition renaming_lift (b c n delta d e m : D) :=
  m=S n /\ renaming_lookup M d e m delta Z Z /\
  forall i v, renaming_lookup M b c n delta i v ->
    renaming_lookup M d e m delta (S i) (S v).

Local Opaque holds beta_formula.
Definition beta_succ_formula : form := ∃ (beta_formula $4 $3 $2 $0 ∧ $1 == σ $0).
Lemma beta_succ_formula_correct rho b c i r :
  holds M (r .: i .: c .: b .: rho) beta_succ_formula <->
  exists v, beta M b c i v /\ r=S v.
Proof.
  unfold beta_succ_formula. setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. reflexivity.
Qed.

Lemma beta_map_succ b c n : exists d e, forall i r, coding_lt M i n ->
  (beta M d e i r <-> exists v, beta M b c i v /\ r=S v).
Proof.
  set (rho := c .: b .: fun _ => Z).
  assert (Ht : forall i, coding_lt M i n -> exists r, holds M (r .: i .: rho) beta_succ_formula).
  { intros i _. destruct (beta_total M b c i) as [v Hv]. exists (S v).
    unfold rho. apply beta_succ_formula_correct. exists v. auto. }
  assert (Hb : forall i r, coding_lt M i n -> holds M (r .: i .: rho) beta_succ_formula ->
    coding_lt M r (S (S b))).
  { intros i r _ Hr. unfold rho in Hr. apply beta_succ_formula_correct in Hr.
    destruct Hr as [v [Hv E]]. subst r. apply coding_lt_succ_cancel.
    exact (remainder_le_dividend M b (beta_modulus M c i) v Hv). }
  assert (Hu : forall i r s, coding_lt M i n ->
    holds M (r .: i .: rho) beta_succ_formula -> holds M (s .: i .: rho) beta_succ_formula -> r=s).
  { intros i r s _ Hr Hs. unfold rho in Hr,Hs.
    apply beta_succ_formula_correct in Hr,Hs.
    destruct Hr as [v [Hv Er]], Hs as [w [Hw Es]].
    assert (v=w) by (eapply beta_unique; eassumption). congruence. }
  destruct (beta_pack_function M rho beta_succ_formula n (S b) Ht Hb Hu) as [d [e Hde]].
  exists d,e. intros i r Hi. rewrite (Hde i r Hi). unfold rho.
  apply beta_succ_formula_correct.
Qed.

Theorem renaming_lift_total b c n delta : exists d e m, renaming_lift b c n delta d e m.
Proof.
  destruct (beta_map_succ b c n) as [d [e Hde]].
  destruct (environment_cons_total M d e n Z) as [b' [c' [n' Hcons]]].
  destruct Hcons as [En [Hhead Htail]]. subst n'.
  exists b',c',(S n). split; [reflexivity|]. split.
  - apply renaming_lookup_inside; [apply coding_zero_lt_succ|].
    apply (proj1 (environment_lookup_inside M b' c' (S n) Z Z (coding_zero_lt_succ M n))). exact Hhead.
  - intros i v [[Hi Hv]|[Hi Hv]].
    + apply renaming_lookup_inside; [apply coding_lt_succ_cancel;exact Hi|].
      apply (proj1 (environment_lookup_inside M b' c' (S n) (S i) (S v)
        (proj2 (coding_lt_succ_cancel M i n) Hi))).
      apply Htail. apply environment_lookup_inside; [exact Hi|].
      apply Hde; [exact Hi|]. exists v. auto.
    + apply renaming_lookup_outside.
      * intro H. apply Hi. exact (proj1 (coding_lt_succ_cancel M i n) H).
      * rewrite Hv. symmetry. apply Arithmetic.add_succ.
Qed.

Lemma renaming_lift_head b c n delta d e m v : renaming_lift b c n delta d e m ->
  (renaming_lookup M d e m delta Z v <-> v=Z).
Proof.
  intros [_ [Hz _]]. split.
  - intro Hv. exact (renaming_lookup_functional d e m delta Z v Z Hv Hz).
  - intro E. now subst v.
Qed.
Lemma renaming_lift_tail b c n delta d e m i v : renaming_lift b c n delta d e m ->
  (renaming_lookup M d e m delta (S i) (S v) <-> renaming_lookup M b c n delta i v).
Proof.
  intros [_ [_ Ht]]. split; [|apply Ht]. intro Hv.
  destruct (renaming_lookup_total b c n delta i) as [w Hw].
  assert (S v=S w) by (eapply renaming_lookup_functional; [exact Hv|apply Ht;exact Hw]).
  apply succ_injective in H. now subst w.
Qed.
Lemma renaming_lift_tail_inv b c n delta d e m i v : renaming_lift b c n delta d e m ->
  renaming_lookup M d e m delta (S i) v ->
  exists w, renaming_lookup M b c n delta i w /\ v=S w.
Proof.
  intros [_ [_ Ht]] Hv. destruct (renaming_lookup_total b c n delta i) as [w Hw].
  exists w. split; [exact Hw|]. eapply renaming_lookup_functional; [exact Hv|apply Ht;exact Hw].
Qed.
Theorem renaming_lift_extensional b c n d e m delta b' c' n' d' e' m' :
  renaming_equivalent b c n d e m delta ->
  renaming_lift b c n delta b' c' n' -> renaming_lift d e m delta d' e' m' ->
  renaming_equivalent b' c' n' d' e' m' delta.
Proof.
  intros Heq Hb Hd i v.
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]]; subst i.
  - rewrite (renaming_lift_head b c n delta b' c' n' v Hb),
      (renaming_lift_head d e m delta d' e' m' v Hd). reflexivity.
  - split; intro Hv.
    + destruct (renaming_lift_tail_inv b c n delta b' c' n' j v Hb Hv) as [w [Hw E]].
      subst v. apply (proj2 (renaming_lift_tail d e m delta d' e' m' j w Hd)). now apply Heq.
    + destruct (renaming_lift_tail_inv d e m delta d' e' m' j v Hd Hv) as [w [Hw E]].
      subst v. apply (proj2 (renaming_lift_tail b c n delta b' c' n' j w Hb)). now apply Heq.
Qed.
End Maps.

Local Opaque holds renaming_lookup_formula.
Definition renaming_lift_formula (b c n delta d e m : term) : form :=
  (m == σ n) ∧ (renaming_lookup_formula d e m delta zero zero ∧
  ∀∀ (renaming_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 delta) $1 $0 →
    renaming_lookup_formula (environment_lift2 d) (environment_lift2 e)
      (environment_lift2 m) (environment_lift2 delta) (σ $1) (σ $0))).
Lemma renaming_lift_formula_correct M rho b c n delta d e m :
  holds M rho (renaming_lift_formula b c n delta d e m) <->
  renaming_lift M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho delta) (evalM M rho d) (evalM M rho e) (evalM M rho m).
Proof.
  unfold renaming_lift_formula,renaming_lift.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_all.
  setoid_rewrite holds_imp. setoid_rewrite renaming_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.
Definition renaming_equivalent_formula (b c n d e m delta : term) : form :=
  ∀∀ ((renaming_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 delta) $1 $0 →
    renaming_lookup_formula (environment_lift2 d) (environment_lift2 e)
    (environment_lift2 m) (environment_lift2 delta) $1 $0) ∧
    (renaming_lookup_formula (environment_lift2 d) (environment_lift2 e)
    (environment_lift2 m) (environment_lift2 delta) $1 $0 →
    renaming_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 delta) $1 $0)).
Lemma renaming_equivalent_formula_correct M rho b c n d e m delta :
  holds M rho (renaming_equivalent_formula b c n d e m delta) <->
  renaming_equivalent M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho delta).
Proof.
  unfold renaming_equivalent_formula,renaming_equivalent.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_and. setoid_rewrite holds_imp.
  setoid_rewrite renaming_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.
