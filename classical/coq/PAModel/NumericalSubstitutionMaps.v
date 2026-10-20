(** Internal finite-prefix substitutions with a separate tail base.
    Beyond length n, index n+j maps to base+j. Binder lifting changes the
    prefix to 0,S(old entries), length to S n and tail base to S base.
    Neither prefix lengths nor indices are restricted to standard numerals. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension BetaPacking NumericalEnvironments NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition substitution_lookup M b c n base i v :=
  (coding_lt M i n /\ beta M b c i v) \/
  (~coding_lt M i n /\ exists j, i = addM M n j /\ v=addM M base j).
Definition substitution_lookup_formula (b c n base i v : term) : form :=
  (Peano.sless i n ∧ beta_formula b c i v) ∨
  ((Peano.sless i n → ⊥) ∧
   ∃ (i`[↑] == (n`[↑] ⊕ $0) ∧ v`[↑] == (base`[↑] ⊕ $0))).
Lemma substitution_holds_eq M rho (a b : term) :
  holds M rho (a == b) <-> evalM M rho a = evalM M rho b.
Proof. reflexivity. Qed.
Lemma substitution_holds_false M rho : holds M rho ⊥ <-> False.
Proof. reflexivity. Qed.
Lemma substitution_eval_add M rho (a b : term) :
  evalM M rho (a ⊕ b) = addM M (evalM M rho a) (evalM M rho b).
Proof. reflexivity. Qed.
Lemma substitution_map_eval_succ M rho (a : term) :
  evalM M rho (σ a) = succM M (evalM M rho a).
Proof. reflexivity. Qed.
Lemma substitution_eval_up M rho x (a : term) :
  evalM M (x .: rho) a`[↑] = evalM M rho a.
Proof. unfold evalM. apply eval_up. Qed.
Local Opaque holds beta_formula evalM.
Lemma substitution_lookup_formula_correct M rho b c n base i v :
  holds M rho (substitution_lookup_formula b c n base i v) <->
  substitution_lookup M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho base) (evalM M rho i) (evalM M rho v).
Proof.
  unfold substitution_lookup_formula,substitution_lookup.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  setoid_rewrite holds_imp. setoid_rewrite holds_sless.
  setoid_rewrite beta_formula_correct. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite substitution_holds_eq.
  setoid_rewrite substitution_holds_false. setoid_rewrite substitution_eval_add.
  setoid_rewrite substitution_eval_up. reflexivity.
Qed.

Local Transparent evalM.
Section Maps.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).

Lemma substitution_tail_total n i : ~coding_lt M i n -> exists j, i = addM M n j.
Proof.
  intro Hni. destruct (@Peano.trichotomy D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i n) as [Hlt|[E|[j E]]].
  - contradiction.
  - exists Z. now rewrite coding_add_zero_r.
  - exists (S j). rewrite (coding_add_comm M n (S j)), Arithmetic.add_succ,
      (coding_add_comm M j n). exact E.
Qed.
Lemma substitution_lookup_total b c n base i : exists v, substitution_lookup M b c n base i v.
Proof.
  destruct (environment_lt_cases M i n) as [Hi|Hi].
  - destruct (beta_total M b c i) as [v Hv]. exists v. left. auto.
  - destruct (substitution_tail_total n i Hi) as [j Hj].
    exists (addM M base j). right. split; [exact Hi|]. exists j. auto.
Qed.
Lemma substitution_lookup_functional b c n base i v w :
  substitution_lookup M b c n base i v -> substitution_lookup M b c n base i w -> v=w.
Proof.
  intros [[Hi Hv]|[Hi [j [Hij Hv]]]] [[Hk Hw]|[Hk [l [Hil Hw]]]]; try contradiction.
  - exact (beta_unique M b c i v w Hv Hw).
  - assert (j=l).
    { apply (add_cancel M j l n). rewrite !(coding_add_comm M _ n). congruence. }
    congruence.
Qed.
Lemma substitution_lookup_inside b c n base i v : coding_lt M i n ->
  (substitution_lookup M b c n base i v <-> beta M b c i v).
Proof. intro Hi. unfold substitution_lookup. tauto. Qed.
Lemma substitution_lookup_outside b c n base i v : ~coding_lt M i n ->
  (substitution_lookup M b c n base i v <-> exists j, i = addM M n j /\ v=addM M base j).
Proof. intro Hi. unfold substitution_lookup. tauto. Qed.

Definition substitution_equivalent (b c n d e m base : D) :=
  forall i v, substitution_lookup M b c n base i v <-> substitution_lookup M d e m base i v.
Lemma substitution_equivalent_refl b c n base : substitution_equivalent b c n b c n base.
Proof. intros i v. reflexivity. Qed.
Lemma substitution_equivalent_lookup_determinacy b c n d e m base i v w :
  substitution_equivalent b c n d e m base -> substitution_lookup M b c n base i v ->
  substitution_lookup M d e m base i w -> v=w.
Proof.
  intros H Hv Hw. apply (substitution_lookup_functional d e m base i v w); [|exact Hw].
  now apply H.
Qed.

Definition substitution_lift (b c n base d e m : D) :=
  m=S n /\ substitution_lookup M d e m (S base) Z Z /\
  forall i v, substitution_lookup M b c n base i v ->
    substitution_lookup M d e m (S base) (S i) (S v).

Local Opaque holds beta_formula.
Definition substitution_beta_succ_formula : form := ∃ (beta_formula $4 $3 $2 $0 ∧ $1 == σ $0).
Lemma substitution_beta_succ_formula_correct rho b c i r :
  holds M (r .: i .: c .: b .: rho) substitution_beta_succ_formula <->
  exists v, beta M b c i v /\ r=S v.
Proof.
  unfold substitution_beta_succ_formula. setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite beta_formula_correct. reflexivity.
Qed.

Lemma substitution_beta_map_succ b c n : exists d e, forall i r, coding_lt M i n ->
  (beta M d e i r <-> exists v, beta M b c i v /\ r=S v).
Proof.
  set (rho := c .: b .: fun _ => Z).
  assert (Ht : forall i, coding_lt M i n -> exists r, holds M (r .: i .: rho) substitution_beta_succ_formula).
  { intros i _. destruct (beta_total M b c i) as [v Hv]. exists (S v).
    unfold rho. apply substitution_beta_succ_formula_correct. exists v. auto. }
  assert (Hb : forall i r, coding_lt M i n -> holds M (r .: i .: rho) substitution_beta_succ_formula ->
    coding_lt M r (S (S b))).
  { intros i r _ Hr. unfold rho in Hr. apply substitution_beta_succ_formula_correct in Hr.
    destruct Hr as [v [Hv E]]. subst r. apply coding_lt_succ_cancel.
    exact (remainder_le_dividend M b (beta_modulus M c i) v Hv). }
  assert (Hu : forall i r s, coding_lt M i n ->
    holds M (r .: i .: rho) substitution_beta_succ_formula -> holds M (s .: i .: rho) substitution_beta_succ_formula -> r=s).
  { intros i r s _ Hr Hs. unfold rho in Hr,Hs.
    apply substitution_beta_succ_formula_correct in Hr,Hs.
    destruct Hr as [v [Hv Er]], Hs as [w [Hw Es]].
    assert (v=w) by (eapply beta_unique; eassumption). congruence. }
  destruct (beta_pack_function M rho substitution_beta_succ_formula n (S b) Ht Hb Hu) as [d [e Hde]].
  exists d,e. intros i r Hi. rewrite (Hde i r Hi). unfold rho.
  apply substitution_beta_succ_formula_correct.
Qed.

Theorem substitution_lift_total b c n base : exists d e m, substitution_lift b c n base d e m.
Proof.
  destruct (substitution_beta_map_succ b c n) as [d [e Hde]].
  destruct (environment_cons_total M d e n Z) as [b' [c' [n' Hcons]]].
  destruct Hcons as [En [Hhead Htail]]. subst n'.
  exists b',c',(S n). split; [reflexivity|]. split.
  - apply substitution_lookup_inside; [apply coding_zero_lt_succ|].
    apply (proj1 (environment_lookup_inside M b' c' (S n) Z Z (coding_zero_lt_succ M n))). exact Hhead.
  - intros i v [[Hi Hv]|[Hi [j [Hij Hv]]]].
    + apply substitution_lookup_inside; [apply coding_lt_succ_cancel;exact Hi|].
      apply (proj1 (environment_lookup_inside M b' c' (S n) (S i) (S v)
        (proj2 (coding_lt_succ_cancel M i n) Hi))).
      apply Htail. apply environment_lookup_inside; [exact Hi|].
      apply Hde; [exact Hi|]. exists v. auto.
    + apply substitution_lookup_outside.
      * intro H. apply Hi. exact (proj1 (coding_lt_succ_cancel M i n) H).
      * exists j. split; rewrite Arithmetic.add_succ; congruence.
Qed.

Lemma substitution_lift_head b c n base d e m v : substitution_lift b c n base d e m ->
  (substitution_lookup M d e m (S base) Z v <-> v=Z).
Proof.
  intros [_ [Hz _]]. split.
  - intro Hv. exact (substitution_lookup_functional d e m (S base) Z v Z Hv Hz).
  - intro E. now subst v.
Qed.
Lemma substitution_lift_tail b c n base d e m i v : substitution_lift b c n base d e m ->
  (substitution_lookup M d e m (S base) (S i) (S v) <-> substitution_lookup M b c n base i v).
Proof.
  intros [_ [_ Ht]]. split; [|apply Ht]. intro Hv.
  destruct (substitution_lookup_total b c n base i) as [w Hw].
  assert (S v=S w) by (eapply substitution_lookup_functional; [exact Hv|apply Ht;exact Hw]).
  apply succ_injective in H. now subst w.
Qed.
Lemma substitution_lift_tail_inv b c n base d e m i v : substitution_lift b c n base d e m ->
  substitution_lookup M d e m (S base) (S i) v ->
  exists w, substitution_lookup M b c n base i w /\ v=S w.
Proof.
  intros [_ [_ Ht]] Hv. destruct (substitution_lookup_total b c n base i) as [w Hw].
  exists w. split; [exact Hw|]. eapply substitution_lookup_functional; [exact Hv|apply Ht;exact Hw].
Qed.
Theorem substitution_lift_extensional b c n d e m base b' c' n' d' e' m' :
  substitution_equivalent b c n d e m base ->
  substitution_lift b c n base b' c' n' -> substitution_lift d e m base d' e' m' ->
  substitution_equivalent b' c' n' d' e' m' (S base).
Proof.
  intros Heq Hb Hd i v.
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]]; subst i.
  - rewrite (substitution_lift_head b c n base b' c' n' v Hb),
      (substitution_lift_head d e m base d' e' m' v Hd). reflexivity.
  - split; intro Hv.
    + destruct (substitution_lift_tail_inv b c n base b' c' n' j v Hb Hv) as [w [Hw E]].
      subst v. apply (proj2 (substitution_lift_tail d e m base d' e' m' j w Hd)). now apply Heq.
    + destruct (substitution_lift_tail_inv d e m base d' e' m' j v Hd Hv) as [w [Hw E]].
      subst v. apply (proj2 (substitution_lift_tail b c n base b' c' n' j w Hb)). now apply Heq.
Qed.
End Maps.

Theorem substitution_lift_functional M b c n base d e m d' e' m' :
  substitution_lift M b c n base d e m ->
  substitution_lift M b c n base d' e' m' ->
  substitution_equivalent M d e m d' e' m' (succM M base).
Proof.
  apply (substitution_lift_extensional M b c n b c n base d e m d' e' m').
  apply substitution_equivalent_refl.
Qed.

(** A one-entry prefix with base zero is actual binder substitution:
    index zero maps to t, and every successor index S i maps to i. *)
Theorem substitution_singleton_total M t : exists b c,
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t /\
  forall i, substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (succM M i) i.
Proof.
  destruct (environment_cons_total M (zeroM M) (zeroM M) (zeroM M) t)
    as [b [c [n [En [Hhead Htail]]]]]. subst n.
  exists b,c. split.
  - apply substitution_lookup_inside; [apply coding_zero_lt_succ|].
    apply (proj1 (environment_lookup_inside M b c (succM M (zeroM M))
      (zeroM M) t (coding_zero_lt_succ M (zeroM M)))). exact Hhead.
  - intro i. apply substitution_lookup_outside.
    + intro H. apply (coding_not_lt_zero M i).
      exact (proj1 (coding_lt_succ_cancel M i (zeroM M)) H).
    + exists i. split; now rewrite ?Arithmetic.add_succ, coding_add_zero.
Qed.

Local Opaque holds substitution_lookup_formula.
Definition substitution_lift_formula (b c n base d e m : term) : form :=
  (m == σ n) ∧ (substitution_lookup_formula d e m (σ base) zero zero ∧
  ∀∀ (substitution_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 base) $1 $0 →
    substitution_lookup_formula (environment_lift2 d) (environment_lift2 e)
      (environment_lift2 m) (σ (environment_lift2 base)) (σ $1) (σ $0))).
Lemma substitution_lift_formula_correct M rho b c n base d e m :
  holds M rho (substitution_lift_formula b c n base d e m) <->
  substitution_lift M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho base) (evalM M rho d) (evalM M rho e) (evalM M rho m).
Proof.
  unfold substitution_lift_formula,substitution_lift.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_all.
  setoid_rewrite holds_imp. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite substitution_holds_eq. setoid_rewrite substitution_map_eval_succ.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.
Definition substitution_equivalent_formula (b c n d e m base : term) : form :=
  ∀∀ ((substitution_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 base) $1 $0 →
    substitution_lookup_formula (environment_lift2 d) (environment_lift2 e)
    (environment_lift2 m) (environment_lift2 base) $1 $0) ∧
    (substitution_lookup_formula (environment_lift2 d) (environment_lift2 e)
    (environment_lift2 m) (environment_lift2 base) $1 $0 →
    substitution_lookup_formula (environment_lift2 b) (environment_lift2 c)
    (environment_lift2 n) (environment_lift2 base) $1 $0)).
Lemma substitution_equivalent_formula_correct M rho b c n d e m base :
  holds M rho (substitution_equivalent_formula b c n d e m base) <->
  substitution_equivalent M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho base).
Proof.
  unfold substitution_equivalent_formula,substitution_equivalent.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_and. setoid_rewrite holds_imp.
  setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.
