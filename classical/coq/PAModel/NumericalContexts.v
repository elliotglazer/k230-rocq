(** Exact-length source formula contexts. The value zero is an ordinary
    member when present at a valid index; zero padding is never membership. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  NumericalProofs NumericalEnvironments SourceBounded SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_member M b c n f :=
  exists i, coding_lt M i n /\ beta M b c i f.

Definition context_lift (t : term) : term := t`[↑].
Lemma context_eval_lift M rho x t :
  evalM M (x .: rho) (context_lift t) = evalM M rho t.
Proof. unfold evalM,context_lift. now rewrite eval_up. Qed.

Definition context_member_formula (b c n f : term) : form :=
  ∃ (Peano.sless $0 (context_lift n) ∧
     beta_formula (context_lift b) (context_lift c) $0 (context_lift f)).

Local Opaque holds beta_formula.
Theorem context_member_formula_correct M rho b c n f :
  holds M rho (context_member_formula b c n f) <->
  context_member M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold context_member_formula,context_member. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite holds_sless.
  setoid_rewrite beta_formula_correct. setoid_rewrite context_eval_lift. reflexivity.
Qed.

Theorem context_empty M b c f : ~context_member M b c (zeroM M) f.
Proof. intros [i [Hi _]]. exact (coding_not_lt_zero M i Hi). Qed.

Lemma context_member_lookup M b c n f :
  context_member M b c n f <->
  exists i, coding_lt M i n /\ environment_lookup M b c n i f.
Proof.
  split; intros [i [Hi Hf]]; exists i; split; [exact Hi| |exact Hi|].
  - apply (proj2 (environment_lookup_inside M b c n i f Hi)). exact Hf.
  - apply (proj1 (environment_lookup_inside M b c n i f Hi)). exact Hf.
Qed.

Theorem context_member_cons M b c n head d e m f :
  environment_cons M b c n head d e m ->
  (context_member M d e m f <-> f=head \/ context_member M b c n f).
Proof.
  intro Hcons. pose proof (proj1 Hcons) as Hlength.
  rewrite !context_member_lookup. split.
  - intros [i [Hi Hf]].
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) i) as [E|[j E]]; subst i.
    + left. exact (proj1 (environment_cons_head M b c n head d e m f Hcons) Hf).
    + right. exists j. split.
      * rewrite Hlength in Hi. exact (proj1 (coding_lt_succ_cancel M j n) Hi).
      * exact (proj1 (environment_cons_tail M b c n head d e m j f Hcons) Hf).
  - intros [E|[i [Hi Hf]]].
    + subst f. exists (zeroM M). split.
      * rewrite Hlength. apply coding_zero_lt_succ.
      * exact (proj2 (environment_cons_head M b c n head d e m head Hcons) eq_refl).
    + exists (succM M i). split.
      * rewrite Hlength. exact (proj2 (coding_lt_succ_cancel M i n) Hi).
      * exact (proj2 (environment_cons_tail M b c n head d e m i f Hcons) Hf).
Qed.

Definition context_singleton M head b c n :=
  environment_cons M (zeroM M) (zeroM M) (zeroM M) head b c n.

Theorem context_singleton_total M head : exists b c n, context_singleton M head b c n.
Proof. apply environment_cons_total. Qed.

Theorem context_singleton_member M head b c n f : context_singleton M head b c n ->
  (context_member M b c n f <-> f=head).
Proof.
  intro H. rewrite (context_member_cons M (zeroM M) (zeroM M) (zeroM M) head b c n f H).
  split; [intros [E|Hbad];[exact E|exfalso;exact (context_empty M _ _ _ Hbad)]|now left].
Qed.

Theorem context_singleton_falsity M : exists b c n,
  context_singleton M (zeroM M) b c n /\ context_member M b c n (zeroM M).
Proof.
  destruct (context_singleton_total M (zeroM M)) as [b [c [n H]]].
  exists b,c,n. split; [exact H|].
  apply (proj2 (context_singleton_member M (zeroM M) b c n (zeroM M) H)). reflexivity.
Qed.

Definition context_included M b c n d e m :=
  forall f, context_member M b c n f -> context_member M d e m f.
Definition context_included_formula (b c n d e m : term) : form :=
  ∀ (context_member_formula (context_lift b) (context_lift c) (context_lift n) $0 →
     context_member_formula (context_lift d) (context_lift e) (context_lift m) $0).

Local Opaque context_member_formula source_bounded_accept_formula.
Theorem context_included_formula_correct M rho b c n d e m :
  holds M rho (context_included_formula b c n d e m) <->
  context_included M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m).
Proof.
  unfold context_included_formula,context_included.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite context_eval_lift. reflexivity.
Qed.

Theorem context_included_refl M b c n : context_included M b c n b c n.
Proof. intros f H. exact H. Qed.

Theorem context_included_trans M b c n d e m p q l :
  context_included M b c n d e m -> context_included M d e m p q l ->
  context_included M b c n p q l.
Proof. intros H1 H2 f Hf. exact (H2 f (H1 f Hf)). Qed.

Definition context_bounded M b c n k :=
  forall f, context_member M b c n f -> source_bounded M f k.
Definition context_bounded_formula (b c n k : term) : form :=
  ∀ (context_member_formula (context_lift b) (context_lift c) (context_lift n) $0 →
     source_bounded_accept_formula $0 (context_lift k)).

Theorem context_bounded_formula_correct M rho b c n k :
  holds M rho (context_bounded_formula b c n k) <->
  context_bounded M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho k).
Proof.
  unfold context_bounded_formula,context_bounded.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite context_eval_lift. reflexivity.
Qed.

Theorem context_bounded_empty M b c k : context_bounded M b c (zeroM M) k.
Proof. intros f H. exfalso. exact (context_empty M b c f H). Qed.

Theorem context_bounded_cons M b c n head d e m k :
  environment_cons M b c n head d e m ->
  (context_bounded M d e m k <->
   source_bounded M head k /\ context_bounded M b c n k).
Proof.
  intro Hcons. split.
  - intro H. split.
    + apply H. apply (proj2 (context_member_cons M b c n head d e m head Hcons)). now left.
    + intros f Hf. apply H. apply (proj2 (context_member_cons M b c n head d e m f Hcons)). now right.
  - intros [Hhead Htail] f Hf.
    apply (proj1 (context_member_cons M b c n head d e m f Hcons)) in Hf.
    destruct Hf as [E|Hf]; [now subst f|exact (Htail f Hf)].
Qed.

Theorem context_bounded_included M b c n d e m k :
  context_included M b c n d e m -> context_bounded M d e m k -> context_bounded M b c n k.
Proof. intros Hinc Hb f Hf. exact (Hb f (Hinc f Hf)). Qed.

Theorem context_member_formula_bound : bounded 4 (context_member_formula $0 $1 $2 $3).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem context_included_formula_bound : bounded 6 (context_included_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem context_bounded_formula_bound : bounded 4 (context_bounded_formula $0 $1 $2 $3).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
