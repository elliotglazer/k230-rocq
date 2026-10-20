(** The finite-prefix source renaming that closes a named variable x:
    x maps to de Bruijn 0, while every other free index i maps to S i.
    All indices and prefix lengths may be nonstandard PA-model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  BetaPacking NumericalProofs NumericalEnvironments NumericalRenamingMaps
  NumericalRenaming SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition raw_binder_index M x i v :=
  (i = x /\ v = zeroM M) \/ (i <> x /\ v = succM M i).
Definition raw_binder_index_formula (x i v:term) : form :=
  ((i == x) ∧ (v == zero)) ∨ ((i == x → ⊥) ∧ (v == σ i)).

Lemma raw_binder_index_formula_correct M rho x i v :
  holds M rho (raw_binder_index_formula x i v) <->
  raw_binder_index M (evalM M rho x) (evalM M rho i) (evalM M rho v).
Proof. reflexivity. Qed.

Definition raw_binder_renaming M x b c :=
  forall i v, renaming_lookup M b c (succM M x) (succM M (zeroM M)) i v <->
    raw_binder_index M x i v.
Definition raw_binder_renaming_formula (x b c:term) : form :=
  ∀∀ ((renaming_lookup_formula (code_lift2 b) (code_lift2 c)
      (σ (code_lift2 x)) (σ zero) $1 $0 → raw_binder_index_formula (code_lift2 x) $1 $0) ∧
    (raw_binder_index_formula (code_lift2 x) $1 $0 →
      renaming_lookup_formula (code_lift2 b) (code_lift2 c) (σ (code_lift2 x)) (σ zero) $1 $0)).

Lemma raw_binder_eval_succ M rho (a:term) : evalM M rho (σ a) = succM M (evalM M rho a).
Proof. reflexivity. Qed.

Lemma raw_binder_renaming_formula_correct M rho x b c :
  holds M rho (raw_binder_renaming_formula x b c) <->
  raw_binder_renaming M (evalM M rho x) (evalM M rho b) (evalM M rho c).
Proof.
  set (body:=
    (renaming_lookup_formula (code_lift2 b) (code_lift2 c) (σ (code_lift2 x)) (σ zero) $1 $0 →
      raw_binder_index_formula (code_lift2 x) $1 $0) ∧
    (raw_binder_index_formula (code_lift2 x) $1 $0 →
      renaming_lookup_formula (code_lift2 b) (code_lift2 c) (σ (code_lift2 x)) (σ zero) $1 $0)).
  change ((forall i v,holds M (v .: i .: rho) body) <->
    forall i v,renaming_lookup M (evalM M rho b) (evalM M rho c) (succM M (evalM M rho x))
      (succM M (zeroM M)) i v <-> raw_binder_index M (evalM M rho x) i v).
  assert (Hbody:forall i v,holds M (v .: i .: rho) body <->
    (renaming_lookup M (evalM M rho b) (evalM M rho c) (succM M (evalM M rho x))
      (succM M (zeroM M)) i v <-> raw_binder_index M (evalM M rho x) i v)).
  { intros i v. unfold body. rewrite holds_and,!holds_imp,!renaming_lookup_formula_correct,!raw_binder_index_formula_correct.
    rewrite !raw_binder_eval_succ,!code_eval_lift2. reflexivity. }
  split;intros H i v;apply Hbody,H.
Qed.

Lemma raw_binder_index_total M x i : exists v,raw_binder_index M x i v.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i x) as [E|H].
  - exists (zeroM M). left;auto.
  - exists (succM M i). right;auto.
Qed.
Lemma raw_binder_index_functional M x i v w :
  raw_binder_index M x i v -> raw_binder_index M x i w -> v=w.
Proof. unfold raw_binder_index. intros [[H E]|[H E]] [[H' E']|[H' E']];congruence. Qed.

Theorem raw_binder_renaming_total M x : exists b c,raw_binder_renaming M x b c.
Proof.
  set (rho:=x .: fun _=>zeroM M).
  set (F:=raw_binder_index_formula $2 $1 $0).
  assert (HT:forall i,coding_lt M i (succM M x) -> exists v,holds M (v .: i .: rho) F).
  { intros i _. destruct (raw_binder_index_total M x i) as [v Hv]. exists v. exact Hv. }
  assert (HB:forall i v,coding_lt M i (succM M x) -> holds M (v .: i .: rho) F ->
      coding_lt M v (succM M (succM M x))).
  { intros i v Hi [[_ ->]|[_ ->]].
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,Hi. }
  assert (HU:forall i v w,coding_lt M i (succM M x) ->
      holds M (v .: i .: rho) F -> holds M (w .: i .: rho) F -> v=w).
  { intros i v w _ Hv Hw. exact (raw_binder_index_functional M x i v w Hv Hw). }
  destruct (beta_pack_function M rho F (succM M x) (succM M x) HT HB HU) as [b [c Hbc]].
  exists b,c. intros i v. split.
  - intros [[Hi Hv]|[Hi Hv]].
    + exact (proj1 (Hbc i v Hi) Hv).
    + right. split.
      * intro E. subst i. exact (Hi (coding_lt_succ M x)).
      * rewrite <- (succ_as_add M i) in Hv. exact Hv.
  - intro H. destruct (environment_lt_cases M i (succM M x)) as [Hi|Hi].
    + left. split;[exact Hi|exact (proj2 (Hbc i v Hi) H)].
    + right. split;[exact Hi|]. destruct H as [[E _]|[_ E]].
      * subst i. contradiction (Hi (coding_lt_succ M x)).
      * rewrite E. apply succ_as_add.
Qed.

Theorem raw_binder_renaming_equivalent M x b c d e :
  raw_binder_renaming M x b c -> raw_binder_renaming M x d e ->
  renaming_equivalent M b c (succM M x) d e (succM M x) (succM M (zeroM M)).
Proof. intros H1 H2 i v. unfold raw_binder_renaming in H1,H2. rewrite (H1 i v),(H2 i v). reflexivity. Qed.

Theorem raw_binder_lift_head M x b c d e n v :
  raw_binder_renaming M x b c ->
  renaming_lift M b c (succM M x) (succM M (zeroM M)) d e n ->
  (renaming_lookup M d e n (succM M (zeroM M)) (zeroM M) v <-> v = zeroM M).
Proof. intros _ HL. exact (renaming_lift_head M b c (succM M x) (succM M (zeroM M)) d e n v HL). Qed.

Theorem raw_binder_lift_tail M x b c d e n i v :
  raw_binder_renaming M x b c ->
  renaming_lift M b c (succM M x) (succM M (zeroM M)) d e n ->
  (renaming_lookup M d e n (succM M (zeroM M)) (succM M i) v <->
    exists w,raw_binder_index M x i w /\ v = succM M w).
Proof.
  intros HR HL. split.
  - intro H. destruct (renaming_lift_tail_inv M b c (succM M x) (succM M (zeroM M)) d e n i v HL H)
      as [w [Hw E]]. exists w. split;[now apply HR|exact E].
  - intros [w [Hw ->]]. apply (proj2 (renaming_lift_tail M b c (succM M x)
      (succM M (zeroM M)) d e n i w HL)). now apply HR.
Qed.

Theorem raw_named_binder_image_total M x f :
  exists b c renamed result, raw_binder_renaming M x b c /\
    numerical_renaming M f b c (succM M x) (succM M (zeroM M)) renamed /\
    sf_relation M SFAll renamed (zeroM M) result.
Proof.
  destruct (raw_binder_renaming_total M x) as [b [c Hb]].
  destruct (numerical_renaming_total M f b c (succM M x) (succM M (zeroM M))) as [g Hg].
  destruct (sf_relation_total M SFAll g (zeroM M)) as [result HR].
  exists b,c,g,result. auto.
Qed.

Print Assumptions raw_binder_renaming_formula_correct.
Print Assumptions raw_binder_renaming_total.
Print Assumptions raw_binder_lift_tail.
Print Assumptions raw_named_binder_image_total.







