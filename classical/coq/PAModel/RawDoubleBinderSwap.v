(** A packed composition of two named closing maps, and the actual
    swap relating the two orders when their names differ. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions BetaPacking
  NumericalRenamingMaps NumericalRenaming SourceBounded SourceRenamingIdentity
  RawBinderRenaming SourceRenamingDiamond SourceShiftSpecialization SourceSwap.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition raw_double_binder_index M a b i v :=
  (i = b /\ v = zeroM M) \/ (i <> b /\ i = a /\ v = code_numeral M 1) \/
  (i <> b /\ i <> a /\ v = succM M (succM M i)).
Definition raw_double_binder_index_formula (a b i v:term) : form :=
  ((i == b) ∧ (v == zero)) ∨ (((i == b → ⊥) ∧ ((i == a) ∧ (v == num 1))) ∨
    ((i == b → ⊥) ∧ ((i == a → ⊥) ∧ (v == σ (σ i))))).
Lemma raw_double_binder_index_formula_correct M rho a b i v :
  holds M rho (raw_double_binder_index_formula a b i v) <->
  raw_double_binder_index M (evalM M rho a) (evalM M rho b) (evalM M rho i) (evalM M rho v).
Proof. reflexivity. Qed.
Lemma raw_double_binder_index_total M a b i :exists v,raw_double_binder_index M a b i v.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i b) as [->|HN].
  - exists (zeroM M). now left.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i a) as [->|HA].
    + exists (code_numeral M 1). right;left;auto.
    + exists (succM M (succM M i)). right;right;auto.
Qed.
Lemma raw_double_binder_index_functional M a b i v w :
  raw_double_binder_index M a b i v -> raw_double_binder_index M a b i w ->v=w.
Proof.
  unfold raw_double_binder_index. intros [[E F]|[[E [F G]]|[E [F G]]]]
    [[E' F']|[[E' [F' G']]|[E' [F' G']]]];congruence.
Qed.

Theorem raw_double_binder_map_total M a b k :exists p q,
  forall i v,coding_lt M i k ->
    (renaming_lookup M p q k (zeroM M) i v <->raw_double_binder_index M a b i v).
Proof.
  set (rho:=a .: b .: fun _=>zeroM M).
  set (F:=raw_double_binder_index_formula $2 $3 $1 $0).
  assert (HT:forall i,coding_lt M i k ->exists v,holds M (v .: i .: rho) F).
  { intros i _. destruct (raw_double_binder_index_total M a b i) as (v&HV). exists v. exact HV. }
  assert (HB:forall i v,coding_lt M i k ->holds M (v .: i .: rho) F ->
    coding_lt M v (succM M (succM M k))).
  { intros i v HI [[_ ->]|[[_ [_ ->]]|[_ [_ ->]]]].
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_lt_succ_cancel,HI. }
  assert (HU:forall i v w,coding_lt M i k ->holds M (v .: i .: rho) F ->
    holds M (w .: i .: rho) F ->v=w).
  { intros i v w _ HV HW. exact (raw_double_binder_index_functional M a b i v w HV HW). }
  destruct (beta_pack_function M rho F k (succM M k) HT HB HU) as (p&q&HP).
  exists p,q. intros i v HI. rewrite (renaming_lookup_inside M p q k (zeroM M) i v HI).
  exact (HP i v HI).
Qed.

Lemma raw_double_binder_action M a b bb bc ab ac lb lc ln i j v :
  raw_binder_renaming M b bb bc -> raw_binder_renaming M a ab ac ->
  renaming_lift M ab ac (succM M a) (succM M (zeroM M)) lb lc ln ->
  renaming_lookup M bb bc (succM M b) (succM M (zeroM M)) i j ->
  renaming_lookup M lb lc ln (succM M (zeroM M)) j v ->raw_double_binder_index M a b i v.
Proof.
  intros HB HA HL HJ HV. apply (proj1 (HB i j)) in HJ.
  destruct HJ as [[E ->]|[NE ->]].
  - apply (proj1 (renaming_lift_head M ab ac _ _ lb lc ln v HL)) in HV. now left.
  - destruct (renaming_lift_tail_inv M ab ac _ _ lb lc ln i v HL HV) as (w&HW&EV).
    apply (proj1 (HA i w)) in HW. destruct HW as [[E ->]|[NA ->]].
    + right;left. auto.
    + right;right. auto.
Qed.

Lemma raw_double_binder_swap_values M a b i l m p q :
  a<>b -> source_swap_map M p q -> raw_double_binder_index M a b i l ->
  raw_double_binder_index M b a i m ->
  renaming_lookup M p q (code_numeral M 2) (zeroM M) l m.
Proof.
  intros HNE [H0 H1]. unfold raw_double_binder_index.
  intros [[E ->]|[[NE [E ->]]|[NB [NA ->]]]]
    [[E' ->]|[[NE' [E' ->]]|[NA' [NB' ->]]]];try contradiction;try congruence;
    try exact H0;try exact H1;apply source_swap_tail.
Qed.

Theorem raw_double_binder_swap M a b f k fa fb fab fba
    ab ac bb bc la lc ln lb ld lm p q :
  a<>b ->source_bounded M f k ->raw_binder_renaming M a ab ac ->raw_binder_renaming M b bb bc ->
  renaming_lift M ab ac (succM M a) (succM M (zeroM M)) la lc ln ->
  renaming_lift M bb bc (succM M b) (succM M (zeroM M)) lb ld lm ->
  numerical_renaming M f ab ac (succM M a) (succM M (zeroM M)) fa ->
  numerical_renaming M f bb bc (succM M b) (succM M (zeroM M)) fb ->
  numerical_renaming M fb la lc ln (succM M (zeroM M)) fab ->
  numerical_renaming M fa lb ld lm (succM M (zeroM M)) fba ->
  source_swap_map M p q -> numerical_renaming M fab p q (code_numeral M 2) (zeroM M) fba.
Proof.
  intros HNE HF HA HB HLA HLB HFA HFB HFAB HFBA HSwap.
  destruct (raw_double_binder_map_total M a b k) as (cb&cc&HC).
  destruct (numerical_renaming_total M f cb cc k (zeroM M)) as (fc&HFC).
  assert (HI:numerical_renaming M f (zeroM M) (zeroM M) (zeroM M) (zeroM M) f).
  { apply (numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
    intros i _. apply source_empty_renaming_lookup. }
  assert (HLeft:numerical_renaming M fb la lc ln (succM M (zeroM M)) fc).
  { apply (numerical_source_renaming_diamond M f k
      (zeroM M) (zeroM M) (zeroM M) (zeroM M) bb bc (succM M b) (succM M (zeroM M))
      cb cc k (zeroM M) la lc ln (succM M (zeroM M)) f fb fc HF HI HFB HFC).
    intros i j l m HIb HId HM HL.
    assert (EJ:j=i) by (eapply renaming_lookup_functional;[exact HId|apply source_empty_renaming_lookup]).
    subst j. apply (proj1 (HC i m HIb)) in HM.
    destruct (renaming_lookup_total M la lc ln (succM M (zeroM M)) l) as (v&HV).
    pose proof (raw_double_binder_action M a b bb bc ab ac la lc ln i l v HB HA HLA HL HV) as HD.
    assert (EV:v=m) by exact (raw_double_binder_index_functional M a b i v m HD HM).
    now subst v. }
  assert (EC:fc=fab) by exact (numerical_renaming_functional M fb la lc ln _ fc fab HLeft HFAB).
  subst fc.
  apply (numerical_source_renaming_diamond M f k
    ab ac (succM M a) (succM M (zeroM M)) cb cc k (zeroM M)
    lb ld lm (succM M (zeroM M)) p q (code_numeral M 2) (zeroM M)
    fa fab fba HF HFA HFC HFBA).
  intros i j l m HIb HIA HJM HIL.
  apply (raw_double_binder_swap_values M a b i l m p q HNE HSwap).
  - exact (proj1 (HC i l HIb) HIL).
  - exact (raw_double_binder_action M b a ab ac bb bc lb ld lm i j m HA HB HLB HIA HJM).
Qed.

Print Assumptions raw_double_binder_map_total.
Print Assumptions raw_double_binder_swap.
