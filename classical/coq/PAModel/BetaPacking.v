(** Uniform packing for arithmetic-formula-defined bounded relations, and
    concatenation of existing internal beta sequences. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Packing.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Add Ring packing_model_ring : (model_semiring M).

Theorem beta_pack_formula rho theta n bound :
  (forall i, coding_lt M i n -> exists r, holds M (r .: i .: rho) theta) ->
  (forall i r, coding_lt M i n -> holds M (r .: i .: rho) theta ->
    coding_lt M r (S bound)) ->
  exists b c, forall i, coding_lt M i n ->
    exists r, holds M (r .: i .: rho) theta /\ beta M b c i r.
Proof.
  intros Htotal Hbound.
  destruct (scaled_common_multiple M n bound) as [c [Hcm Hc]].
  assert (Hunits : forall i j, coding_lt M i j -> coding_lt M j n ->
    unit_modulo M (beta_modulus M c i) (beta_modulus M c j)).
  { intros i j Hij Hjn. apply (beta_units_from_common_multiple M n c Hcm i j Hij).
    apply coding_lt_succ_cases. left. exact Hjn. }
  destruct (crt_for_formula M rho theta c n Htotal Hunits) as [b Hb].
  exists b,c. intros i Hi. destruct (Hb i Hi) as [r [Hr Hbr]].
  exists r. split; [exact Hr|].
  apply congruent_remainder; [apply coding_zero_lt_succ| |exact Hbr].
  apply (coding_lt_trans M r c (beta_modulus M c i)); [|apply modulus_above_scale].
  apply (coding_le_lt_trans M r bound c); [apply (Hbound i r Hi Hr)|exact Hc].
Qed.

Theorem beta_pack_function rho theta n bound :
  (forall i, coding_lt M i n -> exists r, holds M (r .: i .: rho) theta) ->
  (forall i r, coding_lt M i n -> holds M (r .: i .: rho) theta ->
    coding_lt M r (S bound)) ->
  (forall i r s, coding_lt M i n ->
    holds M (r .: i .: rho) theta -> holds M (s .: i .: rho) theta -> r=s) ->
  exists b c, forall i r, coding_lt M i n ->
    (beta M b c i r <-> holds M (r .: i .: rho) theta).
Proof.
  intros Htotal Hbound Hunique.
  destruct (beta_pack_formula rho theta n bound Htotal Hbound) as [b [c Hbc]].
  exists b,c. intros i r Hi. destruct (Hbc i Hi) as [s [Hs Hbs]]. split.
  - intro Hr. assert (r=s) by (eapply beta_unique; eassumption). now subst r.
  - intro Hr. assert (r=s) by (apply (Hunique i r s Hi Hr Hs)). now subst r.
Qed.

Definition concat_relation (b c l d e i r : D) : Prop :=
  (coding_lt M i l /\ beta M b c i r) \/
  (~coding_lt M i l /\ exists j, i = l + j /\ beta M d e j r).

(** After the result/index slots, parameters are l,b,c,d,e. *)
Definition concat_relation_formula : form :=
  (Peano.sless $1 $2 ∧ beta_formula $3 $4 $1 $0) ∨
  ((Peano.sless $1 $2 → ⊥) ∧
    ∃ ($2 == ($3 ⊕ $0) ∧ beta_formula $6 $7 $0 $1)).

Lemma concat_relation_correct rho l b c d e i r :
  holds M (r .: i .: l .: b .: c .: d .: e .: rho) concat_relation_formula <->
  concat_relation b c l d e i r.
Proof.
  unfold concat_relation_formula,concat_relation.
  change (((holds M (r .: i .: l .: b .: c .: d .: e .: rho) (Peano.sless $1 $2) /\
    holds M (r .: i .: l .: b .: c .: d .: e .: rho) (beta_formula $3 $4 $1 $0)) \/
    ((~holds M (r .: i .: l .: b .: c .: d .: e .: rho) (Peano.sless $1 $2)) /\
    exists j, i = l + j /\ holds M (j .: r .: i .: l .: b .: c .: d .: e .: rho)
      (beta_formula $6 $7 $0 $1))) <->
    ((coding_lt M i l /\ beta M b c i r) \/
      (~coding_lt M i l /\ exists j, i = l + j /\ beta M d e j r))).
  rewrite holds_sless,beta_formula_correct.
  split.
  - intros [H|[Hne [j [Hj Hr]]]]; [now left|].
    right. split; [exact Hne|]. exists j. split; [exact Hj|].
    apply beta_formula_correct in Hr. exact Hr.
  - intros [H|[Hne [j [Hj Hr]]]]; [now left|].
    right. split; [exact Hne|]. exists j. split; [exact Hj|].
    apply beta_formula_correct. exact Hr.
Qed.

Lemma coding_difference i l : ~coding_lt M i l -> exists j, i = l + j.
Proof.
  intro Hne.
  destruct (@Peano.trichotomy D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i l) as [Hlt|[Heq|[j Hj]]].
  - contradiction.
  - exists Z. rewrite Heq. ring.
  - change (i = S (l+j)) in Hj. exists (S j). rewrite Hj.
    rewrite (succ_as_add M (l+j)),(succ_as_add M j). ring.
Qed.

Lemma concat_relation_total b c l d e i : exists r, concat_relation b c l d e i r.
Proof.
  destruct (@Peano.trichotomy D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i l) as [Hlt|[Heq|Hgt]].
  - destruct (beta_total M b c i) as [r Hr]. exists r. left. auto.
  - destruct (beta_total M d e Z) as [r Hr]. exists r. right. split.
    + intro H. exact (@Peano.lt_neq D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i l H Heq).
    + exists Z. split; [rewrite Heq;ring|exact Hr].
  - assert (Hne : ~coding_lt M i l).
    { intro H. pose proof (coding_lt_trans M i l i H Hgt) as Hii.
      exact (@Peano.lt_neq D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i i Hii eq_refl). }
    destruct (coding_difference i l Hne) as [j Hj].
    destruct (beta_total M d e j) as [r Hr]. exists r. right.
    split; [exact Hne|]. exists j. auto.
Qed.

Lemma concat_relation_bound b c l d e i r :
  concat_relation b c l d e i r -> coding_lt M r (S (b+d)).
Proof.
  intros [[_ Hr]|[_ [j [_ Hr]]]].
  - apply (coding_le_lt_trans M r b (S (b+d))); [|apply coding_le_add].
    apply (remainder_le_dividend M b (beta_modulus M c i) r Hr).
  - apply (coding_le_lt_trans M r d (S (b+d))).
    + apply (remainder_le_dividend M d (beta_modulus M e j) r Hr).
    + replace (b+d) with (d+b) by ring. apply coding_le_add.
Qed.

Lemma concat_relation_unique b c l d e i r s :
  concat_relation b c l d e i r -> concat_relation b c l d e i s -> r=s.
Proof.
  intros [[Hi Hr]|[Hi [j [Hj Hr]]]] [[Ki Hs]|[Ki [k [Hk Hs]]]];
    try contradiction.
  - eapply beta_unique; eassumption.
  - assert (j = k).
    { apply (Arithmetic.add_cancel M j k l).
      replace (j+l) with (l+j) by ring.
      replace (k+l) with (l+k) by ring. now rewrite <- Hj, <- Hk. }
    subst k. eapply beta_unique; eassumption.
Qed.

Lemma coding_not_lt_sum l j : ~coding_lt M (l+j) l.
Proof.
  intros [k Hk].
  assert (E : Z = S (j+k)).
  { apply (Arithmetic.add_cancel M Z (S (j+k)) l).
    rewrite (succ_as_add M (j+k)), (succ_as_add M ((l+j)+k)) in *.
    replace (Z+l) with l by ring.
    replace ((j+k+S Z)+l) with (((l+j)+k)+S Z) by ring. exact Hk. }
  exact (zero_ne_succ M (j+k) E).
Qed.

Lemma coding_lt_add_left l i j : coding_lt M i j -> coding_lt M (l+i) (l+j).
Proof.
  intros [d Hd]. exists d. rewrite Hd.
  rewrite (succ_as_add M (i+d)), (succ_as_add M ((l+i)+d)). ring.
Qed.

Theorem beta_concatenate b c l d e n :
  exists b' c',
    (forall i r, coding_lt M i l -> beta M b c i r -> beta M b' c' i r) /\
    (forall j r, coding_lt M j n -> beta M d e j r -> beta M b' c' (l+j) r).
Proof.
  set (rho := l .: b .: c .: d .: e .: (fun _ => Z)).
  assert (Ht : forall i, coding_lt M i (l+n) ->
    exists r, holds M (r .: i .: rho) concat_relation_formula).
  { intros i _. destruct (concat_relation_total b c l d e i) as [r Hr].
    exists r. unfold rho. apply concat_relation_correct. exact Hr. }
  assert (Hb : forall i r, coding_lt M i (l+n) ->
    holds M (r .: i .: rho) concat_relation_formula -> coding_lt M r (S (b+d))).
  { intros i r _ Hr. unfold rho in Hr. apply concat_relation_correct in Hr.
    eapply concat_relation_bound. exact Hr. }
  assert (Hu : forall i r s, coding_lt M i (l+n) ->
    holds M (r .: i .: rho) concat_relation_formula ->
    holds M (s .: i .: rho) concat_relation_formula -> r=s).
  { intros i r s _ Hr Hs. unfold rho in Hr,Hs.
    apply concat_relation_correct in Hr,Hs. eapply concat_relation_unique; eassumption. }
  destruct (beta_pack_function rho concat_relation_formula (l+n) (b+d) Ht Hb Hu)
    as [b' [c' Hbc]].
  exists b',c'. split.
  - intros i r Hi Hr.
    assert (Hil : coding_lt M i (l+n)).
    { apply (@Peano.lt_le_trans D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i (l+n) l Hi).
      exists n. reflexivity. }
    apply (proj2 (Hbc i r Hil)). unfold rho. apply concat_relation_correct. left. auto.
  - intros j r Hj Hr.
    apply (proj2 (Hbc (l+j) r (coding_lt_add_left l j n Hj))).
    unfold rho. apply concat_relation_correct. right. split.
    + apply coding_not_lt_sum.
    + exists j. auto.
Qed.

End Packing.
