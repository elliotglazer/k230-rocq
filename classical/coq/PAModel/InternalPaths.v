(** Internally finite paths through the tail projection of the exact pair
    graph. No induction over an external natural-number path is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  BetaExtension BetaPacking Pairing NumericalProofs ProofClosure.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Section Paths.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Add Ring path_ring : (model_semiring M).

Lemma beta_slice b c o n :
  exists b' c', forall i v, coding_lt M i n ->
    (beta M b' c' i v <-> beta M b c (o+i) v).
Proof.
  set (rho := b .: c .: o .: (fun _ => O)).
  set (theta := beta_formula $2 $3 ($4 ⊕ $1) $0).
  assert (HC : forall i v,
    holds M (v .: i .: rho) theta <-> beta M b c (o+i) v).
  { intros i v. unfold theta,rho. apply beta_formula_correct. }
  apply (beta_pack_function M rho theta n b).
  - intros i _. destruct (beta_total M b c (o+i)) as [v Hv].
    exists v. exact (proj2 (HC i v) Hv).
  - intros i v _ Hv. apply (remainder_le_dividend M b (beta_modulus M c (o+i)) v).
    exact (proj1 (HC i v) Hv).
  - intros i v w _ Hv Hw.
    exact (beta_unique M b c (o+i) v w (proj1 (HC i v) Hv) (proj1 (HC i w) Hw)).
Qed.

Definition tail_edge (x y : D) : Prop := exists h, pair_graph M h y x.

Definition tail_path (b c n : D) : Prop :=
  forall i x y, coding_lt M i n -> beta M b c i x ->
    beta M b c (S i) y -> tail_edge x y.

Definition reaches (w z : D) : Prop :=
  exists b c n, beta M b c O w /\ beta M b c n z /\ tail_path b c n.

Lemma reaches_self w : reaches w w.
Proof.
  exists w,w,O. split; [apply beta_singleton|].
  split; [apply beta_singleton|].
  intros i x y Hi. exfalso. exact (coding_not_lt_zero M i Hi).
Qed.

Lemma path_first b c n w z :
  beta M b c O w -> beta M b c (S n) z -> tail_path b c (S n) ->
  exists y, tail_edge w y /\ reaches y z.
Proof.
  intros Hw Hz Hp.
  destruct (beta_total M b c (S O)) as [y Hy].
  exists y. split.
  - apply (Hp O w y); [apply coding_zero_lt_succ|exact Hw|exact Hy].
  - destruct (beta_slice b c (S O) (S n)) as [b' [c' Hs]].
    exists b',c',n. split.
    + apply (proj2 (Hs O y (coding_zero_lt_succ M n))).
      replace (S O+O) with (S O) by ring. exact Hy.
    + split.
      * apply (proj2 (Hs n z (coding_lt_succ M n))).
        rewrite (Arithmetic.add_succ M O n), (Arithmetic.add_zero M n). exact Hz.
      * intros i x t Hi Hx Ht.
        assert (Hi' : coding_lt M i (S n)).
        { apply coding_lt_succ_cases. now left. }
        assert (Hsi : coding_lt M (S i) (S n)).
        { apply coding_lt_succ_cancel. exact Hi. }
        apply (proj1 (Hs i x Hi')) in Hx.
        apply (proj1 (Hs (S i) t Hsi)) in Ht.
        rewrite (Arithmetic.add_succ M O i), (Arithmetic.add_zero M i) in Hx.
        rewrite (Arithmetic.add_succ M O (S i)), (Arithmetic.add_zero M (S i)) in Ht.
        exact (Hp (S i) x t Hsi Hx Ht).
Qed.

Lemma reaches_prepend w t z : tail_edge w t -> reaches t z -> reaches w z.
Proof.
  intros Hwt [b [c [n [Ht [Hz Hp]]]]].
  destruct (beta_concatenate M w w (S O) b c (S n)) as [b' [c' [Hl Hr]]].
  exists b',c',(S n). split.
  - apply Hl; [apply coding_zero_lt_succ|apply beta_singleton].
  - split.
    + pose proof (Hr n z (coding_lt_succ M n) Hz) as H.
      rewrite (Arithmetic.add_succ M O n), (Arithmetic.add_zero M n) in H. exact H.
    + intros i x y Hi Hx Hy.
      destruct (@Peano.zero_or_succ D (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) i) as [-> | [j ->]].
      * assert (Ex : x=w).
        { eapply beta_unique; [exact Hx|apply Hl; [apply coding_zero_lt_succ|apply beta_singleton]]. }
        assert (Ey : y=t).
        { eapply beta_unique; [exact Hy|].
          pose proof (Hr O t (coding_zero_lt_succ M n) Ht) as H.
          replace (S O+O) with (S O) in H by ring. exact H. }
        now subst x y.
      * assert (Hjn : coding_lt M j n) by (apply coding_lt_succ_cancel;exact Hi).
        assert (Hsj : coding_lt M (S j) (S n)) by exact Hi.
        destruct (beta_total M b c j) as [x' Hx'].
        destruct (beta_total M b c (S j)) as [y' Hy'].
        assert (Ex : x=x').
        { eapply beta_unique; [exact Hx|].
          pose proof (Hr j x' (proj2 (coding_lt_succ_cases M j n) (or_introl Hjn)) Hx') as H.
          rewrite (Arithmetic.add_succ M O j), (Arithmetic.add_zero M j) in H. exact H. }
        assert (Ey : y=y').
        { eapply beta_unique; [exact Hy|].
          pose proof (Hr (S j) y' Hsj Hy') as H.
          rewrite (Arithmetic.add_succ M O (S j)), (Arithmetic.add_zero M (S j)) in H. exact H. }
        subst x y. exact (Hp j x' y' Hjn Hx' Hy').
Qed.

End Paths.
