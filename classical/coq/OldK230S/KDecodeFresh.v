(** The raw matrix code is a fresh variable label, including codes 0 and 1.
    This is a syntax theorem, not a soundness theorem for the machine. *)
From Coq Require Import Arith Lia Bool.
From OldZF Require Import Logic L1_LMeta Std_alpha.
From OldK230S Require Import KCode230 KDecoder230.

Fixpoint names_below (n : nat) (p : wff) : Prop :=
  match p with
  | Weq x y | Wel x y => x < n /\ y < n
  | Wim p q => names_below n p /\ names_below n q
  | Wn p => names_below n p
  | Wal x p => x < n /\ names_below n p
  end.

Lemma Df_names_below f : forall n bound, n < bound ->
  names_below bound (Df f n).
Proof.
  induction f as [|f IH]; intros n bound Hn.
  - cbn [Df T0 names_below]. repeat split; lia.
  - destruct n as [|n].
    + cbn [Df T0 names_below]. repeat split; lia.
    + cbn [Df]. unfold Dbody.
      pose proof (div4_lt (S n) ltac:(lia)) as Hd.
      pose proof (unP_le (S n / 4)) as [Hx Hy].
      destruct (unP (S n / 4)) as [x y]. cbn [fst snd] in Hx, Hy.
      destruct (S n mod 4) as [|[|[|k]]].
      * destruct (Nat.eqb y 1); cbn [names_below];
          repeat split; apply IH; lia.
      * cbn [names_below]. lia.
      * cbn [names_below]. split; [lia|apply IH; lia].
      * cbn [names_below]. lia.
Qed.

Theorem D_names_below n : 0 < n -> names_below n (D n).
Proof.
  intros Hn. rewrite D_unfold by exact Hn. unfold Dbody.
  pose proof (div4_lt n Hn) as Hd.
  pose proof (unP_le (n / 4)) as [Hx Hy].
  destruct (unP (n / 4)) as [x y]. cbn [fst snd] in Hx, Hy.
  destruct (n mod 4) as [|[|[|k]]].
  - destruct (Nat.eqb y 1); cbn [names_below]; repeat split;
      unfold D; apply Df_names_below; lia.
  - cbn [names_below]. lia.
  - cbn [names_below]. split; [lia|unfold D; apply Df_names_below; lia].
  - cbn [names_below]. lia.
Qed.

Lemma names_below_occ p : forall bound k,
  names_below bound p -> bound <= k -> occ k p = false.
Proof.
  induction p as [x y|x y|p IHp q IHq|p IH|x p IH];
    intros bound k H Hk; cbn [names_below] in H; cbn [occ].
  - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
  - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
  - destruct H as [Hp Hq]. rewrite (IHp bound k Hp Hk), (IHq bound k Hq Hk).
    reflexivity.
  - exact (IH bound k H Hk).
  - destruct H as [Hx Hp]. apply Bool.orb_false_iff. split.
    + apply Nat.eqb_neq. lia.
    + exact (IH bound k Hp Hk).
Qed.

Theorem D_positive_occ n : 0 < n -> occ n (D n) = false.
Proof. intros H. eapply names_below_occ; [apply D_names_below, H|lia]. Qed.

Theorem D_private_fresh n : fr n (D n) = false.
Proof.
  destruct n as [|n].
  - reflexivity.
  - apply fr_occ, D_positive_occ. lia.
Qed.

Theorem D_zero_closed k : fr k (D 0) = false.
Proof. rewrite D_0. unfold T0. cbn [fr]. destruct k; reflexivity. Qed.

Theorem D_one : D 1 = Wel 0 0.
Proof. change (D (wel 0 0) = Wel 0 0). apply D_wel. Qed.
