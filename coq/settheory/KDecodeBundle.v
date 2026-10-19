(** Exact named-formula decoding of the promoted K230 source schema.
    No role renaming, simplification, or replacement of low matrix codes. *)
From Coq Require Import Arith Lia Bool.
From ZF Require Import Logic.
From K230S Require Import KCode230 KDecoder230.

Definition KSubset (a b k : nat) : wff :=
  Wal k (Wim (Wel k a) (Wel k b)).
Definition KRequest (b k : nat) (phi : wff) : wff :=
  Wal b (Wim phi (Wex b (Wa phi (Wel b k)))).
Definition KCore (a b k : nat) (phi : wff) : wff :=
  Wex k (Wa (Wim phi (Wel b k))
    (Wal b (Wim (Wel b k)
      (Wex a (Wa phi (Wal a (Wim (KSubset a b k) (KRequest b k phi)))))))).
Definition KVacuity (a b c : nat) : wff :=
  Wa (Wim (Wel a b) (Wal c (Wel a b)))
     (Wim (Weq a b) (Wal c (Weq a b))).
Definition KBundle (a b c : nat) (phi : wff) : wff :=
  Wa (KCore a b c phi) (KVacuity a b c).

Lemma wel_nonzero a b : wel a b <> 0.
Proof. unfold wel. lia. Qed.
Lemma wal_nonzero a b : wal a b <> 0.
Proof. unfold wal. lia. Qed.
Lemma wn_nonzero a : wn a <> 0.
Proof. unfold wn, F. apply wim_pos_r. lia. Qed.
Lemma wex_nonzero x a : wex x a <> 0.
Proof. apply wn_nonzero. Qed.
Lemma wa_nonzero a b : wa a b <> 0.
Proof. apply wn_nonzero. Qed.
Lemma wel_nonone a b : a <> b -> wel a b <> 1.
Proof.
  intros H E. unfold wel in E. assert (P a b = 0) by lia.
  apply P_0 in H0 as [-> ->]. contradiction.
Qed.
Lemma pair_nonzero_r a b : b <> 0 -> (a,b) <> (0,0).
Proof. intros H E. injection E. auto. Qed.

Ltac kdecode_side := first
  [ assumption | congruence
  | apply wel_nonzero | apply wal_nonzero | apply wex_nonzero | apply wa_nonzero
  | apply wal_ne_F | apply wex_ne_F | apply wa_ne_F
  | apply wel_nonone; congruence
  | apply pair_nonzero_r; kdecode_side ].
Ltac kdecode := repeat first
  [ rewrite D_wa | rewrite D_wex | rewrite D_wal | rewrite D_wel | rewrite D_weq
  | rewrite D_wim by kdecode_side ].

Theorem D_kcore a b k m : k <> b -> D (kcore a b k m) = KCore a b k (D m).
Proof.
  intros H. unfold kcore, ksubset, krequest, KCore, KSubset, KRequest.
  kdecode. reflexivity.
Qed.

Theorem D_vacuity230 a b c : D (vacuity230 a b c) = KVacuity a b c.
Proof. unfold vacuity230, KVacuity. kdecode. reflexivity. Qed.

Theorem D_bundle230 a b c : c <> b ->
  D (bundle230 a b c) = KBundle a b c (D c).
Proof.
  intros H. unfold bundle230, KBundle, k230.
  now rewrite D_wa, D_kcore, D_vacuity230 by exact H.
Qed.

Theorem D_gated230_enabled a b c : c <> a -> c <> b ->
  D (gated230 a b c) = KBundle a b c (D c).
Proof.
  intros H1 H2. rewrite gated230_enabled by assumption.
  now apply D_bundle230.
Qed.

Theorem D_gated230_disabled a b c : c = a \/ c = b ->
  D (gated230 a b c) = T0.
Proof. intros H. rewrite gated230_disabled by exact H. apply D_0. Qed.
