(** Adapted arithmetic coding from Jeff Codes254.v, commit c132d7eae8158cd3a9850ea3eb7251158c3dd821. K230 uses exactly this dual Cantor pairing. No 254-state theory is imported. *)
From Coq Require Import Arith Lia.

Fixpoint tri (n : nat) : nat := match n with 0 => 0 | S m => S m + tri m end.

Definition P (a b : nat) : nat := tri (a + b) + b.

Definition unP_step (o : nat * nat) : nat * nat :=
  match o with
  | (S a, b) => (a, S b)
  | (0, b) => (S b, 0)
  end.

Definition unP (z : nat) : nat * nat := Nat.iter z unP_step (0, 0).

Lemma tri_S n : tri (S n) = S n + tri n.
Proof. reflexivity. Qed.

Lemma P_unP_step a b : P (fst (unP_step (a, b))) (snd (unP_step (a, b))) = S (P a b).
Proof.
  unfold P. destruct a as [|a]; cbn [unP_step fst snd].
  - rewrite !Nat.add_0_r, !Nat.add_0_l. cbn [tri]. lia.
  - replace (a + S b) with (S a + b) by lia. lia.
Qed.

Lemma P_0 a b : P a b = 0 -> a = 0 /\ b = 0.
Proof.
  unfold P. destruct (a + b) as [|s] eqn:E; cbn [tri]; intro H; lia.
Qed.

(** every positive code has a predecessor along the unpair walk *)
Lemma P_pred a b : P a b <> 0 -> exists a' b', P a' b' + 1 = P a b /\ unP_step (a', b') = (a, b).
Proof.
  intro Hn. destruct b as [|b].
  - destruct a as [|a]; [unfold P in Hn; cbn in Hn; lia|].
    exists 0, a. split; [|reflexivity].
    pose proof (P_unP_step 0 a) as H. cbn [unP_step fst snd] in H. lia.
  - exists (S a), b. split; [|reflexivity].
    pose proof (P_unP_step (S a) b) as H. cbn [unP_step fst snd] in H. lia.
Qed.

Lemma unP_P a b : unP (P a b) = (a, b).
Proof.
  remember (P a b) as n eqn:E. revert a b E. induction n as [|n IH]; intros a b E.
  - symmetry in E. destruct (P_0 a b E) as [-> ->]. reflexivity.
  - destruct (P_pred a b ltac:(lia)) as [a' [b' [H1 H2]]].
    change (unP (S n)) with (unP_step (unP n)). rewrite (IH a' b') by lia. exact H2.
Qed.

Lemma P_unP z : P (fst (unP z)) (snd (unP z)) = z.
Proof.
  induction z as [|z IH]; [reflexivity|].
  change (unP (S z)) with (unP_step (unP z)). destruct (unP z) as [a b].
  rewrite P_unP_step. cbn [fst snd] in IH. now rewrite IH.
Qed.

Lemma P_ge_l a b : a <= P a b.
Proof.
  unfold P. assert (forall n, n <= tri n) by (induction n; cbn; lia).
  specialize (H (a + b)). lia.
Qed.

Lemma P_ge_r a b : b <= P a b.
Proof. unfold P. lia. Qed.

Lemma unP_le z : fst (unP z) <= z /\ snd (unP z) <= z.
Proof.
  pose proof (P_unP z) as E. pose proof (P_ge_l (fst (unP z)) (snd (unP z))).
  pose proof (P_ge_r (fst (unP z)) (snd (unP z))). lia.
Qed.

Lemma unP_0 : unP 0 = (0, 0).
Proof. reflexivity. Qed.

Lemma P_inj a b a' b' : P a b = P a' b' -> a = a' /\ b = b'.
Proof. intro H. pose proof (unP_P a b) as E. rewrite H, unP_P in E. now injection E. Qed.

(** ** Formula codes *)
Definition wim (a b : nat) : nat := 4 * P a b.
Definition wel (i j : nat) : nat := 4 * P i j + 1.
Definition wal (i a : nat) : nat := 4 * P i a + 2.
Definition weq (i j : nat) : nat := 4 * P i j + 3.
Definition F : nat := 1.
Definition wn (a : nat) : nat := wim a F.
Definition wa (a b : nat) : nat := wn (wim a (wn b)).
Definition wex (x a : nat) : nat := wn (wal x (wn a)).

Lemma wel_0_0 : wel 0 0 = F.
Proof. reflexivity. Qed.

(** Frozen source: output role b, input role a, private label c, opaque
    formula code c. Both selected and local conjunctions are reversed.
    Unchanged theory template from dynamic_role_search.formula, opt-233-231-checked.json;
    original 231-state table SHA256 f2b60e0256328cd602c4355609f4eda60b7c072023e31f863104f57ef7047cc0.
    The 230-state source only reparameterizes the separate rho6 logical row. *)
Definition ksubset (a b k : nat) : nat :=
  wal k (wim (wel k a) (wel k b)).
Definition krequest (b k m : nat) : nat :=
  wal b (wim m (wex b (wa m (wel b k)))).
Definition kcore (a b k m : nat) : nat :=
  wex k (wa (wim m (wel b k))
    (wal b (wim (wel b k)
      (wex a (wa m (wal a (wim (ksubset a b k) (krequest b k m)))))))).
Definition k230 (a b c : nat) : nat := kcore a b c c.
Definition vacuity230 (a b c : nat) : nat :=
  wa (wim (wel a b) (wal c (wel a b)))
     (wim (weq a b) (wal c (weq a b))).
Definition bundle230 (a b c : nat) : nat :=
  wa (k230 a b c) (vacuity230 a b c).
Definition gated230 (a b c : nat) : nat :=
  if (Nat.eqb c a || Nat.eqb c b)%bool then 0 else bundle230 a b c.

Lemma wim_ne_F a b : wim a b <> F.
Proof. unfold wim, F. lia. Qed.
Lemma wal_ne_F a b : wal a b <> F.
Proof. unfold wal, F. lia. Qed.
Lemma wn_ne_F a : wn a <> F.
Proof. apply wim_ne_F. Qed.
Lemma wex_ne_F x a : wex x a <> F.
Proof. apply wim_ne_F. Qed.
Lemma wa_ne_F a b : wa a b <> F.
Proof. apply wim_ne_F. Qed.
Lemma wim_pos_r a b : 0 < b -> wim a b <> 0.
Proof. unfold wim. pose proof (P_ge_r a b). lia. Qed.

Lemma k230_ne_halt a b c : k230 a b c <> F.
Proof. apply wex_ne_F. Qed.
Lemma bundle230_ne_halt a b c : bundle230 a b c <> F.
Proof. apply wa_ne_F. Qed.
Lemma gated230_ne_halt a b c : gated230 a b c <> F.
Proof.
  unfold gated230. destruct (Nat.eqb c a || Nat.eqb c b)%bool;
    [unfold F; discriminate|apply bundle230_ne_halt].
Qed.
Lemma gated230_enabled a b c : c <> a -> c <> b ->
  gated230 a b c = bundle230 a b c.
Proof.
  intros H1 H2. unfold gated230.
  apply Nat.eqb_neq in H1. apply Nat.eqb_neq in H2.
  now rewrite H1, H2.
Qed.
Lemma gated230_disabled a b c : c = a \/ c = b -> gated230 a b c = 0.
Proof.
  intros [-> | ->]; unfold gated230; rewrite Nat.eqb_refl;
    [reflexivity|now rewrite Bool.orb_true_r].
Qed.

