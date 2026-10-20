(** Adapted total decoder from Jeff Wff254.v at the same pinned commit. Code 0 is a closed tautology; code 1 is Wel 0 0. Reading arrows to code 1 as negation requires a later relative-falsity/IR bridge; that bridge is not claimed here. *)
From Coq Require Import Arith Lia.
From OldZF Require Import Logic.
From OldK230S Require Import KCode230.

Definition T0 : wff := Wim (Wal 0 (Weq 0 0)) (Wal 0 (Weq 0 0)).

Definition Dbody (rec : nat -> wff) (n : nat) : wff :=
  let '(x, y) := unP (n / 4) in
  match n mod 4 with
  | 0 => if Nat.eqb y 1 then Wn (rec x) else Wim (rec x) (rec y)
  | 1 => Wel x y
  | 2 => Wal x (rec y)
  | _ => Weq x y
  end.

Fixpoint Df (f n : nat) : wff :=
  match f with
  | 0 => T0
  | S f => match n with 0 => T0 | _ => Dbody (Df f) n end
  end.

Definition D (n : nat) : wff := Df (S n) n.

Lemma div4_lt n : 0 < n -> n / 4 < n.
Proof. intro H. apply Nat.div_lt; lia. Qed.

Lemma Df_stable f : forall g n, n < f -> n < g -> Df f n = Df g n.
Proof.
  induction f as [|f IH]; intros [|g] n H1 H2; try lia.
  cbn [Df]. destruct n as [|m]; [reflexivity|].
  unfold Dbody. pose proof (div4_lt (S m) ltac:(lia)) as Hd.
  pose proof (unP_le (S m / 4)) as [Hx Hy].
  destruct (unP (S m / 4)) as [x y]. cbn [fst snd] in Hx, Hy.
  destruct (S m mod 4) as [|[|[|k]]]; try reflexivity.
  - destruct (Nat.eqb y 1); rewrite ?(IH g x), ?(IH g y) by lia; reflexivity.
  - rewrite (IH g y) by lia. reflexivity.
Qed.

Lemma Dbody_ext (r1 r2 : nat -> wff) n : 0 < n -> (forall k, k < n -> r1 k = r2 k) ->
  Dbody r1 n = Dbody r2 n.
Proof.
  intros Hn H. unfold Dbody. pose proof (div4_lt n Hn) as Hd.
  pose proof (unP_le (n / 4)) as [Hx Hy].
  destruct (unP (n / 4)) as [x y]. cbn [fst snd] in Hx, Hy.
  destruct (n mod 4) as [|[|[|k]]]; try reflexivity.
  - destruct (Nat.eqb y 1); rewrite ?(H x), ?(H y) by lia; reflexivity.
  - rewrite (H y) by lia. reflexivity.
Qed.

Lemma D_unfold n : 0 < n -> D n = Dbody D n.
Proof.
  intro Hn. unfold D at 1. destruct n as [|m]; [lia|].
  change (Df (S (S m)) (S m)) with (Dbody (Df (S m)) (S m)).
  apply Dbody_ext; [exact Hn|]. intros k Hk. unfold D. apply Df_stable; lia.
Qed.

Lemma code_div (k t a b : nat) : t < 4 -> (4 * P a b + t) / 4 = P a b /\ (4 * P a b + t) mod 4 = t.
Proof.
  intro Ht. split.
  - rewrite Nat.mul_comm. rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia.
  - rewrite Nat.mul_comm, Nat.add_comm. rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia.
Qed.

Lemma D_0 : D 0 = T0.
Proof. reflexivity. Qed.

Lemma D_wel x y : D (wel x y) = Wel x y.
Proof.
  unfold wel. rewrite D_unfold by lia. unfold Dbody.
  destruct (code_div 0 1 x y ltac:(lia)) as [E1 E2]. rewrite E1, E2, unP_P. reflexivity.
Qed.

Lemma D_weq x y : D (weq x y) = Weq x y.
Proof.
  unfold weq. rewrite D_unfold by lia. unfold Dbody.
  destruct (code_div 0 3 x y ltac:(lia)) as [E1 E2]. rewrite E1, E2, unP_P. reflexivity.
Qed.

Lemma D_wal x a : D (wal x a) = Wal x (D a).
Proof.
  unfold wal. rewrite D_unfold by lia. unfold Dbody.
  destruct (code_div 0 2 x a ltac:(lia)) as [E1 E2]. rewrite E1, E2, unP_P. reflexivity.
Qed.

Lemma wim_pos a b : (a, b) <> (0, 0) -> 0 < wim a b.
Proof.
  intro H. unfold wim. destruct (Nat.eq_dec (P a b) 0) as [E|E]; [|lia].
  apply P_0 in E. destruct E as [-> ->]. now contradiction H.
Qed.

Lemma D_wim a b : b <> 1 -> (a, b) <> (0, 0) -> D (wim a b) = Wim (D a) (D b).
Proof.
  intros H1 H2. pose proof (wim_pos a b H2) as Hp. rewrite D_unfold by exact Hp. unfold Dbody, wim.
  replace (4 * P a b) with (4 * P a b + 0) by lia.
  destruct (code_div 0 0 a b ltac:(lia)) as [E1 E2]. rewrite E1, E2, unP_P.
  apply Nat.eqb_neq in H1. now rewrite H1.
Qed.

Lemma D_wn a : D (wn a) = Wn (D a).
Proof.
  unfold wn, F. assert (Hp : 0 < wim a 1) by (apply wim_pos; congruence).
  rewrite D_unfold by exact Hp. unfold Dbody, wim.
  replace (4 * P a 1) with (4 * P a 1 + 0) by lia.
  destruct (code_div 0 0 a 1 ltac:(lia)) as [E1 E2]. rewrite E1, E2, unP_P. reflexivity.
Qed.

Lemma D_wim00 : D (wim 0 0) = T0.
Proof. reflexivity. Qed.

Lemma D_wex x a : D (wex x a) = Wex x (D a).
Proof. unfold wex. now rewrite D_wn, D_wal, D_wn. Qed.

Lemma D_wa a b : D (wa a b) = Wa (D a) (D b).
Proof.
  unfold wa. rewrite D_wn, D_wim, D_wn; [reflexivity| |].
  - unfold wn, F, wim. pose proof (P_ge_r a 1). lia.
  - intro E. injection E as _ E. unfold wn, F, wim in E. pose proof (P_ge_r b 1). lia.
Qed.
