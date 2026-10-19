(** * Zip: list-zipper views of busycoq tapes for k230 (adapted from zf/v335/coq/SimBase.v).

    [zc q l r] is the configuration in state [q] whose head is on the first cell of [r]
    ([r] read rightwards, [l] read leftwards from the head), both sides completed with
    blanks.  [zl q l r] has the head on the first cell of [l] instead. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import TM230.
Import ListNotations.

Notation zeros n := (repeat false n).
Notation ones n := (repeat true n).

Definition zc (q : state) (l r : list bool) : Q * tape :=
  (q, (Str_app l (const false), hd false r, Str_app (tl r) (const false))).

Definition zl (q : state) (l r : list bool) : Q * tape := zc q (tl l) (hd false l :: r).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma zR q l (b : bool) r (w : bool) q' : tm (q, b) = Some (w, R, q') -> zc q l (b :: r) -[ tm ]-> zc q' (w :: l) r.
Proof. intros H. destruct r; exact (step_right H). Qed.

Lemma zL q l (b : bool) r (w : bool) q' : tm (q, b) = Some (w, L, q') -> zc q l (b :: r) -[ tm ]-> zl q' l (w :: r).
Proof. intros H. destruct l; exact (step_left H). Qed.

Lemma zl_cons q x l r : zl q (x :: l) r = zc q l (x :: r).
Proof. reflexivity. Qed.

Lemma zl_nil q r : zl q [] r = zc q [] (false :: r).
Proof. reflexivity. Qed.

Lemma rep_comm {A} (x : A) n l : repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma rep_snoc {A} (x : A) n : repeat x (S n) = repeat x n ++ [x].
Proof. induction n as [|n IH]; [reflexivity|]. simpl in *. rewrite IH. reflexivity. Qed.

Lemma rep_add {A} (x : A) n m : repeat x (n + m) = repeat x n ++ repeat x m.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma str_app_false l : Str_app (l ++ [false]) (const false) = Str_app l (const false).
Proof.
  induction l as [|x l IH]; simpl.
  - symmetry. apply const_unfold.
  - rewrite IH. reflexivity.
Qed.

Lemma str_app_zeros l n : Str_app (l ++ zeros n) (const false) = Str_app l (const false).
Proof.
  induction n as [|n IH].
  - rewrite app_nil_r. reflexivity.
  - rewrite rep_snoc, app_assoc, str_app_false. exact IH.
Qed.

Lemma zc_padl q l r n : zc q (l ++ zeros n) r = zc q l r.
Proof. unfold zc. rewrite str_app_zeros. reflexivity. Qed.

Lemma zl_padl q l r n : zl q (l ++ zeros n) r = zl q l r.
Proof.
  unfold zl. destruct l as [|x l].
  - destruct n as [|n]; [reflexivity|]. simpl. apply (zc_padl q [] _ n).
  - simpl. apply zc_padl.
Qed.

Lemma zc_padr q l r n : zc q l (r ++ zeros n) = zc q l r.
Proof.
  unfold zc. destruct r as [|x r].
  - destruct n as [|n]; [reflexivity|]. simpl.
    rewrite <- (app_nil_l (zeros n)), str_app_zeros. reflexivity.
  - simpl. rewrite str_app_zeros. reflexivity.
Qed.

(** ** Self-loops over runs (possibly rewriting the symbol) *)
Lemma scanR q (b w : bool) n l r : tm (q, b) = Some (w, R, q) ->
  zc q l (repeat b n ++ r) -->* zc q (repeat w n ++ l) r.
Proof.
  intros H. revert l. induction n as [|n IH]; intros l; simpl.
  - apply evstep_refl.
  - eapply evstep_step; [apply zR, H|]. rewrite <- rep_comm. apply IH.
Qed.

Lemma scanL q (b w : bool) n l r : tm (q, b) = Some (w, L, q) ->
  zl q (repeat b n ++ l) r -->* zl q l (repeat w n ++ r).
Proof.
  intros H. revert r. induction n as [|n IH]; intros r; simpl.
  - apply evstep_refl.
  - rewrite zl_cons. eapply evstep_step; [apply zL, H|].
    rewrite <- rep_comm. apply IH.
Qed.
