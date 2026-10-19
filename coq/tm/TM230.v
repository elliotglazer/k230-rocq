(** Adapted from Jeff's pinned TM254.v; see THIRD_PARTY.txt. *)
(** * TM230: k230.tm as a busycoq [TM].

    States are the numbers 0..230 ([bnat 230]); state 230 is the terminal state (no row).
    The machine is read off the literal table [table230] (Table230.v, generated from the file);
    [tmn] is the same transition function on plain numbers, used by the symbolic executor. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia Eqdep_dec.
From BusyCoq Require Import TM.
From K230 Require Import Table230.
Import ListNotations.

(** ** Bounded naturals (as in zf/v335/coq/ZFTM.v) *)
Definition bnat (k : nat) : Type := { n : nat | Nat.leb n k = true }.

Definition bval {k} (x : bnat k) : nat := proj1_sig x.

Definition bmk (k n : nat) : bnat k :=
  match Nat.leb n k as b return Nat.leb n k = b -> bnat k with
  | true => fun H => exist _ n H
  | false => fun _ => exist _ k (Nat.leb_refl k)
  end eq_refl.

Lemma bnat_eq : forall k (x y : bnat k), bval x = bval y -> x = y.
Proof.
  intros k [x Hx] [y Hy]; simpl; intros ->.
  f_equal. apply UIP_dec. exact bool_dec.
Qed.

Lemma bval_bmk : forall k n, n <= k -> bval (bmk k n) = n.
Proof.
  intros k n H. unfold bmk.
  generalize (@eq_refl bool (Nat.leb n k)).
  generalize (Nat.leb n k) at 2 3. intros b E. destruct b; [reflexivity|].
  apply Nat.leb_nle in E. lia.
Qed.

Lemma bmk_bval : forall k (x : bnat k), bmk k (bval x) = x.
Proof.
  intros k x. apply bnat_eq. apply bval_bmk.
  destruct x as [n H]. simpl. apply Nat.leb_le, H.
Qed.

Lemma bval_le : forall k (x : bnat k), bval x <= k.
Proof. intros k [n H]. simpl. apply Nat.leb_le, H. Qed.

Definition bnat_dec {k} (x y : bnat k) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (bval x) (bval y)) as [E|E].
  - left. apply bnat_eq, E.
  - right. intros ->. apply E. reflexivity.
Defined.

Definition ball (k : nat) : list (bnat k) := map (bmk k) (seq 0 (S k)).

Lemma ball_spec : forall k x, In x (ball k).
Proof.
  intros k x. unfold ball. rewrite <- (bmk_bval k x).
  apply in_map, in_seq. pose proof (bval_le k x). lia.
Qed.

(** ** The busycoq context *)
Definition NH := 230.                     (* the terminal state *)
Definition state := bnat NH.
Definition st (n : nat) : state := bmk NH n.

Module Ctx230 <: Ctx.
  Definition Q := state.
  Definition Sym := bool.
  Definition q0 := st 0.
  Definition s0 := false.
  Definition q1 := st 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof. intros H. apply (f_equal bval) in H. vm_compute in H. discriminate. Qed.
  Definition s1 := true.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q : forall a b : Q, {a = b} + {a <> b} := bnat_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := ball NH.
  Definition all_qs_spec := ball_spec NH.
  Definition all_syms := [false; true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; tauto. Qed.
End Ctx230.

Module TM230 := TM.TM Ctx230.
Export TM230.

(** ** The transition function *)
Definition tmn (q : nat) (s : bool) : option (bool * dir * nat) :=
  match nth_error table230 q with
  | None => None
  | Some (w0, d0, n0, w1, d1, n1) => if s then Some (w1, d1, n1) else Some (w0, d0, n0)
  end.

Definition tm : TM := fun '(q, s) =>
  match tmn (bval q) s with
  | None => None
  | Some (w, d, n) => Some (w, d, st n)
  end.

Lemma table_length : length table230 = NH.
Proof. reflexivity. Qed.

Lemma tm_st q s w d n : tmn q s = Some (w, d, n) -> tm (st q, s) = Some (w, d, st n).
Proof.
  intros H. assert (Hq : q < NH).
  { unfold tmn in H. destruct (nth_error table230 q) eqn:E; [|discriminate].
    rewrite <- table_length. apply nth_error_Some. rewrite E. discriminate. }
  unfold tm. rewrite bval_bmk by (unfold NH in *; lia). rewrite H. reflexivity.
Qed.

Lemma tm_halt s : tm (st NH, s) = None.
Proof. reflexivity. Qed.

(** every transition target is a state (no row points beyond 230) *)
Lemma targets_ok : forallb (fun '(_, _, n0, _, _, n1) => andb (Nat.leb n0 NH) (Nat.leb n1 NH)) table230 = true.
Proof. vm_compute. reflexivity. Qed.
