(** Adapted from Jeff's pinned m254 Leaves.v. *)
(** * Leaves: the leaves of an RM.v program tree, and the fact that every walk ends at one.

    [leaves p f n] lists, for the (unfolded) tree below node [n], every leaf edge together with
    the bits that lead to it.  [leaves_root]: the bits read by a walk from the root and the leaf
    it reaches form an element of [leaves p (nnodes p + 1) (root p)]. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From K230 Require Import RM RMEquiv.
Import ListNotations.

Definition subl (Lf : nat -> list (list bool * edge)) (b : bool) (e : edge) : list (list bool * edge) :=
  match e with
  | ENode m => map (fun x => (b :: fst x, snd x)) (Lf m)
  | _ => [([b], e)]
  end.

Fixpoint leaves (p : prog) (f n : nat) : list (list bool * edge) :=
  match f with
  | 0 => []
  | S f => subl (fun m => leaves p f m) false (fst (nodes p n)) ++
           subl (fun m => leaves p f m) true (snd (nodes p n))
  end.

Lemma leaves_child p f n b x :
  In x (subl (fun m => leaves p f m) b (child p n b)) -> In x (leaves p (S f) n).
Proof. intros H. simpl. apply in_or_app. destruct b; unfold child in H; [right|left]; exact H. Qed.

Lemma walk_leaves p f n P i e d :
  walk p f n P i = Some (e, d) -> In (map (bit P) (seq i (d - i)), e) (leaves p f n).
Proof.
  revert n i. induction f as [|f IH]; intros n i W; [discriminate|].
  apply leaves_child with (b := bit P i).
  rewrite walk_S in W. destruct (child p n (bit P i)) as [m|r|r|k|k|] eqn:E.
  - pose proof (walk_gt _ _ _ _ _ _ _ W) as [Hlt _].
    specialize (IH m (S i) W).
    replace (d - i) with (S (d - S i)) by lia. cbn [seq map subl].
    apply (in_map (fun x => (bit P i :: fst x, snd x))) in IH. exact IH.
  - injection W as <- <-. replace (S i - i) with 1 by lia. left. reflexivity.
  - injection W as <- <-. replace (S i - i) with 1 by lia. left. reflexivity.
  - injection W as <- <-. replace (S i - i) with 1 by lia. left. reflexivity.
  - injection W as <- <-. replace (S i - i) with 1 by lia. left. reflexivity.
  - injection W as <- <-. replace (S i - i) with 1 by lia. left. reflexivity.
Qed.

Lemma leaves_root p P e d :
  walk p (nnodes p + 1) (root p) P 0 = Some (e, d) ->
  In (firstn d (P ++ repeat false d), e) (leaves p (nnodes p + 1) (root p)).
Proof.
  intros W. rewrite pad_bits. apply walk_leaves in W. rewrite Nat.sub_0_r in W. exact W.
Qed.
