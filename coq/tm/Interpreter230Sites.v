(** Site certificates for K230, adapted from Jeff's pinned m254 Site.v. *)
From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia PArith.
From BusyCoq Require Import TM.
From K230 Require Import Table230 TM230 Zip Boot230 Runtime230Core RM.
Import ListNotations.

(** ** Sites *)
Inductive op : Type := OInc (r : nat) | ODec (r : nat) | OBrk (k : nat) | OCont (k : nat) | OHalt.

Fixpoint pos_bits (p : positive) (acc : list bool) : list bool :=
  match p with
  | xH => acc
  | xO p => pos_bits p (false :: acc)
  | xI p => pos_bits p (true :: acc)
  end.
Definition path_of (p : positive) : list bool := pos_bits p [].

(** Cells between the PC marker and the register header: at least [D0]; the boot leaves 181. *)
Definition D0 := 64.
Definition growth (x : boxst) := match x with BPlain (FDec _) => 1 | _ => 0 end.

Definition start (Q : list bool) : sconf :=
  (84, false, [SB true], map SB Q ++ [SR false 1 (D0 - length Q); SB true; SBox (BPlain FNone)]).

(* [ovf]: the PC overflowed, the marker moved one cell left *)
Definition tgt_conf (P : list bool) (ovf : bool) (x : boxst) : sconf :=
  (84, false, [SB true], map SB P ++ [SR false 1 (D0 + (if ovf then 1 else 0) + growth x - length P); SB true; SBox x]).

Definition FUEL := 4000.

Definition run_to (br : branch) (Q : list bool) (e : sconf) : bool :=
  match exec FUEL br (fun s => matches s e) (start Q) false with Some _ => true | None => false end.

Definition is_halt (s : sconf) : bool := let '(q, _, _, _) := s in Nat.eqb q NH.

Definition run_halt (Q : list bool) : bool :=
  match exec FUEL None is_halt (start Q) false with Some _ => true | None => false end.

Definition allones (P : list bool) : bool := forallb (fun b => b) P.

Definition check_site (Q : list bool) (o : op) : bool :=
  match o with
  | OInc r => run_to None Q (tgt_conf (inc_path Q) (allones Q) (BPlain (FInc r)))
  | ODec r =>
      andb (run_to (Some (r, true)) Q (tgt_conf (brk 1 Q) (allones (strip_path false 1 Q)) (BPlain FNone)))
           (run_to (Some (r, false)) Q (tgt_conf (inc_path Q) (allones Q) (BPlain (FDec r))))
  | OBrk k => run_to None Q (tgt_conf (brk k Q) (allones (strip_path false k Q)) (BPlain FNone))
  | OCont k => run_to None Q (tgt_conf (cont k Q) false (BPlain FNone))
  | OHalt => run_halt Q
  end.

(** ** Concrete meaning of [start] and [tgt_conf] *)
Lemma conc_start n vs Q :
  conc n vs (start Q) = zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs).
Proof.
  unfold start, conc. rewrite flat_app, flat_SB. unfold flat. simpl.
  rewrite Nat.add_0_r, !app_nil_r. reflexivity.
Qed.

Lemma conc_target n vs P ovf x :
  conc n vs (tgt_conf P ovf x) =
  zc (st 84) [true] (P ++ zeros (n + (D0 + (if ovf then 1 else 0) + growth x - length P)) ++ true :: box_list x vs).
Proof.
  unfold tgt_conf, conc. rewrite flat_app, flat_SB. unfold flat. simpl.
  rewrite Nat.add_0_r, !app_nil_r. reflexivity.
Qed.

Section Sound.

Lemma conc_target_plain n vs P ovf :
  conc n vs (tgt_conf P ovf (BPlain FNone)) =
  zc (st 84) [true] (P ++ zeros (n + (D0 + (if ovf then 1 else 0) - length P)) ++ true :: sepsR vs).
Proof. rewrite conc_target. cbn [growth box_list]. now rewrite Nat.add_0_r. Qed.

Lemma conc_target_inc n vs P ovf r :
  conc n vs (tgt_conf P ovf (BPlain (FInc r))) =
  zc (st 84) [true] (P ++ zeros (n + (D0 + (if ovf then 1 else 0) - length P)) ++ true :: sepsR (incr r vs ++ [1])).
Proof. rewrite conc_target. cbn [growth box_list]. now rewrite Nat.add_0_r. Qed.

Lemma conc_target_dec n vs P ovf r :
  conc n vs (tgt_conf P ovf (BPlain (FDec r))) =
  zc (st 84) [true] (P ++ zeros (n + (D0 + (if ovf then 1 else 0) + 1 - length P)) ++ true :: sepsR (decr r vs)).
Proof. rewrite conc_target. reflexivity. Qed.

Hypothesis box_mark : forall q r l vs, skip_target q = Some r -> 10 <= length vs ->
  zc (st q) l (sepsR vs) -->* zl (st (mark_exit r)) l (sepsM r vs).
Hypothesis box_inc : forall r l vs, r < 9 -> 10 <= length vs ->
  zc (st 64) l (sepsM r vs) -->* zl (st 40) l (sepsR (incr r vs ++ [1])).
Hypothesis box_dec0 : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 = 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 97) l (sepsR vs).
Hypothesis box_decp : forall r l vs, r < 9 -> 10 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 40) (true :: l) (sepsR (decr r vs)).

Lemma run_to_sound br Q e : run_to br Q e = true ->
  forall n vs, valid br vs -> conc n vs (start Q) -->+ conc n vs e.
Proof.
  unfold run_to. destruct (exec FUEL br (fun s => matches s e) (start Q) false) as [s|] eqn:E;
    [|discriminate]. intros _ n vs V.
  destruct (exec_sound box_mark box_inc box_dec0 box_decp _ _ _ _ _ _ n vs E V) as (Hm & _ & P).
  rewrite <- (matches_conc _ _ n vs Hm). apply P. reflexivity.
Qed.

Lemma run_halt_sound Q : run_halt Q = true ->
  forall n vs, 10 <= length vs -> exists l r, conc n vs (start Q) -->+ zc (st NH) l r.
Proof.
  unfold run_halt. destruct (exec FUEL None is_halt (start Q) false) as [s|] eqn:E; [|discriminate].
  intros _ n vs V.
  destruct (exec_sound box_mark box_inc box_dec0 box_decp _ _ _ _ _ _ n vs E (conj V I)) as (Hh & _ & P).
  destruct s as [[[q onl] l] r]. simpl in Hh. apply Nat.eqb_eq in Hh. subst q.
  specialize (P eq_refl). simpl in P. destruct onl.
  - eexists _, _. exact P.
  - eexists _, _. exact P.
Qed.

(** The per-site theorem for an increment (the other operations are analogous). *)
Theorem site_inc Q r : check_site Q (OInc r) = true ->
  forall n vs, 10 <= length vs ->
  zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs) -->+
  zc (st 84) [true] (inc_path Q ++ zeros (n + (D0 + (if allones Q then 1 else 0) - length (inc_path Q)))
                     ++ true :: sepsR (incr r vs ++ [1])).
Proof.
  intros H n vs V. rewrite <- conc_start. rewrite <- (conc_target_inc n vs _ _ r).
  apply (run_to_sound None); [exact H | split; [exact V | exact I]].
Qed.

Theorem site_dec Q r : check_site Q (ODec r) = true ->
  forall n vs, 10 <= length vs ->
  (nth r vs 0 = 0 ->
   zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs) -->+
   zc (st 84) [true] (brk 1 Q ++ zeros (n + (D0 + (if allones (strip_path false 1 Q) then 1 else 0)
                                               - length (brk 1 Q))) ++ true :: sepsR vs)) /\
  (nth r vs 0 <> 0 ->
   zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs) -->+
   zc (st 84) [true] (inc_path Q ++ zeros (n + (D0 + (if allones Q then 1 else 0) + 1 - length (inc_path Q)))
                      ++ true :: sepsR (decr r vs))).
Proof.
  intros H n vs V. simpl in H. apply andb_prop in H as [H0 H1]. split; intros Z.
  - rewrite <- conc_start. rewrite <- (conc_target_plain n vs _ _).
    apply (run_to_sound (Some (r, true))); [exact H0 | split; [exact V | exact Z]].
  - rewrite <- conc_start. rewrite <- (conc_target_dec n vs _ _ r).
    apply (run_to_sound (Some (r, false))); [exact H1 | split; [exact V | exact Z]].
Qed.

(** General forms used by Sim.v *)
Lemma site_run br Q P ovf x : run_to br Q (tgt_conf P ovf x) = true ->
  forall n vs, valid br vs ->
  zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs) -->+
  zc (st 84) [true] (P ++ zeros (n + (D0 + (if ovf then 1 else 0) + growth x - length P)) ++ true :: box_list x vs).
Proof.
  intros H n vs V. rewrite <- conc_start, <- conc_target. apply (run_to_sound br); assumption.
Qed.

Lemma site_halt Q : run_halt Q = true -> forall n vs, 10 <= length vs ->
  exists c, zc (st 84) [true] (Q ++ zeros (n + (D0 - length Q)) ++ true :: sepsR vs) -->+ c /\ halted tm c.
Proof.
  intros H n vs V. destruct (run_halt_sound Q H n vs V) as (l & r & P).
  rewrite conc_start in P. exists (zc (st NH) l r). split; [exact P | reflexivity].
Qed.

End Sound.
