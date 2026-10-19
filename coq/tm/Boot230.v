(** K230's exact blank-tape bootstrap. After 408419 steps the machine is
    at state 84 with [true] to its left, a gap of 181 zero cells, and
    176 register blocks. The first nine physical values are listed
    below; the 167 spare blocks contain 1. Adapted from the pinned
    m254 Boot.v; correctness is checked anew against Table230. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia PArith.
From BusyCoq Require Import TM.
From K230 Require Import TM230 Zip.
Import ListNotations.

Definition sepsR (vs : list nat) : list bool := flat_map (fun v => false :: ones (S v)) vs.
Definition boot_regs : list nat := [0; 0; 0; 3; 0; 0; 3; 0; 0] ++ repeat 1 167.

(** ** A computable step on list zippers [(q, l, r)] with numeric states, mirroring [zc]. *)
Definition lconf := (nat * list bool * list bool)%type.

Definition lstep (s : lconf) : option lconf :=
  let '(q, l, r) := s in
  match tmn q (hd false r) with
  | None => None
  | Some (w, R, q') => Some (q', w :: l, tl r)
  | Some (w, L, q') => Some (q', tl l, hd false l :: w :: tl r)
  end.

Definition lconc (s : lconf) : Q * tape := let '(q, l, r) := s in zc (st q) l r.

Lemma lstep_sound s s' : lstep s = Some s' -> lconc s -[ tm ]-> lconc s'.
Proof.
  destruct s as [[q l] r]. unfold lstep. intros H.
  assert (E : zc (st q) l r = zc (st q) l (hd false r :: tl r)) by (destruct r; reflexivity).
  simpl. rewrite E. clear E.
  destruct (tmn q (hd false r)) as [[[w [|]] q1]|] eqn:T; [| |discriminate];
    injection H as <-; simpl.
  - apply zL, tm_st, T.
  - apply zR, tm_st, T.
Qed.

(* run exactly [p] steps (binary recursion on the step count) *)
Fixpoint lrunp (p : positive) (s : lconf) : option lconf :=
  match p with
  | xH => lstep s
  | xO p => match lrunp p s with None => None | Some s => lrunp p s end
  | xI p => match lstep s with
            | None => None
            | Some s => match lrunp p s with None => None | Some s => lrunp p s end
            end
  end.

Lemma lrunp_sound p s s' : lrunp p s = Some s' -> lconc s -->* lconc s'.
Proof.
  revert s s'. induction p as [p IH|p IH|]; intros s s' H; simpl in H.
  - destruct (lstep s) as [s1|] eqn:E1; [|discriminate].
    destruct (lrunp p s1) as [s2|] eqn:E2; [|discriminate].
    eapply evstep_step; [apply lstep_sound, E1|].
    eapply evstep_trans; [apply IH, E2 | apply IH, H].
  - destruct (lrunp p s) as [s1|] eqn:E1; [|discriminate].
    eapply evstep_trans; [apply IH, E1 | apply IH, H].
  - eapply evstep_step; [apply lstep_sound, H | apply evstep_refl].
Qed.

(** ** Trailing blanks *)
Fixpoint dropf (l : list bool) : list bool :=
  match l with false :: l => dropf l | _ => l end.
Definition trim (l : list bool) : list bool := rev (dropf (rev l)).

Lemma dropf_spec l : exists n, l = zeros n ++ dropf l.
Proof.
  induction l as [|[|] l IH]; [exists 0; reflexivity | exists 0; reflexivity|].
  destruct IH as [n E]. exists (S n). simpl. rewrite <- E. reflexivity.
Qed.

Lemma rev_zeros n : rev (zeros n) = zeros n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. symmetry. apply (rep_snoc false n). Qed.

Lemma trim_spec l : exists n, l = trim l ++ zeros n.
Proof.
  destruct (dropf_spec (rev l)) as [n E]. exists n. unfold trim.
  rewrite <- rev_zeros, <- rev_app_distr, <- E. symmetry. apply rev_involutive.
Qed.

Definition boot_right : list bool := zeros 181 ++ true :: sepsR boot_regs.

Definition boot_ok : bool :=
  match lrunp 408419 (0, [], []) with
  | Some (q, l, r) =>
      andb (Nat.eqb q 84)
           (andb (if list_eq_dec bool_dec (trim l) [true] then true else false)
                 (if list_eq_dec bool_dec (trim r) boot_right then true else false))
  | None => false
  end.

Lemma boot_ok_true : boot_ok = true.
Proof. Time vm_compute. reflexivity. Qed.

(* the blank tape is [zc (st 0) [] []] *)
Theorem boot : c0 -->* zc (st 84) [true] boot_right.
Proof.
  pose proof boot_ok_true as B. unfold boot_ok in B.
  destruct (lrunp 408419 (0, [], [])) as [[[q l] r]|] eqn:E; [|discriminate].
  apply andb_prop in B as [Bq B]. apply andb_prop in B as [Bl Br]. apply Nat.eqb_eq in Bq. subst q.
  destruct (list_eq_dec bool_dec (trim l) [true]) as [El|]; [|discriminate].
  destruct (list_eq_dec bool_dec (trim r) boot_right) as [Er|]; [|discriminate].
  apply lrunp_sound in E. simpl in E. change c0 with (zc (st 0) [] []).
  destruct (trim_spec l) as [m1 H1]. destruct (trim_spec r) as [m2 H2].
  rewrite H1, H2, El, Er, zc_padl, zc_padr in E. exact E.
Qed.
