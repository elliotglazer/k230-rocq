(** Halting equivalence for the frozen K230 table and Prog230. *)
From Coq Require Import Lists.List.
From BusyCoq Require Import TM.
From K230 Require Import RM RMEquiv Prog230 TM230 Zip Boot230 Sim230.
Import ListNotations.

Theorem tm230_rm : halts tm c0 <-> rm_halts p230 ([], R0).
Proof.
  split.
  - intros H.
    assert (Hb : halts tm (zc (st 84) [true] boot_right)) by exact (halts_evstep' tm _ _ H boot).
    destruct (progress_halts tm (fun T => exists N, Inv N T) (fun _ => rm_halts p230 ([], R0))
                (zc (st 84) [true] boot_right)) as (T & _ & HZ).
    + intros T [N HI]. destruct (inv_next N T HI) as [(c & Hr & Ha) | (c' & Hr')].
      * left. exists N, c. split; assumption.
      * right. destruct (inv_step N T c' HI Hr') as (T' & HI' & HT').
        exists T'. split; [exists (S N); exact HI' | exact HT'].
    + exists 0. exact inv_boot.
    + exact Hb.
    + exact HZ.
  - intros (N & c & Hr & Ha).
    destruct (reach N c Hr) as (T & HT & HI).
    exact (halts_evstep tm _ _ (inv_halt N T c HI Hr Ha) HT).
Qed.

Corollary tm230_iter : halts tm c0 <-> iter_halts p230 R0.
Proof. rewrite tm230_rm. apply rm_halts_iff_iter, p230_wf. Qed.

