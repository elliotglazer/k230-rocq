(** Exact program semantics from the register file produced by the blank boot. *)
From Coq Require Import List.
From K230 Require Import RM RMEquiv Prog230.
From K230P Require Import Dag230 ProgramBisim230 ProgLib230 L2Root230.
From K230L Require Import Enum230 L1_Comp230 Seed230.
Import ListNotations.

Lemma R0_enc_seed230 : approx R0 (enc seed230).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Theorem prog230 : rm_halts p230 ([], R0) <-> L1_Comp230.halts_from seed230.
Proof.
  rewrite p230_dag, (rm_halts_iff_iter _ dag230_wf).
  exact (iter_halts_dag seed230 R0 R0_enc_seed230).
Qed.

Corollary prog230_iter : iter_halts p230 R0 <-> L1_Comp230.halts_from seed230.
Proof. rewrite <- (rm_halts_iff_iter _ p230_wf). exact prog230. Qed.
