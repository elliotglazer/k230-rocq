(** The literal interpreter tree and the structured source have identical
    halting behavior, by checking every branch of a finite bisimulation. *)
From Coq Require Import List.
From K230 Require Import RM RMEquiv Prog230.
From K230P Require Import Bisim230 Dag230 Cert230.
Import ListNotations.

Lemma cert230_forward : check (ptree p230) (ptree dag230) cert230 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cert230_backward : check (ptree dag230) (ptree p230) (mirror cert230) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p230_dag R : rm_halts p230 ([], R) <-> rm_halts dag230 ([], R).
Proof. exact (check_iff p230 dag230 cert230 cert230_forward cert230_backward R). Qed.

Lemma dag230_wf : wf dag230.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.
