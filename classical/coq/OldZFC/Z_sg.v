(** * Z_sg: the hierarchy formulas are Sigma (checked by computation). *)
From OldUndecidability.FOL Require Import Sets.minZF.
From OldZF Require Import Std_tr.
From OldZFC Require Import Z_rel Z_base Z_cl Z_L.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Lemma D0_Ord0 : D0 (Ord0 $0).
Proof. d0comp. Qed.
Lemma Sg_Def0 : Sg (Def0 $0 $1).
Proof. sgcomp. Qed.
Lemma Sg_LL : Sg (LL $0 $1).
Proof. sgcomp. Qed.
Lemma Sg_Lform : Sg Lform.
Proof. sgcomp. Qed.
