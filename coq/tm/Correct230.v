(** End-to-end, axiom-free Rocq verification of the frozen 230-state machine. *)
From BusyCoq Require TM.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230 Require TM230 Sim230Main.
From K230P Require Import Main230.
From K230S Require Import KQuotZFC.
From K230L Require Import Seed230 Consistency230.

Theorem tm230_halts_iff_ZFC_inconsistent :
  K230.TM230.TM230.halts K230.TM230.tm K230.TM230.TM230.c0 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite Sim230Main.tm230_rm, prog230, seed230_iff_thm.
  exact thm230_iff_standardZFC.
Qed.

Corollary tm230_nonhalting_iff_ZFC_consistent :
  (~ K230.TM230.TM230.halts K230.TM230.tm K230.TM230.TM230.c0) <->
    ~ (StandardZFC ⊢TC ⊥).
Proof. rewrite tm230_halts_iff_ZFC_inconsistent. reflexivity. Qed.
