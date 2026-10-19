(** One consistency direction, including Foundation and Choice at the source. *)
From Coq Require Import List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_iface.
From RegCon Require Import Rel.
From ZFC Require Import Z_prim Z_wo Z_main.
From K230S Require Import KPrimeTheory KQuotZFTransfer.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition StandardZFC (phi : form) : Prop :=
  (ZFc phi \/ phi = ax_reg') \/ phi = ax_ac.

Theorem KPrimeOrd_standardZFC_inconsistent :
  StandardZFC ⊢TC ⊥ -> KPrimeOrd ⊢TC ⊥.
Proof.
  intros H. apply KPrimeOrd_ZFc_inconsistent.
  exact (ac_reg_relcon H).
Qed.

Corollary KPrimeOrd_consistent_implies_standardZFC_consistent :
  (KPrimeOrd ⊢TC ⊥ -> False) -> (StandardZFC ⊢TC ⊥ -> False).
Proof. intros HK HZ. apply HK, KPrimeOrd_standardZFC_inconsistent, HZ. Qed.
