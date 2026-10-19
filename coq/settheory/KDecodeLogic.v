(** Pure named-logic consequences of the exact decoder. The code-level
    proof enumerator and the de Bruijn KPrimeOrd bridge are not assumed. *)
From Coq Require Import Arith Lia.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta.
From K230S Require Import KCode230 KDecoder230 KDecodeBundle KDecodeEncode.
Unset Implicit Arguments.

Lemma kleqv_refl p : leqv p p.
Proof. split; apply lpc_id. Qed.
Lemma kleqv_trans p q r : leqv p q -> leqv q r -> leqv p r.
Proof. intros [Hpq Hqp] [Hqr Hrq]. split; eapply lsyl; eassumption. Qed.
Lemma kleqv_neg p q : leqv p q -> leqv (Wn p) (Wn q).
Proof. intros [Hpq Hqp]. split; apply lcontra; assumption. Qed.
Lemma kleqv_all x p q : leqv p q -> leqv (Wal x p) (Wal x q).
Proof. intros [Hpq Hqp]. split; apply lal; assumption. Qed.
Lemma kleqv_imp p p' q q' : leqv p p' -> leqv q q' ->
  leqv (Wim p q) (Wim p' q').
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_lprov, ded, ded.
  - mp q; [dt H3 | mp p; [dh | mp p'; [dt H2 | dh]]].
  - mp q'; [dt H4 | mp p'; [dh | mp p; [dt H1 | dh]]].
Qed.

Theorem KCore_matrix_equiv a b c p q : leqv p q ->
  leqv (KCore a b c p) (KCore a b c q).
Proof.
  intros H. unfold KCore, KSubset, KRequest, Wex, Wa.
  repeat first [exact H | apply kleqv_refl | apply kleqv_imp
    | apply kleqv_neg | apply kleqv_all].
Qed.

Lemma KVacuity_pure a b c : c <> a -> c <> b -> lprov (KVacuity a b c).
Proof.
  intros Ha Hb.
  pose proof (LB6a a b c ltac:(congruence) ltac:(congruence)) as H.
  destruct (ae_sound _ _ (ae_andcomm
    (Wim (Weq a b) (Wal c (Weq a b)))
    (Wim (Wel a b) (Wal c (Wel a b))))) as [Hswap _].
  exact (LDET _ _ Hswap H).
Qed.

Theorem KBundle_core_equiv a b c p : c <> a -> c <> b ->
  leqv (KBundle a b c p) (KCore a b c p).
Proof.
  intros Ha Hb. unfold KBundle. split.
  - apply lpc_andl.
  - apply der_lprov, ded.
    mp (KVacuity a b c).
    + mp (KCore a b c p);
        [dt (lpc_andi (KCore a b c p) (KVacuity a b c)) | dh].
    + apply dthm. now apply KVacuity_pure.
Qed.

Theorem decoded_enabled_core_equiv a b c : c <> a -> c <> b ->
  leqv (D (gated230 a b c)) (KCore a b c (D c)).
Proof.
  intros Ha Hb. rewrite D_gated230_enabled by assumption.
  now apply KBundle_core_equiv.
Qed.

Theorem decoded_disabled_pure a b c : c = a \/ c = b ->
  lprov (D (gated230 a b c)).
Proof.
  intros H. rewrite D_gated230_disabled by exact H. unfold T0. apply lpc_id.
Qed.

Theorem padded_decoded_core_equiv p : no_relative_atom p ->
  leqv (D (gated230 1 3 (padded230 p))) (KCore 1 3 (padded230 p) p).
Proof.
  intros Hp. eapply kleqv_trans.
  - apply decoded_enabled_core_equiv; pose proof (padded230_gt_three p); lia.
  - rewrite D_padded230 by exact Hp. apply KCore_matrix_equiv.
    split; [apply lpc_nn_elim | apply lpc_nn_intro].
Qed.
