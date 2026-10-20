(** Transport of the decoder's pure-logic equivalences to ordinary natural
    deduction.  All equality assumptions are explicit.  The actual emitted
    core-to-KPrimeOrd theorem is a separate construction. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LMeta Std_dB Std_tr Std_alpha
  Std_F Std_iface Std_setnd Std_setbase Std_breq Std_brnd.
From OldK230S Require Import KCode230 KDecoder230 KDecodeBundle KDecodeEncode
  KDecodeLogic KDecodeTranslate.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem lprov_dB230 p : lprov p -> forall rho, EqAx ⊢C dB rho p.
Proof.
  induction 1 as
    [a b Hab IH1 Ha IH2 | x a Ha IH | a b c | a | a b | x a b
    | x y z Hxz Hyz | x y a | x a | x y | x y z | x y z | x y z];
    intros rho.
  - exact (IE (IH1 rho) (IH2 rho)).
  - cbn [dB]. apply AllI_named. intros t. rewrite dB_inst. apply IH.
  - eapply Weak; [apply nd_B1 | intros f H; contradiction].
  - eapply Weak; [apply nd_B2 | intros f H; contradiction].
  - eapply Weak; [apply nd_B3 | intros f H; contradiction].
  - eapply Weak; [apply nd_B4 | intros f H; contradiction].
  - eapply Weak; [apply nd_B6a; assumption | intros f H; contradiction].
  - eapply Weak; [apply nd_B6b | intros f H; contradiction].
  - eapply Weak; [apply nd_B6c | intros f H; contradiction].
  - apply nd_B7.
  - apply nd_B8a.
  - apply nd_B8b.
  - apply nd_B8c.
Qed.

Theorem leqv_dB230 G rho p q : incl EqAx G -> leqv p q ->
  G ⊢C dB rho p ↔ dB rho q.
Proof.
  intros HE [Hpq Hqp]. apply CI.
  - eapply Weak; [exact (lprov_dB230 _ Hpq rho) | exact HE].
  - eapply Weak; [exact (lprov_dB230 _ Hqp rho) | exact HE].
Qed.

Lemma source_names_notbinder n k : source_names n <> bname k.
Proof. destruct n as [|[|n]]; unfold source_names, bname; lia. Qed.

Theorem ordinary_matrix230_equiv G (phi : form) N rho :
  incl EqAx G -> fb N phi ->
  G ⊢C dB rho (tr source_names phi) ↔ phi[fun n => rho (source_names n)].
Proof.
  intros HE Hfb. apply (tr_equiv phi N); try assumption.
  intros n k Hn Hk. apply source_names_notbinder.
Qed.

Theorem ordinary_code230_nd_core G (phi : form) rho : incl EqAx G ->
  G ⊢C dB rho (D (gated230 1 3 (ordinary_code230 phi))) ↔
    dB rho (KCore 1 3 (ordinary_code230 phi) (tr source_names phi)).
Proof.
  intros HE. apply leqv_dB230; [exact HE | apply ordinary_code230_core].
Qed.
