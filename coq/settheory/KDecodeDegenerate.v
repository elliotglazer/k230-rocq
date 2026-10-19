(** Coincident active roles in the literal source are valid.  Empty and a
    container for one specified object suffice; no singleton uniqueness,
    extensionality, or metatheoretic excluded middle is used. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_tr Std_alpha Std_F Std_iface
  Std_setnd Std_setbase Std_breq Std_brnd.
From K230S Require Import KP0 KDecodeBundle KDecodeAbstract.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma decode_env_root_fresh a b k rho C q : fr k q = false ->
  dB (decode_env a b k rho (rho b) (rho a) C) q = dB rho q.
Proof.
  intros Hfresh. rewrite <- decode_env_root. apply dB_ext_fr. intros v Hv.
  unfold upd. destruct (Nat.eqb_spec v k) as [->|Hne]; [congruence|reflexivity].
Qed.

Lemma named_same_roles_true G q a k rho C : k <> a -> fr k q = false ->
  G ⊢C dB rho q -> G ⊢C rho a ∈' C -> G ⊢C dB rho (KCore a a k q).
Proof.
  intros Hka Hfresh Hq Hmem. unfold KCore.
  apply (dB_exI _ _ _ C). rewrite (decode_env_root a a k rho C).
  apply dB_andI.
  - apply II. ctx_push Hunused.
    match goal with |- ?G0 ⊢C _ =>
      change (G0 ⊢C dB (decode_env a a k rho (rho a) (rho a) C) (Wel a k)) end.
    rewrite decode_env_member by exact Hka. exact Hmem.
  - apply dB_allI. intros u. rewrite decode_env_output by exact Hka.
    apply II. ctx_push Hunused.
    apply (dB_exI _ _ _ (rho a)). rewrite decode_env_output by exact Hka.
    apply dB_andI.
    + rewrite decode_env_root_fresh by exact Hfresh. exact Hq.
    + apply dB_allI. intros p. rewrite decode_env_output by exact Hka.
      apply II. ctx_push Hsub.
      apply (dB_allI _ a (Wim q (Wex a (Wa q (Wel a k))))).
      intros z. rewrite decode_env_output by exact Hka.
      apply II. ctx_push Hz.
      apply (dB_exI _ _ _ (rho a)). rewrite decode_env_output by exact Hka.
      apply dB_andI.
      * rewrite decode_env_root_fresh by exact Hfresh. exact Hq.
      * rewrite decode_env_member by exact Hka. exact Hmem.
Qed.

Lemma named_same_roles_false G q a k rho C : k <> a -> fr k q = false ->
  G ⊢C ¬ dB rho q -> G ⊢C ∀ ($0 ∈' C`[↑] → ⊥) ->
  G ⊢C dB rho (KCore a a k q).
Proof.
  intros Hka Hfresh Hq Hempty. unfold KCore.
  apply (dB_exI _ _ _ C). rewrite (decode_env_root a a k rho C).
  apply dB_andI.
  - apply II. ctx_push Hphi. rewrite decode_env_root_fresh in Hphi by exact Hfresh.
    fabsurd. exact (IE Hq Hphi).
  - apply dB_allI. intros u. rewrite decode_env_output by exact Hka.
    apply II. ctx_push Hu.
    match type of Hu with ?G0 ⊢C _ =>
      change (G0 ⊢C dB (decode_env a a k rho u (rho a) C) (Wel a k)) in Hu end.
    rewrite decode_env_member in Hu by exact Hka.
    finst Hempty u. fabsurd. exact (IE Hempty Hu).
Qed.

Definition hosting230 : form := ∀ ∃ ($1 ∈' $0).

Theorem named_same_roles G q a k rho : k <> a -> fr k q = false ->
  G ⊢C empty_object -> G ⊢C hosting230 -> G ⊢C dB rho (KCore a a k q).
Proof.
  intros Hka Hfresh Hempty Hhost. apply (XM_rule G (dB rho q)).
  - fintro Hq. unfold hosting230 in Hhost. finst Hhost (rho a).
    fex Hhost C HC. exact (named_same_roles_true _ q a k rho C Hka Hfresh Hq HC).
  - fintro Hq. unfold empty_object in Hempty. fex Hempty C HC.
    exact (named_same_roles_false _ q a k rho C Hka Hfresh Hq HC).
Qed.
