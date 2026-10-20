(** * Std_brnd: natural deduction on [dB] images of named wffs, and the ND equivalence between a
    library formula and the [dB] image of its named translation [tr] ([tr_equiv]). *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_H Std_iface Std_iface2.
From OldZF Require Import Std_setnd Std_setbase Std_breq.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Rules for [dB] images *)
Section DBRules.
Context {G : list form}.

Lemma dB_allE rho x a t : G ⊢C dB rho (Wal x a) -> G ⊢C dB (upd rho x t) a.
Proof. intros H. cbn [dB] in H. apply (AllE t) in H. rewrite dB_inst in H. exact H. Qed.

Lemma dB_allI rho x a : (forall t, G ⊢C dB (upd rho x t) a) -> G ⊢C dB rho (Wal x a).
Proof. intros H. cbn [dB]. apply AllI_named. intros t. rewrite dB_inst. apply H. Qed.

Lemma dB_exI rho x a t : G ⊢C dB (upd rho x t) a -> G ⊢C dB rho (Wex x a).
Proof.
  intros H. unfold Wex. cbn [dB]. apply II. ctx_push H1.
  apply (AllE t) in H1. cbn [subst_form] in H1. rewrite dB_inst in H1. exact (IE H1 H).
Qed.

Lemma dB_exE rho x a psi : G ⊢C dB rho (Wex x a) -> (forall t, G ⊢C dB (upd rho x t) a → psi) -> G ⊢C psi.
Proof.
  intros H H2. apply DN_rule. eapply IE; [apply weak_cons, H|].
  cbn [dB]. apply AllI_named. intros t. cbn [subst_form]. rewrite dB_inst. apply II.
  eapply IE; [apply Ctx; right; now left|]. eapply IE; [apply weak_cons, weak_cons, H2|]. apply Ctx; now left.
Qed.

Lemma dB_andI rho a b : G ⊢C dB rho a -> G ⊢C dB rho b -> G ⊢C dB rho (Wa a b).
Proof.
  intros H1 H2. unfold Wa. cbn [dB]. apply II. eapply IE; [eapply IE; [apply Ctx; now left|]|];
    apply weak_cons; assumption.
Qed.

Lemma dB_andE1 rho a b : G ⊢C dB rho (Wa a b) -> G ⊢C dB rho a.
Proof.
  intros H. unfold Wa in H. cbn [dB] in H. apply DN_rule. eapply IE; [apply weak_cons, H|].
  apply II. apply Exp. eapply IE; [apply Ctx; right; now left|]. apply Ctx; now left.
Qed.

Lemma dB_andE2 rho a b : G ⊢C dB rho (Wa a b) -> G ⊢C dB rho b.
Proof.
  intros H. unfold Wa in H. cbn [dB] in H. apply DN_rule. eapply IE; [apply weak_cons, H|].
  apply II. apply Ctx; right; now left.
Qed.

Lemma dB_imp rho a b : G ⊢C dB rho (Wim a b) -> G ⊢C dB rho a -> G ⊢C dB rho b.
Proof. intros H1 H2. exact (IE H1 H2). Qed.

Lemma dB_neg rho a : G ⊢C dB rho (Wn a) -> G ⊢C dB rho a -> G ⊢C ⊥.
Proof. intros H1 H2. exact (IE H1 H2). Qed.

End DBRules.

Lemma upd_eq (rho : nat -> term) x t : upd rho x t x = t.
Proof. unfold upd. now rewrite Nat.eqb_refl. Qed.

Lemma upd_neq (rho : nat -> term) x t v : v <> x -> upd rho x t v = rho v.
Proof. intros H. unfold upd. apply Nat.eqb_neq in H. now rewrite H. Qed.

(** ** Library formula vs. the dB image of its named translation *)
Lemma bname_inj k k' : bname k = bname k' -> k = k'.
Proof. unfold bname. lia. Qed.

Lemma tr_equiv (phi : form) : forall N eta (rho : nat -> term) G, incl EqAx G -> fb N phi ->
  (forall n k, n < N -> k < qd phi -> eta n <> bname k) ->
  G ⊢C dB rho (tr eta phi) ↔ phi[fun n => rho (eta n)].
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity; intros N eta rho G HE Hfb Hn.
  - cbn. fsplit.
    + fintro H. apply (IE H). apply AllI_named. intros t. cbn. unfold shift_env. cbn. apply (eqE_refl HE).
    + fintro H. fabsurd. exact H.
  - assert (E : dB rho (tr eta (atom P v)) = (atom P v)[fun n => rho (eta n)]).
    { destruct P; cbn in v, Hfb |- *; rewrite (vec2 v); cbn;
        destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; reflexivity. }
    rewrite E. fsplit; apply imp_refl.
  - destruct Hfb as [Fa Fb].
    assert (Hna : forall n k, n < N -> k < qd a -> eta n <> bname k) by (intros; apply Hn; cbn; lia).
    assert (Hnb : forall n k, n < N -> k < qd b -> eta n <> bname k) by (intros; apply Hn; cbn; lia).
    set (sg := fun n => rho (eta n)).
    destruct op.
    + (* conjunction *)
      cbn [tr dB subst_form]. fsplit.
      * fintro H. fsplit.
        -- fcontra Hc. apply (IE H). fintro HA. fintro HB. apply (IE Hc).
           exact (iff_l _ _ _ (IHa N eta rho _ HE Fa Hna) HA).
        -- fcontra Hc. apply (IE H). fintro HA. fintro HB. apply (IE Hc).
           exact (iff_l _ _ _ (IHb N eta rho _ HE Fb Hnb) HB).
      * fintro H. fdestr H H1 H2. fintro Hi. apply (IE (IE Hi (iff_r _ _ _ (IHa N eta rho _ HE Fa Hna) H1))).
        exact (iff_r _ _ _ (IHb N eta rho _ HE Fb Hnb) H2).
    + (* disjunction *)
      cbn [tr dB subst_form]. fsplit.
      * fintro H. apply (XM_rule _ (a[sg])).
        -- fintro Ha. fleft. exact Ha.
        -- fintro Hna'. fright. apply (iff_l _ _ _ (IHb N eta rho _ HE Fb Hnb)). apply (IE H).
           fintro HA. apply (IE Hna'). exact (iff_l _ _ _ (IHa N eta rho _ HE Fa Hna) HA).
      * fintro H. fintro HnA. fcases H H1 H2.
        -- fabsurd. apply (IE HnA). exact (iff_r _ _ _ (IHa N eta rho _ HE Fa Hna) H1).
        -- exact (iff_r _ _ _ (IHb N eta rho _ HE Fb Hnb) H2).
    + (* implication *)
      rewrite tr_impl_cases. destruct (isbot b) eqn:Eb.
      * apply isbot_true in Eb. subst b. cbn [dB subst_form]. fsplit.
        -- fintro H. fintro Ha. apply (IE H). exact (iff_r _ _ _ (IHa N eta rho _ HE Fa Hna) Ha).
        -- fintro H. fintro HA. apply (IE H). exact (iff_l _ _ _ (IHa N eta rho _ HE Fa Hna) HA).
      * cbn [dB subst_form]. fsplit.
        -- fintro H. fintro Ha. apply (iff_l _ _ _ (IHb N eta rho _ HE Fb Hnb)). apply (IE H).
           exact (iff_r _ _ _ (IHa N eta rho _ HE Fa Hna) Ha).
        -- fintro H. fintro HA. apply (iff_r _ _ _ (IHb N eta rho _ HE Fb Hnb)). apply (IE H).
           exact (iff_l _ _ _ (IHa N eta rho _ HE Fa Hna) HA).
  - set (y := bname (qd a)). set (sg := fun n => rho (eta n)).
    assert (Hn' : forall n k, n < S N -> k < qd a -> scons y eta n <> bname k).
    { intros [|n] k Hlt Hk; cbn.
      - unfold y. intros E. apply bname_inj in E. lia.
      - apply Hn; cbn; lia. }
    assert (Esub : forall t, a[fun n => upd rho y t (scons y eta n)] = a[t .: sg]).
    { intros t. apply (subst_ext_fb _ (S N)); [exact Hfb|]. intros [|n] Hlt.
      - change (upd rho y t y = t). apply upd_eq.
      - change (upd rho y t (eta n) = rho (eta n)). apply upd_neq. intros E. apply (Hn n (qd a)); [lia| cbn; lia| exact E]. }
    assert (IH : forall t G', incl EqAx G' -> G' ⊢C dB (upd rho y t) (tr (scons y eta) a) ↔ a[t .: sg]).
    { intros t G' HE'. rewrite <- Esub. apply (IHa (S N)); assumption. }
    destruct q.
    + cbn [tr]. fold y. cbn [subst_form]. fsplit.
      * fintro H. apply AllI_named. intros t. rewrite up_inst_form.
        apply (iff_l _ _ _ (IH t _ HE)). exact (dB_allE _ _ _ t H).
      * fintro H. apply dB_allI. intros t. apply (iff_r _ _ _ (IH t _ HE)).
        apply (AllE t) in H. rewrite up_inst_form in H. exact H.
    + cbn [tr]. fold y. cbn [subst_form]. fsplit.
      * fintro H. apply (dB_exE _ _ _ _ H). intros t. fintro Ht. apply (ExI t). rewrite up_inst_form.
        exact (iff_l _ _ _ (IH t _ HE) Ht).
      * fintro H. apply (ExE_named H). intros t. rewrite up_inst_form. ctx_push Ht.
        apply (dB_exI _ _ _ t). exact (iff_r _ _ _ (IH t _ HE) Ht).
Qed.
