(** * Std_glue: O'Rear's system proves [v_0 e. v_0] iff the library's ZF (closed schemes) is
    inconsistent.

      Theorem A  (prov_iff_ZFc) :  prov (Wel v0 v0) <-> ZFc ⊢TC ⊥
      Theorem B  (minZFeq_to_prov) :  minZFeq ⊢TC ⊥ -> prov (Wel v0 v0)

    [ZFc] (Std_iface.v) = the library's minZFeq axioms (FOL/Sets/minZF.v: extensionality, empty set,
    pairing, union, power set, von Neumann infinity, equality axioms, separation and replacement
    schemes) with the scheme instances universally closed.  No regularity, no choice (neither is in
    the library's ZF).  [minZFeq] is the library's theory itself, whose scheme instances keep their
    free variables as parameters; the converse of Theorem B for it is not claimed here. *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_setinf.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Composition of derivability *)
Lemma thm_list (T T' : form -> Prop) : (forall psi, T psi -> thm T' psi) ->
  forall A, (forall psi, In psi A -> T psi) ->
  exists B, (forall psi, In psi B -> T' psi) /\ forall psi, In psi A -> B ⊢C psi.
Proof.
  intros H. induction A as [|a A IH]; intros HA.
  - exists []. split; intros _ [].
  - destruct (H a (HA a (or_introl eq_refl))) as [B1 [HB1 D1]].
    destruct (IH (fun psi Hp => HA psi (or_intror Hp))) as [B2 [HB2 D2]].
    exists (B1 ++ B2). split.
    + intros psi [Hp|Hp]%in_app_iff; auto.
    + intros psi [<-|Hp].
      * eapply Weak; [exact D1 | apply incl_appl, incl_refl].
      * eapply Weak; [exact (D2 psi Hp) | apply incl_appr, incl_refl].
Qed.

Lemma thm_trans (T T' : form -> Prop) phi :
  thm T phi -> (forall psi, T psi -> thm T' psi) -> thm T' phi.
Proof.
  intros [A [HA D]] H. destruct (thm_list T T' H A HA) as [B [HB DB]].
  exists B. split; [exact HB | exact (prv_cut D DB)].
Qed.

Lemma thm_ax (T : form -> Prop) phi : T phi -> thm T phi.
Proof. intro H. exists [phi]. split; [intros psi [<-|[]]; exact H | apply Ctx; now left]. Qed.

Lemma thm_tprv (T : form -> Prop) phi : thm T phi <-> @tprv _ _ falsity_on class T phi.
Proof. reflexivity. Qed.

(** ** F direction: prov (v0 e. v0) -> ZFc inconsistent *)
Lemma ZFc_EqAx psi : In psi EqAx -> ZFc psi.
Proof. intros H. left. constructor 1. unfold ZF0base. cbn in *. tauto. Qed.

Lemma Fvalid_of_bridge n a : maxfr a < n -> thm ZFc (Lib n a) -> Fvalid ZFc a.
Proof.
  intros Hn [A [HA D]]. exists A. split; [exact HA|]. intro rho. exact (Lib_inst A n a rho Hn D).
Qed.

Section F.
Hypothesis bEXT : bridge_EXT.
Hypothesis bPOW : bridge_POW.
Hypothesis bUNI : bridge_UNI.
Hypothesis bINFo : bridge_INFo.
Hypothesis bREP : bridge_REP.

Lemma ZFc_Fvalid a : prov a -> Fvalid ZFc a.
Proof.
  apply (@prov_Fvalid ZFc ZFc_EqAx).
  - exact (Fvalid_of_bridge 3 EXT maxfr_EXT bEXT).
  - exact (Fvalid_of_bridge 4 POW maxfr_POW bPOW).
  - exact (Fvalid_of_bridge 4 UNI maxfr_UNI bUNI).
  - exact (Fvalid_of_bridge 3 INF maxfr_INF bINFo).
  - intro ph. exact (Fvalid_of_bridge _ (REP ph) (Nat.lt_succ_diag_r _) (bREP ph _ (Nat.lt_succ_diag_r _))).
Qed.

Theorem prov_to_ZFc : prov (Wel v0 v0) -> thm ZFc falsity.
Proof.
  intro H. destruct (ZFc_Fvalid _ H) as [A [HA D]].
  exists (ax_eset' :: A). split.
  - intros psi [<-|Hp]; [left; constructor 1; unfold ZF0base; cbn; tauto | auto].
  - assert (Hall : (ax_eset' :: A) ⊢C ∀ ($0 ∈' $0)).
    { apply AllI_named. intro t. eapply Weak; [exact (D (fun _ => t)) | intros ? ?; now right]. }
    assert (He : (ax_eset' :: A) ⊢C ax_eset') by (apply Ctx; now left).
    unfold ax_eset' in He. apply (ExE_named He). intro w. cbn.
    assert (H1 : ((is_eset $0)[w..] :: ax_eset' :: A) ⊢C (is_eset $0)[w..]) by (apply Ctx; now left).
    cbn in H1. apply (AllE w) in H1. cbn in H1. rewrite subst_term_shift in H1.
    eapply IE; [exact H1|].
    apply (AllE w) in Hall. cbn in Hall. eapply Weak; [exact Hall | intros ? ?; now right].
Qed.
End F.

(** ** H direction: ZFc inconsistent -> prov (v0 e. v0) *)
Lemma prov_discharge G c : lprov (foldi G c) -> (forall h, In h G -> prov h) -> prov c.
Proof.
  intros H HG. apply lprov_prov in H. revert c H; induction G as [|h G IH]; intros c H; [exact H|].
  cbn [foldi fold_left] in H. specialize (IH (fun h' Hh' => HG h' (or_intror Hh')) _ H).
  exact (DET _ _ IH (HG h (or_introl eq_refl))).
Qed.

Definition eta0 (n : nat) : nat := 2 * n + 1.

Lemma oddenv_eta0 : oddenv eta0.
Proof. intro n. unfold eta0. rewrite Nat.odd_add, Nat.odd_mul. reflexivity. Qed.

Theorem TPset_to_prov : thm TPset falsity -> prov (Wel v0 v0).
Proof.
  intros [C [HC D]].
  pose proof (nd_sound C falsity D eta0 oddenv_eta0) as S. cbn [tr] in S.
  apply der_foldi in S.
  assert (Hb : prov botw).
  { apply (prov_discharge _ _ S). intros h Hh. apply in_map_iff in Hh as [th [<- Hth]].
    destruct (HC th Hth) as (a & n & Ha & Hn & ->). exact (tr_cl_prov eta0 n a Ha Hn). }
  exact (DET _ _ (lprov_prov _ (l_botw_elim _)) Hb).
Qed.

Section H.
Hypothesis bZF0 : bridge_ZF0.
Hypothesis bINF : bridge_INF.

Lemma ZFc_from_TPset psi : ZFc psi -> thm TPset psi.
Proof.
  intros [H| ->]; [now apply bZF0|].
  apply (thm_trans _ _ _ inf_or_to_zf). intros psi [Hp| ->]; [now apply bZF0 | exact bINF].
Qed.

Theorem ZFc_to_prov : thm ZFc falsity -> prov (Wel v0 v0).
Proof. intro H. apply TPset_to_prov. exact (thm_trans _ _ _ H ZFc_from_TPset). Qed.

(** the library's own minZFeq (open scheme instances) *)
Lemma minZFeq_from_ZFc psi : minZFeq psi -> thm ZFc psi.
Proof.
  intros Hm. destruct Hm as [psi Hb | phi | phi].
  - apply thm_ax. unfold minZFeq', minZF' in Hb. cbn in Hb.
    repeat (destruct Hb as [<-|Hb]; [first [left; constructor 1; unfold ZF0base; cbn; tauto | now right] |]).
    destruct Hb.
  - destruct (fb_exists phi) as [N HN].
    assert (Hc : closedf (forall_times N (ax_sep' phi))) by (apply sep_closed; eapply fb_mono; eauto).
    exists [forall_times N (ax_sep' phi)]. split; [intros psi [<-|[]]; left; now constructor 2|].
    assert (X : [forall_times N (ax_sep' phi)] ⊢C (ax_sep' phi)[var])
      by (apply (closed_inst _ N); [exact Hc | apply Ctx; now left]).
    rewrite subst_var in X. exact X.
  - destruct (fb_exists phi) as [N HN].
    assert (Hc : closedf (forall_times N (ax_rep' phi))) by (apply rep_closed; eapply fb_mono; eauto).
    exists [forall_times N (ax_rep' phi)]. split; [intros psi [<-|[]]; left; now constructor 3|].
    assert (X : [forall_times N (ax_rep' phi)] ⊢C (ax_rep' phi)[var])
      by (apply (closed_inst _ N); [exact Hc | apply Ctx; now left]).
    rewrite subst_var in X. exact X.
Qed.

Theorem minZFeq_to_prov : @tprv _ _ falsity_on class minZFeq falsity -> prov (Wel v0 v0).
Proof. intro H. apply ZFc_to_prov. exact (thm_trans _ _ _ H minZFeq_from_ZFc). Qed.
End H.
