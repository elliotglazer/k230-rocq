(** * Relative consistency of the axiom of regularity

    ZFc     = the library's ZF axioms (ZFeq': equality axioms, extensionality, empty set,
              pairing, union, power set, infinity) plus the universal closures of all
              instances of the separation and replacement schemes (library's ax_sep, ax_rep);
    ZFcReg  = ZFc plus the axiom of regularity (foundation).

    Main theorem: ZFcReg ⊢TC ⊥ -> ZFc ⊢TC ⊥ (classical natural deduction of the library). *)

Require Import OldUndecidability.FOL.ZF.
Require Import OldUndecidability.FOL.Syntax.Facts.
Require Import OldUndecidability.FOL.Sets.ZF.
Require Import OldUndecidability.FOL.Reductions.PCPb_to_ZFD.
From OldUndecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.
Require Import Lia.
From OldRegCon Require Import Rel WF.

#[local] Hint Constructors prv : core.
#[local] Instance pc : peirce := class.

Open Scope syn.

#[local] Hint Extern 3 (incl _ _) => inc : core.
#[local] Hint Extern 3 (_ ⊢ _) => ctx : core.

(* ** The theories *)

Definition ax_reg : form :=
  ∀ (∃ $0 ∈ $1) → ∃ ($0 ∈ $1 ∧ ∀ ($0 ∈ $1 → ¬ ($0 ∈ $2))).

Inductive ZFc : form -> Prop :=
| ZFc_base phi : In phi ZFeq' -> ZFc phi
| ZFc_sep phi n : bounded n (ax_sep phi) -> ZFc (forall_times n (ax_sep phi))
| ZFc_rep phi n : bounded n (ax_rep phi) -> ZFc (forall_times n (ax_rep phi)).

Inductive ZFcReg : form -> Prop :=
| ZFcReg_ZF phi : ZFc phi -> ZFcReg phi
| ZFcReg_reg : ZFcReg ax_reg.

(* ** The class WF as relativization predicate *)

Notation relw := (rel Mwf).

Arguments Mwf : simpl never.

Lemma Mwf_up sigma : Mwf[up sigma] = Mwf.
Proof. apply M_up, Mwf_bounded. Qed.

#[export] Hint Rewrite Mwf_up Mwf_inst : wfsubst.

Ltac rsimp := cbn; autorewrite with wfsubst; cbn; subsimpl.

#[local] Instance ZF_funcs_dec' : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

#[local] Instance ZF_preds_dec' : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Ltac bcomp := apply bounded_comp_eq; compute; repeat split; lia.

Definition B0 : list form := ZFeq' ++ Wax.

Lemma B0_closed b sigma : b el B0 -> b[sigma] = b.
Proof.
  intros Hb. apply bounded_0_subst. unfold B0, ZFeq', ZF', Wax in Hb.
  repeat (destruct Hb as [<-|Hb]; [bcomp |]). destruct Hb.
Qed.

Lemma B0_ZFeq G : B0 <<= G -> ZFeq' <<= G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.

Lemma B0_Wax G : B0 <<= G -> Wax <<= G.
Proof. intros H a Ha. apply H, in_app_iff. now right. Qed.

Lemma Mwf_funcs Gamma f v : B0 <<= Gamma ->
  (forall t, Vector.In t v -> Gamma ⊢ Mwf[t..]) -> Gamma ⊢ Mwf[(func f v)..].
Proof.
  intros HB Hv. rewrite Mwf_inst. setoid_rewrite Mwf_inst in Hv.
  pose proof (B0_ZFeq HB) as HT. pose proof (B0_Wax HB) as HW.
  destruct f; cbn in v.
  - revert Hv. pattern v; apply Vector.case0. intros _.
    now apply WF_eset.
  - revert Hv. apply (Vector.caseS' v). clear v. intros a v. apply (Vector.caseS' v). clear v.
    intros b v. pattern v; apply Vector.case0.
    intros Hv. apply WF_pair; trivial; apply Hv.
    + apply Vector.In_cons_hd.
    + apply Vector.In_cons_tl, Vector.In_cons_hd.
  - revert Hv. apply (Vector.caseS' v). clear v. intros a v.
    pattern v; apply Vector.case0.
    intros Hv. apply WF_union; trivial. apply Hv, Vector.In_cons_hd.
  - revert Hv. apply (Vector.caseS' v). clear v. intros a v.
    pattern v; apply Vector.case0.
    intros Hv. apply WF_power; trivial. apply Hv, Vector.In_cons_hd.
  - revert Hv. pattern v; apply Vector.case0. intros _.
    now apply WF_om.
Qed.

(* ** Relativized subset *)

Definition subM (x y : term) : form := ∀ (Mwf → ($0 ∈ x`[↑] → $0 ∈ y`[↑])).
Arguments subM : simpl never.

Lemma rel_sub x y : relw (sub x y) = subM x y.
Proof. reflexivity. Qed.

Lemma subM_subst x y sigma : (subM x y)[sigma] = subM x`[sigma] y`[sigma].
Proof. unfold subM. cbn. now rewrite Mwf_up, !up_term. Qed.

#[export] Hint Rewrite rel_sub subM_subst : wfsubst.

Lemma subM_intro T x y : (forall z, (z ∈ x :: WF z :: T) ⊢ z ∈ y) -> T ⊢ subM x y.
Proof. intros H. unfold subM. apply AllI_named. intros z. rsimp. apply II, II, H. Qed.

Lemma subM_elim T x y z : T ⊢ subM x y -> T ⊢ WF z -> T ⊢ z ∈ x -> T ⊢ z ∈ y.
Proof.
  intros H1 H2 H3. unfold subM in H1. apply (AllE z) in H1. rsimp. cbn in H1.
  rewrite Mwf_inst in H1. subsimpl_in H1. eapply IE; [eapply IE|]; eassumption.
Qed.

Lemma sub_subM T x y : T ⊢ sub x y -> T ⊢ subM x y.
Proof. intros H. apply subM_intro. intros z. eapply sub_elim; [wk H | auto]. Qed.

Lemma subM_sub T x y : T ⊢ WF x -> T ⊢ subM x y -> T ⊢ sub x y.
Proof.
  intros H1 H2. apply sub_intro. intros z. eapply subM_elim; [wk H2 | | auto].
  eapply WF_el; [wk H1 | auto].
Qed.

(* ** Relativized axioms of ZFeq' *)

Section Axioms.

Variable G : list form.
Hypothesis HG : ZFeq' <<= G.

Lemma ax_G phi : phi el ZFeq' -> G ⊢ phi.
Proof. intros H. apply Ctx, HG, H. Qed.

Lemma rel_ext : G ⊢ relw ax_ext.
Proof.
  unfold ax_ext. cbn. rewrite !rel_sub. apply AllI_named. intros x. rsimp. apply II.
  apply AllI_named. intros y. rsimp. apply II, II, II.
  apply ZF_ext'; [auto | |]; apply subM_sub; auto.
Qed.

Lemma rel_union : G ⊢ relw ax_union.
Proof.
  unfold ax_union. cbn. apply AllI_named. intros x. rsimp. apply II.
  apply AllI_named. intros z. rsimp. apply II. apply CI.
  - apply II. apply (union_elim (x := x) (z := z)); [auto | auto |]. intros y.
    apply (ExI y). rsimp. apply CI; [| apply CI; auto].
    eapply WF_el; [| apply ctx1]. auto.
  - apply II. eapply ExE_named; [auto |]. intros y. rsimp.
    apply ZF_union_el' with y; [auto |]. eapply CE2. auto.
Qed.

Lemma power_intro T x z : ZFeq' <<= T -> T ⊢ sub z x -> T ⊢ z ∈ PP x.
Proof.
  intros HT H. assert (HP : T ⊢ ax_power) by (apply Ctx, HT; cbn; tauto).
  unfold ax_power in HP. apply (AllE x), (AllE z) in HP. simp_in HP.
  eapply IE; [eapply CE2, HP | exact H].
Qed.

Lemma rel_power : G ⊢ relw ax_power.
Proof.
  unfold ax_power. cbn. rewrite rel_sub. apply AllI_named. intros x. rsimp. apply II.
  apply AllI_named. intros y. rsimp. apply II. apply CI.
  - apply II. apply sub_subM, power_el; auto.
  - apply II. apply power_intro; [auto |]. apply subM_sub; auto.
Qed.

Lemma rel_om1 : G ⊢ relw ax_om1.
Proof.
  assert (H : G ⊢ ax_om1) by (apply ax_G; cbn; tauto). unfold ax_om1, inductive in *. cbn.
  apply CI; [eapply CE1, H |]. apply AllI_named. intros z. rsimp. apply II.
  eapply CE2, (AllE z) in H. cbn in H. subsimpl_in H. wk H.
Qed.

Lemma rel_om2 : G ⊢ relw ax_om2.
Proof.
  assert (H : G ⊢ ax_om2) by (apply ax_G; cbn; tauto). unfold ax_om2, inductive in *. cbn.
  rewrite rel_sub. apply AllI_named. intros x. rsimp. apply II, II. apply sub_subM.
  apply (AllE x) in H. simp_in H. eapply IE; [wk H |]. apply CI.
  - eapply CE1. auto.
  - apply AllI_named. intros z. cbn. subsimpl. apply II.
    assert (H' : (z ∈ x :: (∅ ∈ x ∧ (∀ (Mwf → ($0 ∈ x`[↑] → σ $0 ∈ x`[↑])))) :: WF x :: G)
      ⊢ ∀ (Mwf → ($0 ∈ x`[↑] → σ $0 ∈ x`[↑]))) by (eapply CE2; auto).
    apply (AllE z) in H'. rsimp. cbn in H'. rewrite Mwf_inst in H'. subsimpl_in H'.
    eapply IE; [eapply IE; [exact H' |] | auto]. eapply WF_el; auto.
Qed.

End Axioms.

(* ** Axioms with a quantifier-free matrix *)

Lemma rel_drop G n theta : forall_times n theta el G -> bounded n theta -> relw theta = theta ->
  bounded 0 (forall_times n theta) -> G ⊢ relw (forall_times n theta).
Proof.
  intros H1 H2 H3 H4. rewrite <- (subst_var (relw (forall_times n theta))).
  apply (rel_forall_times Mwf_bounded (L := [forall_times n theta])).
  - intros b sigma [<-|[]]. apply bounded_0_subst, H4.
  - intros Gamma tau HL. rewrite H3. apply (subst_forall_prv (N := n)); [apply Ctx, HL; now left | exact H2].
  - intros a [<-|[]]. exact H1.
Qed.

Lemma rel_qf G phi : ZFeq' <<= G -> phi el [ax_refl; ax_sym; ax_trans; ax_eq_elem; ax_eset; ax_pair] ->
  G ⊢ relw phi.
Proof.
  intros HG H. repeat (destruct H as [<-|H]); try destruct H.
  - apply (rel_drop (n := 1) (theta := $0 ≡ $0)); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
  - apply (rel_drop (n := 2) (theta := $1 ≡ $0 → $0 ≡ $1)); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
  - apply (rel_drop (n := 3) (theta := $2 ≡ $1 → $1 ≡ $0 → $2 ≡ $0)); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
  - apply (rel_drop (n := 4) (theta := $3 ≡ $1 → $2 ≡ $0 → $3 ∈ $2 → $1 ∈ $0)); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
  - apply (rel_drop (n := 1) (theta := ¬ ($0 ∈ ∅))); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
  - apply (rel_drop (n := 3) (theta := $0 ∈ {$1; $2} ↔ $0 ≡ $1 ∨ $0 ≡ $2)); [apply HG; cbn; tauto | bcomp | reflexivity | bcomp].
Qed.

(* ** Regularity holds in WF *)

Lemma rel_reg G : ZFeq' <<= G -> G ⊢ relw ax_reg.
Proof.
  intros HG. unfold ax_reg. cbn. apply AllI_named. intros x. rsimp. apply II, II.
  eapply ExE_named; [auto |]. intros y. rsimp. apply conj_split.
  apply (WF_elim (x := x)); [auto |]. intros t.
  eapply min_elim.
  { apply wf_elim with t y; [apply tw_wf; auto | | auto].
    apply sub_intro. intros z. eapply trans_elim; [apply tw_trans; auto | auto | auto]. }
  intros m. apply (ExI m). rsimp. apply CI; [| apply CI].
  - eapply WF_el; [| eapply minel_el; auto]. auto.
  - eapply minel_el; auto.
  - apply AllI_named. intros z. rsimp. apply II, II, II. eapply minel_min; auto.
Qed.

(* ** Separation and replacement hold in WF *)

Lemma rel_sep_core G phi : B0 <<= G -> G ⊢ ax_sep (relw phi) -> G ⊢ relw (ax_sep phi).
Proof.
  intros HB H. pose proof (B0_ZFeq HB) as HT. pose proof (B0_Wax HB) as HW.
  unfold ax_sep. cbn. rewrite <- !(rel_subst Mwf_bounded).
  apply AllI_named. intros X. rsimp. apply II.
  apply (sep_elim (X := X) (prv_weak1 _ H)). intros Z.
  apply (ExI Z). rsimp. apply CI.
  - apply WF_closure; [auto | auto |]. apply AllI_named. intros v. simp. apply II.
    eapply WF_el; [apply ctx3 |]. eapply CE1, sep_in; auto.
  - apply AllI_named. intros V. rsimp. rewrite sep_norm. apply II. apply CI.
    + apply II. eapply sep_in; auto.
    + apply II. eapply sep_out; [auto | eapply CE1; auto | eapply CE2; auto].
Qed.

Lemma fr_norm (phi : form) X Y Y' a :
  phi[$2 .: a .: Nat.add 3 >> var][up (up (X..))][up (Y..)][Y'..] =
  phi[X .: (a`[up (up (X..))]`[up (Y..)]`[Y'..])..].
Proof. rewrite !subst_comp. apply subst_ext. intros [|[|j]]; cbn; trivial; term_eq. Qed.

Lemma rel_rep_core G phi : B0 <<= G -> G ⊢ ax_rep ((WF $0 ∧ WF $1) ∧ relw phi) -> G ⊢ relw (ax_rep phi).
Proof.
  intros HB H. pose proof (B0_ZFeq HB) as HT. pose proof (B0_Wax HB) as HW.
  unfold ax_rep, fun_rel. cbn. rewrite <- !(rel_subst Mwf_bounded). apply II.
  match goal with |- (?h :: G) ⊢ _ => set (Hf := h) end.
  assert (Hfun : (Hf :: G) ⊢ fun_rel ((WF $0 ∧ WF $1) ∧ relw phi)).
  { apply fun_rel_intro. intros X Y Y'. simp.
    match goal with |- ?L ⊢ _ => set (Γ := L) end.
    assert (WX : Γ ⊢ WF X) by (eapply CE1, CE1, ctx2).
    assert (WY : Γ ⊢ WF Y) by (eapply CE2, CE1, ctx2).
    assert (WY' : Γ ⊢ WF Y') by (eapply CE2, CE1, ctx1).
    assert (Hf' : Γ ⊢ Hf) by (apply ctx3).
    unfold Hf in Hf'. apply (AllE X) in Hf'. cbn in Hf'. rewrite Mwf_inst, Mwf_up in Hf'.
    pose proof (IE Hf' WX) as H1. apply (AllE Y) in H1. cbn in H1. rewrite Mwf_up, Mwf_inst in H1.
    pose proof (IE H1 WY) as H2. apply (AllE Y') in H2. cbn in H2. rewrite Mwf_inst in H2.
    pose proof (IE H2 WY') as H3. rewrite !fr_norm in H3. cbn in H3. subsimpl_in H3.
    eapply IE; [eapply IE; [exact H3 |] |]; eapply CE2; auto. }
  apply AllI_named. intros X. rsimp. apply II.
  apply (rep_elim (X := X) (prv_weak1 _ (prv_weak1 _ H)) (prv_weak1 _ Hfun)). intros Z.
  apply (ExI Z). rsimp. apply CI.
  - apply WF_closure; [auto | auto |]. apply AllI_named. intros u. simp. apply II.
    eapply rep_in; [auto | auto |]. intros V. simp. eapply CE2, CE1. auto.
  - apply AllI_named. intros U. rsimp. rewrite rep_norm. apply II. apply CI.
    + apply II. eapply rep_in; [auto | auto |]. intros V. simp.
      apply (ExI V). rsimp. rewrite rep_inst_norm. apply CI; [eapply CE1, CE1; auto |].
      apply CI; [auto | eapply CE2; auto].
    + apply II. eapply ExE_named; [auto |]. intros V. rsimp. rewrite rep_inst_norm.
      eapply rep_out; [auto | eapply CE1, CE2; auto |]. simp.
      apply CI; [apply CI | eapply CE2, CE2; auto]; [eapply CE1; auto | auto].
Qed.

(* ** Universally closed instances *)

Lemma forall_times_bounded n k (theta : form) : bounded (k + n) theta -> bounded k (forall_times n theta).
Proof.
  induction n in k |- *; intros H.
  - now rewrite PeanoNat.Nat.add_0_r in H.
  - change (forall_times (S n) theta) with (∀ forall_times n theta). constructor.
    apply IHn. now rewrite PeanoNat.Nat.add_succ_r in H.
Qed.

Lemma forall_times_closed n (theta : form) : bounded n theta -> bounded 0 (forall_times n theta).
Proof. intros H. now apply forall_times_bounded. Qed.

Lemma rel_sep_ax G phi n : B0 <<= G -> forall_times n (ax_sep (relw phi)) el G ->
  bounded n (ax_sep (relw phi)) -> G ⊢ relw (forall_times n (ax_sep phi)).
Proof.
  intros HB H1 H2. rewrite <- (subst_var (relw (forall_times n (ax_sep phi)))).
  apply (rel_forall_times Mwf_bounded (L := B0 ++ [forall_times n (ax_sep (relw phi))])).
  - intros b sigma [Hb|[<-|[]]]%in_app_iff; [now apply B0_closed |].
    now apply bounded_0_subst, forall_times_closed.
  - intros Gamma tau HL. rewrite (rel_subst Mwf_bounded), ax_sep_subst. apply rel_sep_core.
    + intros a Ha. apply HL, in_app_iff. now left.
    + rewrite <- (rel_subst Mwf_bounded), <- ax_sep_subst.
      apply (subst_forall_prv (N := n)); [| exact H2]. apply Ctx, HL, in_app_iff. right. now left.
  - intros a [Ha|[<-|[]]]%in_app_iff; [now apply HB | exact H1].
Qed.

Definition repM (phi : form) : form := (WF $0 ∧ WF $1) ∧ relw phi.

Lemma repM_subst phi sigma : (repM phi)[up (up sigma)] = repM (phi[up (up sigma)]).
Proof. unfold repM. cbn. rewrite !WF_subst. cbn. now rewrite (rel_subst Mwf_bounded). Qed.

Lemma rel_rep_ax G phi n : B0 <<= G -> forall_times n (ax_rep (repM phi)) el G ->
  bounded n (ax_rep (repM phi)) -> G ⊢ relw (forall_times n (ax_rep phi)).
Proof.
  intros HB H1 H2. rewrite <- (subst_var (relw (forall_times n (ax_rep phi)))).
  apply (rel_forall_times Mwf_bounded (L := B0 ++ [forall_times n (ax_rep (repM phi))])).
  - intros b sigma [Hb|[<-|[]]]%in_app_iff; [now apply B0_closed |].
    now apply bounded_0_subst, forall_times_closed.
  - intros Gamma tau HL. rewrite (rel_subst Mwf_bounded), ax_rep_subst. apply rel_rep_core.
    + intros a Ha. apply HL, in_app_iff. now left.
    + fold (repM (phi[up (up tau)])). rewrite <- repM_subst, <- ax_rep_subst.
      apply (subst_forall_prv (N := n)); [| exact H2]. apply Ctx, HL, in_app_iff. right. now left.
  - intros a [Ha|[<-|[]]]%in_app_iff; [now apply HB | exact H1].
Qed.

(* ** Bounds *)

Lemma Mwf_bcomp k : bounded_comp (S k) Mwf.
Proof. apply bounded_comp_eq. eapply bounded_up; [apply Mwf_bounded | lia]. Qed.

Lemma rel_bcomp {ff} k (phi : form ff) : bounded_comp k (relw phi) <-> bounded_comp k phi.
Proof.
  induction phi in k |- *; cbn; try tauto.
  - rewrite IHphi1, IHphi2. tauto.
  - destruct q; cbn; rewrite IHphi; pose proof (Mwf_bcomp k); tauto.
Qed.

Lemma sep_bounded_rel n phi : bounded n (ax_sep phi) -> bounded n (ax_sep (relw phi)).
Proof.
  rewrite <- !bounded_comp_eq. unfold ax_sep. cbn. rewrite !(rel_subst Mwf_bounded), !rel_bcomp. tauto.
Qed.

Lemma WF_bcomp k j : j < k -> bounded_comp k (WF $j).
Proof.
  intros Hj. apply bounded_comp_eq. rewrite <- Mwf_inst. eapply subst_bounded_max; [| apply Mwf_bounded].
  intros [|i] Hi; [constructor; lia | lia].
Qed.

Lemma rep_bounded_rel n phi : bounded n (ax_rep phi) -> bounded n (ax_rep (repM phi)).
Proof.
  rewrite <- !bounded_comp_eq. unfold ax_rep, fun_rel, repM. cbn.
  rewrite !(rel_subst Mwf_bounded), !rel_bcomp, !WF_subst. cbn.
  pose proof (WF_bcomp (k := S (S (S n))) (j := 2) ltac:(lia)). pose proof (WF_bcomp (k := S (S (S n))) (j := 1) ltac:(lia)).
  pose proof (WF_bcomp (k := S (S (S n))) (j := 0) ltac:(lia)). pose proof (WF_bcomp (k := S (S (S (S n)))) (j := 0) ltac:(lia)).
  pose proof (WF_bcomp (k := S (S (S (S n)))) (j := 1) ltac:(lia)). tauto.
Qed.

(* ** All relativized axioms are provable from finitely many ZFc axioms *)

Lemma B0_ZFc b : b el B0 -> ZFc b.
Proof.
  intros Hb. apply in_app_iff in Hb as [Hb|Hb].
  - now apply ZFc_base.
  - repeat (destruct Hb as [<-|Hb]); try destruct Hb.
    + apply (ZFc_sep (n := 1)). bcomp.
    + apply (ZFc_sep (n := 1)). bcomp.
    + apply (ZFc_rep (n := 0)). bcomp.
    + apply (ZFc_sep (n := 0)). bcomp.
Qed.

Lemma ZFcReg_closed a : ZFcReg a -> bounded 0 a.
Proof.
  intros [phi H | ].
  - destruct H as [phi H | phi n Hb | phi n Hb].
    + unfold ZFeq', ZF' in H. repeat (destruct H as [<-|H]); try destruct H; bcomp.
    + now apply forall_times_closed.
    + now apply forall_times_closed.
  - bcomp.
Qed.

Lemma rel_axiom a : ZFcReg a ->
  exists L, (forall b, b el L -> ZFc b) /\ (forall G, L <<= G -> G ⊢ relw a).
Proof.
  intros [phi H | ].
  - destruct H as [phi H | phi n Hb | phi n Hb].
    + exists B0. split; [apply B0_ZFc |]. intros G HG. pose proof (B0_ZFeq HG) as HT.
      unfold ZFeq', ZF' in H. repeat (destruct H as [<-|H]); try destruct H.
      1-4, 6-7: apply rel_qf; [auto | cbn; tauto].
      * now apply rel_ext.
      * now apply rel_union.
      * now apply rel_power.
      * now apply rel_om1.
      * now apply rel_om2.
    + exists (B0 ++ [forall_times n (ax_sep (relw phi))]). split.
      * intros b [Hb'|[<-|[]]]%in_app_iff; [now apply B0_ZFc |]. apply ZFc_sep, sep_bounded_rel, Hb.
      * intros G HG. apply rel_sep_ax.
        -- intros a0 Ha0. apply HG, in_app_iff. now left.
        -- apply HG, in_app_iff. right. now left.
        -- apply sep_bounded_rel, Hb.
    + exists (B0 ++ [forall_times n (ax_rep (repM phi))]). split.
      * intros b [Hb'|[<-|[]]]%in_app_iff; [now apply B0_ZFc |]. apply ZFc_rep, rep_bounded_rel, Hb.
      * intros G HG. apply rel_rep_ax.
        -- intros a0 Ha0. apply HG, in_app_iff. now left.
        -- apply HG, in_app_iff. right. now left.
        -- apply rep_bounded_rel, Hb.
  - exists B0. split; [apply B0_ZFc |]. intros G HG. apply rel_reg, B0_ZFeq, HG.
Qed.

Lemma rel_axioms A : (forall a, a el A -> ZFcReg a) ->
  exists L, (forall b, b el L -> ZFc b) /\ (forall a, a el A -> forall G, L <<= G -> G ⊢ relw a).
Proof.
  induction A as [|a A IH]; intros HA.
  - exists []. split; [intros b [] | intros a' []].
  - destruct (rel_axiom (HA a (or_introl eq_refl))) as [L1 [H1 H2]].
    destruct IH as [L2 [H3 H4]]; [intros b Hb; apply HA; now right |].
    exists (L1 ++ L2). split.
    + intros b [Hb|Hb]%in_app_iff; auto.
    + intros b [<-|Hb] G HG.
      * apply H2. intros c Hc. apply HG, in_app_iff. now left.
      * apply H4; trivial. intros c Hc. apply HG, in_app_iff. now right.
Qed.

(* ** Main theorem *)

Theorem regularity_relcon : ZFcReg ⊢TC ⊥ -> ZFc ⊢TC ⊥.
Proof.
  intros [A [HA Hprv]].
  destruct (rel_axioms HA) as [L [HL1 HL2]].
  exists (B0 ++ L). split.
  - intros b [Hb|Hb]%in_app_iff; [now apply B0_ZFc | now apply HL1].
  - assert (H := rel_prv Mwf_bounded (p0 := class) B0_closed Mwf_funcs Hprv (Gamma := B0 ++ L) (sigma := fun _ => ∅)).
    apply H.
    + apply incl_appl, incl_refl.
    + intros k. rewrite Mwf_inst. apply WF_eset; [eapply B0_ZFeq | eapply B0_Wax]; auto.
    + intros a Ha. rewrite (rel_closed Mwf_bounded); [| apply ZFcReg_closed, HA, Ha].
      apply HL2; auto.
Qed.

(* ** Comparison with the library's theory ZFeq (schema instances as open formulas) *)

Lemma ZFc_proves_ZFeq_axiom {p : peirce} phi : ZFeq phi -> exists L, (forall b, b el L -> ZFc b) /\ L ⊢ phi.
Proof.
  intros [psi H | psi | psi].
  - exists [psi]. split; [intros b [<-|[]]; now apply ZFc_base | apply Ctx; now left].
  - destruct (find_bounded (ax_sep psi)) as [n Hn]. exists [forall_times n (ax_sep psi)]. split.
    + intros b [<-|[]]. now apply ZFc_sep.
    + assert (H : [forall_times n (ax_sep psi)] ⊢ forall_times n (ax_sep psi)) by (apply Ctx; now left).
      pose proof (subst_forall_prv H Hn var) as H'. now rewrite subst_var in H'.
  - destruct (find_bounded (ax_rep psi)) as [n Hn]. exists [forall_times n (ax_rep psi)]. split.
    + intros b [<-|[]]. now apply ZFc_rep.
    + assert (H : [forall_times n (ax_rep psi)] ⊢ forall_times n (ax_rep psi)) by (apply Ctx; now left).
      pose proof (subst_forall_prv H Hn var) as H'. now rewrite subst_var in H'.
Qed.

Lemma ZFeq_ZFc {p : peirce} phi : ZFeq ⊢T phi -> ZFc ⊢T phi.
Proof.
  intros [A [HA H]].
  assert (HL : exists L, (forall b, b el L -> ZFc b) /\ forall a, a el A -> L ⊢ a).
  { clear H. induction A as [|a A IH].
    - exists []. split; [intros b [] | intros a' []].
    - destruct (ZFc_proves_ZFeq_axiom (HA a (or_introl eq_refl))) as [L1 [H1 H2]].
      destruct IH as [L2 [H3 H4]]; [intros b Hb; apply HA; now right |].
      exists (L1 ++ L2). split.
      + intros b [Hb|Hb]%in_app_iff; auto.
      + intros b [<-|Hb]; [apply (Weak H2) | apply (Weak (H4 b Hb))]; auto. }
  destruct HL as [L [HL1 HL2]]. exists L. split; trivial. eapply prv_cut; eassumption.
Qed.
