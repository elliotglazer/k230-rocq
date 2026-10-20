(** * Z_ac: the axiom of choice holds in L.

    ZF ⊢ "every x ∈ L_α has a choice set" (Z_wo) relativizes to L (Z_rel.transfer, with the
    axioms of the derivation relativized by Z_axL); (L_α)^L = L_α because [LL] is Sigma and
    ZF ⊢ ∀α ∃!Y LL α Y (upward absoluteness + uniqueness). *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldRegCon Require Import Rel.
From OldRegCon Require MinZF.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_sg Z_refl Z_axL Z_wo.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** The two ZF theorems that are relativized *)
Definition T1 : form := ∀ (Ord0 $0 → ∃ LL $1 $0).
Definition T2 : form := ∀ (Ord0 $0 → ∀ (LL $1 $0 → ∀ ($0 ∈' $1 → ACmat $0))).

Lemma T1_closed : closedf T1.
Proof. unfold closedf. fbcomp. Qed.
Lemma T2_closed : closedf T2.
Proof. unfold closedf. fbcomp. Qed.

(** the axioms of the derivations *)
Definition A0 : list form := ax_reg' :: ax_om' :: ZF0base ++ Ax_wo.

Lemma A0_ZF : incl ZF0base A0.
Proof. intros b Hb. right. right. apply in_app_iff. now left. Qed.
Lemma A0_reg : In ax_reg' A0.
Proof. now left. Qed.
Lemma A0_om : In ax_om' A0.
Proof. right. now left. Qed.
Lemma A0_wo : incl Ax_wo A0.
Proof. intros b Hb. right. right. apply in_app_iff. now right. Qed.
Lemma A0_L : incl Ax_L A0.
Proof. apply Ax_wo_L, A0_wo. Qed.

Lemma A0_ZFR a : In a A0 -> ZFR a.
Proof.
  intros [<- | [<- | Ha]]; [apply ZFR_reg | apply ZFR_om |].
  apply in_app_iff in Ha as [Ha|Ha]; [now apply ZFR_base | now apply Ax_wo_ok].
Qed.

Lemma ZFR_closed' a : ZFR a -> closedf a.
Proof.
  intros [[[phi H | phi n H | phi n H] | ->] | ->].
  - now apply ZF0base_closed.
  - exact H.
  - exact H.
  - apply ax_om'_closed.
  - cbn. lia.
Qed.

Lemma T1_prv : A0 ⊢C T1.
Proof.
  pose proof A0_ZF as HG. pose proof A0_reg as HR. pose proof A0_om as HOm. pose proof A0_L as HL.
  unfold T1. apply AllI_named. intros a. simp. fintro H. eapply LL_ex; eassumption.
Qed.

Lemma T2_prv : A0 ⊢C T2.
Proof.
  pose proof A0_ZF as HG. pose proof A0_reg as HR. pose proof A0_om as HOm. pose proof A0_wo as HW.
  unfold T2. eapply wo_choice; eassumption.
Qed.

(** ** Relativized reasoning about [rel Lform] *)
Lemma relsub (phi : form) sg : (rel Lform phi)[sg] = rel Lform (phi[sg]).
Proof. apply (rel_subst bounded_Lform). Qed.

Lemma rel_allE G (phi : form) t : G ⊢C rel Lform (∀ phi) -> G ⊢C InL t -> G ⊢C rel Lform (phi[t..]).
Proof.
  intros H Ht. change (G ⊢C ∀ (Lform → rel Lform phi)) in H. apply (AllE t) in H.
  change (G ⊢C Lform[t..] → (rel Lform phi)[t..]) in H. rewrite relsub in H. exact (IE H Ht).
Qed.

Lemma rel_impE G (phi psi : form) : G ⊢C rel Lform (phi → psi) -> G ⊢C rel Lform phi -> G ⊢C rel Lform psi.
Proof. intros H1 H2. exact (IE H1 H2). Qed.

Lemma rel_exE G (phi psi : form) : G ⊢C rel Lform (∃ phi) ->
  (forall t, ((InL t ∧ rel Lform (phi[t..])) :: G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros H H'. change (G ⊢C ∃ (Lform ∧ rel Lform phi)) in H. apply (ExE_named H). intros t.
  change (((Lform[t..] ∧ (rel Lform phi)[t..]) :: G) ⊢C psi). rewrite relsub. apply H'.
Qed.
Ltac rex H y Hy := apply (rel_exE _ _ _ H); intros y; ctx_push Hy; try clear H.

Lemma Ord0_L G a : G ⊢C TransC Lform -> G ⊢C InL a -> G ⊢C Ord0 a -> G ⊢C rel Lform (Ord0 a).
Proof.
  intros HT Ha H.
  pose proof (D0_abs Lform bounded_Lform (Ord0 $0) D0_Ord0 G (fun _ => a) HT (fun _ => Ha)) as H'.
  rewrite relsub, Ord0_subst in H'. exact (iff_r _ _ _ H' H).
Qed.

Lemma LL_up G a y : G ⊢C TransC Lform -> G ⊢C InL a -> G ⊢C InL y -> G ⊢C rel Lform (LL a y) -> G ⊢C LL a y.
Proof.
  intros HT Ha Hy H.
  assert (Hs : forall k, G ⊢C Lform[((a .: y .: fun _ => a) k)..]) by (intros [|[|k]]; assumption).
  pose proof (Sg_up Lform bounded_Lform (LL $0 $1) Sg_LL G _ HT Hs) as H'.
  rewrite relsub, LL_subst in H'. exact (H' H).
Qed.

(** ** AC in L *)
Section AC.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma ac_in_L x : G ⊢C rel Lform T1 -> G ⊢C rel Lform T2 -> G ⊢C InL x -> G ⊢C rel Lform (ACmat x).
Proof.
  intros H1 H2 HxL. pose proof HxL as Hx. rewrite InL_eq in Hx.
  fex Hx a Ha. fex Ha Y HY. fdestr HY HY1 HY3. fdestr HY1 HOa HLY.
  fassert HT : (TransC Lform). { eapply L_transC; eassumption. }
  fassert HaL : (InL a). { eapply L_ord; eassumption. }
  fassert HOaL : (rel Lform (Ord0 a)). { now apply Ord0_L. }
  (* (L_a)^L exists *)
  pose proof (rel_allE _ _ a H1 HaL) as H1a. unfold T1 in H1a.
  replace ((Ord0 $0 → ∃ LL $1 $0)[a..]) with (Ord0 a → ∃ LL a`[↑] $0) in H1a by (simp; reflexivity).
  pose proof (rel_impE _ _ _ H1a HOaL) as H1b. clear H1a.
  rex H1b Y' HY0. fdestr HY0 HY'L HY'.
  replace ((LL a`[↑] $0)[Y'..]) with (LL a Y') in HY' by (simp; reflexivity).
  fassert HLY' : (LL a Y'). { now apply LL_up. }
  fassert HE : (Y ≡' Y'). { eapply LL_unique; eassumption. }
  fassert HxY' : (x ∈' Y'). { eapply elem_cong; [eassumption | apply eq_refl'; eassumption | exact HE | exact HY3]. }
  (* T2 at a, Y', x *)
  pose proof (rel_allE _ _ a H2 HaL) as H2a. unfold T2 in H2a.
  replace ((Ord0 $0 → ∀ (LL $1 $0 → ∀ ($0 ∈' $1 → ACmat $0)))[a..])
    with (Ord0 a → ∀ (LL a`[↑] $0 → ∀ ($0 ∈' $1 → ACmat $0))) in H2a by (simp; reflexivity).
  pose proof (rel_impE _ _ _ H2a HOaL) as H2b. clear H2a.
  pose proof (rel_allE _ _ Y' H2b HY'L) as H2c. clear H2b.
  replace ((LL a`[↑] $0 → ∀ ($0 ∈' $1 → ACmat $0))[Y'..])
    with (LL a Y' → ∀ ($0 ∈' Y'`[↑] → ACmat $0)) in H2c by (simp; reflexivity).
  pose proof (rel_impE _ _ _ H2c HY') as H2d. clear H2c.
  pose proof (rel_allE _ _ x H2d HxL) as H2e. clear H2d.
  replace (($0 ∈' Y'`[↑] → ACmat $0)[x..]) with (x ∈' Y' → ACmat x) in H2e by (simp; reflexivity).
  exact (rel_impE _ _ _ H2e HxY').
Qed.
End AC.

Lemma rel_T G T : incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G ->
  (forall a, In a A0 -> G ⊢C rel Lform a) -> A0 ⊢C T -> closedf T -> G ⊢C rel Lform T.
Proof.
  intros HG HR HOm HL HA HT HTc.
  assert (HLe : G ⊢C ∃ Lform) by (eapply L_ex; eassumption). apply (ExE_named HLe). intros t.
  apply (transfer Lform bounded_Lform A0 T _ t HT HTc).
  - intros a Ha. now apply ZFR_closed', A0_ZFR.
  - intros a Ha. apply weak_cons. now apply HA.
  - apply Ctx. now left.
Qed.

Theorem acL_ex : exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G -> incl A G -> G ⊢C rel Lform ax_ac.
Proof.
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
               incl Ax_L G -> incl L G -> G ⊢C rel Lform a) (Q := ZFR) (A := A0)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5. apply Hx; trivial. intros b Hb. now apply H5, HL.
  - intros a Ha. now apply axL_ZFR, A0_ZFR.
  - exists L. split; [exact HL1|]. intros G HG HR HOm HL HLG.
    assert (HA : forall a, In a A0 -> G ⊢C rel Lform a) by (intros a Ha; now apply HL2).
    pose proof (rel_T G T1 HG HR HOm HL HA T1_prv T1_closed) as H1.
    pose proof (rel_T G T2 HG HR HOm HL HA T2_prv T2_closed) as H2.
    change (G ⊢C ∀ (Lform → rel Lform (ACmat $0))). apply AllI_named. intros x.
    change (G ⊢C Lform[x..] → (rel Lform (ACmat $0))[x..]). rewrite relsub, ACmat_subst. cbn [subst_term]. apply II.
    apply ac_in_L.
    + now apply incl_cons_r.
    + now apply in_cons_r.
    + now apply in_cons_r.
    + now apply incl_cons_r.
    + now apply weak_cons.
    + now apply weak_cons.
    + apply Ctx. now left.
Qed.

