(** Reverse consistency reduction, interpreting the ordinary core in L. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL Z_main.
From K230S Require Import KP0 KP0Use KPSeed KPrimeCore KPrimeTheory KQuotZFC
  KUpperCore KUpperReflect KUpperFinish.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma kprime_core_matrix_bounded n phi :
  closedf (forall_times n (kprime_core phi)) -> fb (S (S n)) phi.
Proof.
  intros H. apply fb_forall_times in H. rewrite Nat.add_0_r in H.
  unfold kprime_core, output_root in H. cbn in H.
  destruct H as [[Hphi Hmem] Hcl].
  eapply fb_ren_inv; [exact Hphi|]. intros k Hk. cbn in Hk |- *. lia.
Qed.

Definition core_holdsL (a : form) : Prop :=
  exists A, (forall b, In b A -> ZFR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
    incl Ax_L G -> incl A G -> G ⊢C rel Lform a.

Lemma KPrimeOrd_holdsL a : KPrimeOrd a -> core_holdsL a.
Proof.
  intros [psi Ha|phi n Hc].
  - apply axL_ZFR. apply ZFR_base. unfold ZF0base.
    unfold equality_axioms in Ha. cbn in Ha |- *. tauto.
  - exists (upper_core_insts n phi). split.
    + intros b Hb. exact (upper_core_insts_ok n phi b (kprime_core_matrix_bounded n phi Hc) Hb).
    + intros G HG HR HOm HL HI. apply (L_kprime_core G HG HR HOm HL n phi);
        [exact (kprime_core_matrix_bounded n phi Hc)|exact HI].
Qed.

Lemma KPrimeOrdIR_holdsL a : KPrimeOrdIR a -> core_holdsL a.
Proof.
  intros [Ha| ->]; [apply KPrimeOrd_holdsL, Ha|].
  exists []. split; [intros b []|]. intros G HG HR HOm HL _.
  unfold irreflexivity. cbn [rel]. fall x. fintro HxL. fintro Hxx.
  exact (no_self_g HG HR x Hxx).
Qed.

Theorem KPrimeOrdIR_standardZFC_inconsistent :
  KPrimeOrdIR ⊢TC ⊥ -> StandardZFC ⊢TC ⊥.
Proof.
  intros [A [HA DA]].
  destruct (MinZF.collect (R := fun B (a : form) =>
    forall G, incl ZF0base G -> In ax_reg' G -> In ax_om' G ->
      incl Ax_L G -> incl B G -> G ⊢C rel Lform a)
    (Q := ZFR) (A := A)) as [B [HB DB]].
  - intros B B' a Ha HBB G HG HR HOm HL HBG. apply Ha; try assumption.
    intros b Hb. apply HBG, HBB, Hb.
  - intros a Ha. apply KPrimeOrdIR_holdsL, HA, Ha.
  - set (G0 := ax_reg' :: ax_om' :: ZF0base ++ Ax_L ++ B).
    assert (HG : incl ZF0base G0) by
      (intros b Hb; right; right; apply in_or_app; now left).
    assert (HR : In ax_reg' G0) by now left.
    assert (HOm : In ax_om' G0) by (right; now left).
    assert (HL : incl Ax_L G0) by
      (intros b Hb; right; right; apply in_or_app; right; apply in_or_app; now left).
    assert (HBG : incl B G0) by
      (intros b Hb; right; right; apply in_or_app; right; apply in_or_app; now right).
    exists G0. split.
    + intros b [<-|[<-|Hb]].
      * left. now right.
      * left. left. right. reflexivity.
      * apply in_app_or in Hb as [Hb|Hb].
        -- left. left. left. now apply ZF0_base.
        -- apply in_app_or in Hb as [Hb|Hb].
           ++ destruct (Ax_L_ok b Hb) as [H|H]; [left; left|left; right]; assumption.
           ++ destruct (HB b Hb) as [H|H]; [left; left|left; right]; assumption.
    + apply (ExE_named (L_ex HG HR HOm HL)). intros x.
      change ⊥ with (rel Lform ⊥).
      apply (transfer Lform bounded_Lform A ⊥ _ x DA).
      * exact I.
      * intros a Ha. destruct (HA a Ha) as [Ha'| ->].
        -- now apply KPrimeOrd_closed.
        -- unfold closedf, irreflexivity. cbn. lia.
      * intros a Ha. apply weak_cons. apply (DB a Ha); assumption.
      * apply Ctx. now left.
Qed.

Theorem KPrimeOrdIR_standardZFC_equiconsistent :
  KPrimeOrdIR ⊢TC ⊥ <-> StandardZFC ⊢TC ⊥.
Proof.
  split; [apply KPrimeOrdIR_standardZFC_inconsistent|].
  intros H. apply (Weak_T (KPrimeOrd_standardZFC_inconsistent H)).
  intros a Ha. now left.
Qed.

Theorem KPrimeOrd_standardZFC_equiconsistent :
  KPrimeOrd ⊢TC ⊥ <-> StandardZFC ⊢TC ⊥.
Proof.
  split; [|apply KPrimeOrd_standardZFC_inconsistent].
  intros H. apply KPrimeOrdIR_standardZFC_inconsistent.
  apply (Weak_T H). intros a Ha. now left.
Qed.
