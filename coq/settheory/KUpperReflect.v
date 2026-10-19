(** Selector reflection and common bounds in L.
    A single reflected formula supplies both subset and matrix-witness
    closure, after finite parameter hosting in an earlier level. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL.
From K230S Require Import KP0Use KPRaw KPrimeCore KUpperCore.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Arguments Lform : simpl never.
#[local] Arguments InL : simpl never.
#[local] Hint Rewrite Lform_up Lform_inst InL_subst relL_subst relS_subst' : fsub.

Ltac fconv_h H :=
  match type of H with _ ⊢C ?f => match goal with |- _ ⊢C ?g =>
    replace g with f by (repeat (first [reflexivity | form_subst_eq | progress f_equal]));
    exact H end end.
Ltac fmp_conv H H' :=
  match type of H with ?G ⊢C ?A → _ =>
    let T := fresh in assert (T : G ⊢C A) by fconv_h H'; fmp H T; clear T end.

Definition witness_theta (phi : form) : form :=
  ($2 ∈' $3 ∧ phi[$0 .: $1 .: (fun k => $(4+k))]) ∨
  ((¬ ($2 ∈' $3)) ∧ ∃ phi[$0 .: $2 .: (fun k => $(5+k))]).

Definition L_request (phi : form) (sg : nat -> term) (p Y : term) : form :=
  (∃ (InL $0 ∧ rel Lform (phi[$0 .: p`[↑] .: (fun k => (sg k)`[↑])]))) →
  ∃ ($0 ∈' Y`[↑] ∧ rel Lform (phi[$0 .: p`[↑] .: (fun k => (sg k)`[↑])])).

Lemma fb_witness_theta n phi : fb (S (S n)) phi -> fb (4+n) (witness_theta phi).
Proof.
  intros H. unfold witness_theta. cbn. repeat split; try lia;
    (eapply fb_subst; [exact H|intros [|[|k]] Hk; cbn; lia]).
Qed.

Definition upper_cp_zeta : form := ∀ ((∀ ($0 ∈' $1 → $0 ∈' $2)) → $0 ∈' $2).
Definition upper_cp_rho : form := ∃ (∀ ((∀ ($0 ∈' $1 → $0 ∈' $3)) → $0 ∈' $1)).
Definition upper_cp_theta : form :=
  ($2 ∈' $3 ∧ upper_cp_rho) ∨ ((¬ ($2 ∈' $3)) ∧ upper_cp_zeta).

Lemma fb_upper_cp_theta n : fb (4+n) upper_cp_theta.
Proof. unfold upper_cp_theta, upper_cp_rho, upper_cp_zeta. fbcomp. Qed.

Definition reflection_pair (A B : form) : form :=
  ($0 ∈' $1 ∧ A[fun k => $(2+k)]) ∨
  ((¬ ($0 ∈' $1)) ∧ B[fun k => $(2+k)]).

Lemma fb_reflection_pair m A B : fb m A -> fb m B -> fb (2+m) (reflection_pair A B).
Proof.
  intros HA HB. unfold reflection_pair. cbn. repeat split; try lia;
    (eapply fb_subst; [eassumption|intros k Hk; cbn; lia]).
Qed.

Lemma reflected_left G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) m A B sg beta Y s t :
  fb m A -> fb m B ->
  G ⊢C Refl (2+m) (reflection_pair A B) beta -> G ⊢C LL beta Y ->
  G ⊢C s ∈' t -> G ⊢C s ∈' Y -> G ⊢C t ∈' Y ->
  (forall k, k<m -> G ⊢C sg k ∈' Y) ->
  G ⊢C rel Lform (A[sg]) ↔ relS Y (A[sg]).
Proof.
  intros HA HB HRf HY Hst Hs Ht Hsg.
  fassert R : (rel Lform ((reflection_pair A B)[s .: t .: sg]) ↔
    relS Y ((reflection_pair A B)[s .: t .: sg])).
  { eapply (refl_use HG HR HOm HL (2+m) (reflection_pair A B) beta Y (s .: t .: sg));
      [exact (fb_reflection_pair m A B HA HB)|exact HRf|exact HY|].
    intros [|[|k]] Hk; cbn; [exact Hs|exact Ht|apply Hsg; lia]. }
  unfold reflection_pair in R. simp_in R.
  fsplit; fintro H.
  - fassert HP : (rel Lform ((reflection_pair A B)[s .: t .: sg])).
    { unfold reflection_pair. simp. fleft. fsplit; [exact Hst|fconv_h H]. }
    unfold reflection_pair in HP. simp_in HP.
    fhave T : (iff_l _ _ _ R HP). fcases T T1 T2.
    + fdestr T1 Hunused Hout. fconv_h Hout.
    + fdestr T2 Hbad Hunused. fabsurd. exact (IE Hbad Hst).
  - fassert HP : (relS Y ((reflection_pair A B)[s .: t .: sg])).
    { unfold reflection_pair. simp. fleft. fsplit; [exact Hst|fconv_h H]. }
    unfold reflection_pair in HP. simp_in HP.
    fhave T : (iff_r _ _ _ R HP). fcases T T1 T2.
    + fdestr T1 Hunused Hout. fconv_h Hout.
    + fdestr T2 Hbad Hunused. fabsurd. exact (IE Hbad Hst).
Qed.

Lemma reflected_right G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) m A B sg beta Y s :
  fb m A -> fb m B ->
  G ⊢C Refl (2+m) (reflection_pair A B) beta -> G ⊢C LL beta Y ->
  G ⊢C s ∈' Y -> (forall k, k<m -> G ⊢C sg k ∈' Y) ->
  G ⊢C rel Lform (B[sg]) ↔ relS Y (B[sg]).
Proof.
  intros HA HB HRf HY Hs Hsg.
  fassert Hns : (¬ (s ∈' s)). { fintro Hss. exact (no_self_g HG HR s Hss). }
  fassert R : (rel Lform ((reflection_pair A B)[s .: s .: sg]) ↔
    relS Y ((reflection_pair A B)[s .: s .: sg])).
  { eapply (refl_use HG HR HOm HL (2+m) (reflection_pair A B) beta Y (s .: s .: sg));
      [exact (fb_reflection_pair m A B HA HB)|exact HRf|exact HY|].
    intros [|[|k]] Hk; cbn; [exact Hs|exact Hs|apply Hsg; lia]. }
  unfold reflection_pair in R. simp_in R.
  fsplit; fintro H.
  - fassert HP : (rel Lform ((reflection_pair A B)[s .: s .: sg])).
    { unfold reflection_pair. simp. fright. fsplit; [exact Hns|fconv_h H]. }
    unfold reflection_pair in HP. simp_in HP.
    fhave T : (iff_l _ _ _ R HP). fcases T T1 T2.
    + fdestr T1 Hbad Hunused. fabsurd. exact (IE Hns Hbad).
    + fdestr T2 Hunused Hout. fconv_h Hout.
  - fassert HP : (relS Y ((reflection_pair A B)[s .: s .: sg])).
    { unfold reflection_pair. simp. fright. fsplit; [exact Hns|fconv_h H]. }
    unfold reflection_pair in HP. simp_in HP.
    fhave T : (iff_r _ _ _ R HP). fcases T T1 T2.
    + fdestr T1 Hbad Hunused. fabsurd. exact (IE Hns Hbad).
    + fdestr T2 Hunused Hout. fconv_h Hout.
Qed.

Lemma reflected_witness_request G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi other sg beta Y s t p :
  fb (S (S n)) phi ->
  fb (4+n) other ->
  G ⊢C Refl (2+(4+n)) (reflection_pair (witness_theta phi) other) beta ->
  G ⊢C LL beta Y ->
  G ⊢C s ∈' t -> G ⊢C s ∈' Y -> G ⊢C t ∈' Y -> G ⊢C p ∈' Y ->
  (forall k, k<n -> G ⊢C sg k ∈' Y) ->
  G ⊢C L_request phi sg p Y.
Proof.
  intros Hfb Hother HRf HY Hst Hs Ht Hp Hparams.
  pose proof (fb_witness_theta n phi Hfb) as Htheta.
  unfold L_request. fintro Hsome.
  fassert R1 : (rel Lform ((witness_theta phi)[p .: p .: p .: p .: sg]) ↔
    relS Y ((witness_theta phi)[p .: p .: p .: p .: sg])).
  { eapply (reflected_left _ HG HR HOm HL _ _ other _ _ _ s t);
      [exact Htheta|exact Hother|exact HRf|exact HY|exact Hst|exact Hs|exact Ht|].
    intros [|[|[|[|k]]]] Hk; cbn; try exact Hp. apply Hparams. lia. }
  fassert L1 : (rel Lform ((witness_theta phi)[p .: p .: p .: p .: sg])).
  { unfold witness_theta. simp. fright. fsplit.
    - fintro Hpp. exact (no_self_g HG HR p Hpp).
    - fconv_h Hsome. }
  fhave S1 : (iff_l _ _ _ R1 L1). unfold witness_theta in S1. simp_in S1.
  fcases S1 S1a S1b.
  - fdestr S1a Hpp Hunused. fabsurd. exact (no_self_g HG HR p Hpp).
  - fdestr S1b Hnot Hfound. fex Hfound y Hy. fdestr Hy HyY Hyphi.
    fassert R2 : (rel Lform ((witness_theta phi)[y .: p .: s .: t .: sg]) ↔
      relS Y ((witness_theta phi)[y .: p .: s .: t .: sg])).
    { eapply (reflected_left _ HG HR HOm HL _ _ other _ _ _ s t);
        [exact Htheta|exact Hother|exact HRf|exact HY|exact Hst|exact Hs|exact Ht|].
      intros [|[|[|[|k]]]] Hk; cbn;
        [exact HyY|exact Hp|exact Hs|exact Ht|apply Hparams; lia]. }
    fassert S2 : (relS Y ((witness_theta phi)[y .: p .: s .: t .: sg])).
    { unfold witness_theta. simp. fleft. fsplit; [exact Hst|fconv_h Hyphi]. }
    fhave L2 : (iff_r _ _ _ R2 S2). unfold witness_theta in L2. simp_in L2.
    fcases L2 L2a L2b.
    + fdestr L2a Hunused Hphi. fexists y. fsplit; [exact HyY|fconv_h Hphi].
    + fdestr L2b Hnst Hunused. fabsurd. exact (IE Hnst Hst).
Qed.

Lemma reflected_power_container G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi beta Y s t x :
  fb (S (S n)) phi -> incl powL_insts G ->
  G ⊢C Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) beta ->
  G ⊢C LL beta Y ->
  G ⊢C s ∈' t -> G ⊢C s ∈' Y -> G ⊢C t ∈' Y ->
  G ⊢C InL x -> G ⊢C x ∈' Y ->
  G ⊢C ∃ ($0 ∈' Y`[↑] ∧ rel Lform (upper_cp_zeta[x`[↑] .: $0 .: var])).
Proof.
  intros Hphi Hpw HRf HY Hst Hs Ht HxL HxY.
  pose proof (fb_witness_theta n phi Hphi) as Htheta.
  pose proof (axL_power HG HR HOm HL Hpw) as Hpow.
  unfold ax_power' in Hpow. cbn [rel] in Hpow. finst Hpow x. fmp Hpow HxL.
  fex Hpow P HP. fdestr HP HPL HPp. rewrite rel_is_power in HPp.
  fassert Hrho : (rel Lform (upper_cp_rho[x..])).
  { unfold upper_cp_rho. simp. fexists P. fsplit; [exact HPL|].
    fall z. fintro HzL. fintro Hsub. finst HPp z. fmp HPp HzL.
    apply (iff_r _ _ _ HPp). rewrite rel_sub'. fconv_h Hsub. }
  fassert R1 : (rel Lform (upper_cp_theta[x .: x .: s .: t .: (fun _ => x)]) ↔
    relS Y (upper_cp_theta[x .: x .: s .: t .: (fun _ => x)])).
  { eapply (reflected_right _ HG HR HOm HL _ (witness_theta phi) _ _ _ _ s);
      [exact Htheta|apply fb_upper_cp_theta|exact HRf|exact HY|exact Hs|].
    intros [|[|[|[|k]]]] Hk; cbn; [exact HxY|exact HxY|exact Hs|exact Ht|exact HxY]. }
  fassert L1 : (rel Lform (upper_cp_theta[x .: x .: s .: t .: (fun _ => x)])).
  { unfold upper_cp_theta. simp. fleft. fsplit; [exact Hst|fconv_h Hrho]. }
  fhave S1 : (iff_l _ _ _ R1 L1). unfold upper_cp_theta in S1. simp_in S1.
  fcases S1 S1a S1b.
  - fdestr S1a Hunused Hr. unfold upper_cp_rho in Hr. simp_in Hr.
    fex Hr W HW. fdestr HW HWY HWz.
    fassert R2 : (rel Lform (upper_cp_theta[x .: W .: x .: x .: (fun _ => x)]) ↔
      relS Y (upper_cp_theta[x .: W .: x .: x .: (fun _ => x)])).
    { eapply (reflected_right _ HG HR HOm HL _ (witness_theta phi) _ _ _ _ s);
        [exact Htheta|apply fb_upper_cp_theta|exact HRf|exact HY|exact Hs|].
      intros [|[|[|[|k]]]] Hk; cbn; [exact HxY|exact HWY|exact HxY|exact HxY|exact HxY]. }
    fassert S2 : (relS Y (upper_cp_theta[x .: W .: x .: x .: (fun _ => x)])).
    { unfold upper_cp_theta, upper_cp_zeta. simp. fright. fsplit.
      - fintro Hxx. exact (no_self_g HG HR x Hxx).
      - fconv_h HWz. }
    fhave L2 : (iff_r _ _ _ R2 S2). unfold upper_cp_theta in L2. simp_in L2.
    fcases L2 L2a L2b.
    + fdestr L2a Hxx Hunused2. fabsurd. exact (no_self_g HG HR x Hxx).
    + fdestr L2b Hunused2 Hzeta. fexists W. fsplit; [exact HWY|fconv_h Hzeta].
  - fdestr S1b Hnst Hunused. fabsurd. exact (IE Hnst Hst).
Qed.

Lemma reflected_subset_closed G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi beta Y s t :
  fb (S (S n)) phi -> incl powL_insts G ->
  G ⊢C Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) beta ->
  G ⊢C Ord0 beta -> G ⊢C LL beta Y ->
  G ⊢C s ∈' t -> G ⊢C s ∈' Y -> G ⊢C t ∈' Y ->
  G ⊢C rel Lform (subset_closed Y).
Proof.
  intros Hphi Hpw HRf Hbo HY Hst Hs Ht.
  fassert HT : (Trans0 Y). { eapply LL_trans with (a:=beta); eassumption. }
  unfold subset_closed. simp. fall x. fintro HxL. fintro HxY.
  fall z. fintro HzL. fintro Hsub.
  fobtain (reflected_power_container _ HG HR HOm HL n phi beta Y s t x
    Hphi Hpw HRf HY Hst Hs Ht HxL HxY) as W HW.
  fdestr HW HWY HWz. unfold upper_cp_zeta in HWz. simp_in HWz.
  finst HWz z. fmp HWz HzL.
  match type of HWz with _ ⊢C ?A → _ => fassert HS : A end.
  { unfold raw_subset in Hsub. fconv_h Hsub. }
  fmp HWz HS. exact (trans0_use Y W z HT HWY HWz).
Qed.

Fixpoint tuple_in (n : nat) (sg : nat -> term) (Y : term) : form :=
  match n with
  | 0 => ⊥ → ⊥
  | S m => sg m ∈' Y ∧ tuple_in m sg Y
  end.

Lemma tuple_in_subst n sg Y tau :
  (tuple_in n sg Y)[tau] = tuple_in n (fun k => (sg k)`[tau]) Y`[tau].
Proof. revert sg Y tau. induction n; intros; cbn; [reflexivity|now rewrite IHn]. Qed.
#[local] Hint Rewrite tuple_in_subst : fsub.

Lemma tuple_in_ext n sg tau Y :
  (forall k, k < n -> sg k = tau k) -> tuple_in n sg Y = tuple_in n tau Y.
Proof.
  induction n as [|n IH]; intros H; cbn; [reflexivity|].
  rewrite (H n ltac:(lia)). f_equal. apply IH. intros k Hk. apply H. lia.
Qed.

Ltac tuple_convert H :=
  repeat rewrite tuple_in_subst in H;
  match type of H with _ ⊢C ?F => match goal with |- _ ⊢C ?T =>
    let E := fresh "Etuple" in assert (E : T = F);
    [apply tuple_in_ext; intros k Hk; autorewrite with fsub; reflexivity
    |rewrite E; exact H] end end.

Lemma tuple_in_get n : forall G sg Y k, k<n -> G ⊢C tuple_in n sg Y -> G ⊢C sg k ∈' Y.
Proof.
  induction n; intros G sg Y k Hk H; [lia|]. cbn in H.
  destruct (Nat.eq_dec k n) as [->|Hne]; [exact (CE1 H)|].
  eapply IHn; [lia|exact (CE2 H)].
Qed.

Lemma tuple_in_mono n : forall G sg Y Z,
  G ⊢C Sub0 Y Z -> G ⊢C tuple_in n sg Y -> G ⊢C tuple_in n sg Z.
Proof.
  induction n; intros G sg Y Z HS H; cbn in H |- *.
  - exact H.
  - fsplit.
    + exact (sub0_use Y Z (sg n) HS (CE1 H)).
    + exact (IHn _ sg Y Z HS (CE2 H)).
Qed.

Lemma tuple_L_level n : forall G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) sg p,
  G ⊢C InL p -> (forall k, k<n -> G ⊢C InL (sg k)) ->
  G ⊢C ∃ ∃ ((Ord0 $1 ∧ LL $1 $0) ∧
    (p`[↑]`[↑] ∈' $0 ∧ tuple_in n (fun k => (sg k)`[↑]`[↑]) $0)).
Proof.
  induction n; intros G HG HR HOm HL sg p Hp Hsg.
  - pose proof Hp as H. rewrite InL_eq in H. fex H beta HB. fex HB Y HY.
    fdestr HY HY1 HpY. fdestr HY1 Hbo HBY.
    fexists beta. fexists Y. fsplit; [fsplit; assumption|].
    fsplit; [exact HpY|]. cbn. fintro Hfalse. exact Hfalse.
  - fobtain (IHn G HG HR HOm HL sg p Hp ltac:(intros k Hk; apply Hsg; lia)) as beta HB.
    fex HB Y HY. fdestr HY HY1 HY2. fdestr HY1 Hbo HBY. fdestr HY2 HpY Htuple.
    fobtain (L_above HG HR HOm HL (sg n) beta (Hsg n ltac:(lia)) Hbo) as gamma HC.
    fex HC Yn HZ. fdestr HZ HZ1 HnZ. fdestr HZ1 HZ2 HGZ. fdestr HZ2 Hgo Hbg.
    fassert Hsub : (Sub0 Y Yn).
    { eapply LL_sub with (a:=gamma) (b:=beta); eassumption. }
    fexists gamma. fexists Yn. fsplit; [fsplit; assumption|]. fsplit.
    + exact (sub0_use Y Yn p Hsub HpY).
    + cbn. fsplit; [exact HnZ|].
      fassert HT : (tuple_in n sg Y). { tuple_convert Htuple. }
      pose proof (tuple_in_mono n _ sg Y Yn Hsub HT) as T. tuple_convert T.
Qed.

Lemma reflected_witness_closed G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi sg beta Y s t :
  fb (S (S n)) phi ->
  G ⊢C Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) beta ->
  G ⊢C Ord0 beta -> G ⊢C LL beta Y ->
  G ⊢C s ∈' t -> G ⊢C s ∈' Y -> G ⊢C t ∈' Y ->
  (forall k, k<n -> G ⊢C sg k ∈' Y) ->
  G ⊢C rel Lform (witness_closed phi sg Y).
Proof.
  intros Hphi HRf Hbo HY Hst Hs Ht Hparams.
  unfold witness_closed, matrix_request. simp.
  fall p. fintro HpL. fintro HpY. fintro Hsome.
  fassert R : (L_request phi sg p Y).
  { apply (reflected_witness_request _ HG HR HOm HL n phi upper_cp_theta sg beta Y s t p).
    - exact Hphi.
    - apply fb_upper_cp_theta.
    - exact HRf.
    - exact HY.
    - exact Hst.
    - exact Hs.
    - exact Ht.
    - exact HpY.
    - exact Hparams. }
  unfold L_request in R. fmp_conv R Hsome.
  fex R y Hy. fdestr Hy HyY Hyphi. fexists y. fsplit.
  - eapply InL_intro; eassumption.
  - fsplit; [exact HyY|fconv_h Hyphi].
Qed.

Definition L_bound (phi : form) (sg : nat -> term) (a x Y : term) : form :=
  (InL Y ∧ a ∈' Y) ∧
  (x ∈' Y ∧ (rel Lform (subset_closed Y) ∧ rel Lform (witness_closed phi sg Y))).

Definition upper_insts n phi : list form :=
  powL_insts ++ refl_insts (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta).

Lemma upper_insts_ok n phi a : fb (S (S n)) phi -> In a (upper_insts n phi) -> ZFR a.
Proof.
  intros Hphi Ha. apply in_app_or in Ha as [Ha|Ha].
  - exact (oc_insts_ok 0 Qpow a fb_Qpow Ha).
  - apply (refl_insts_ok (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) a);
      [|exact Ha]. apply fb_reflection_pair.
    + exact (fb_witness_theta n phi Hphi).
    + apply fb_upper_cp_theta.
Qed.

Lemma L_bound_exists G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi sg a x :
  fb (S (S n)) phi -> incl (upper_insts n phi) G ->
  G ⊢C InL a -> G ⊢C InL x -> (forall k, k<n -> G ⊢C InL (sg k)) ->
  G ⊢C ∃ L_bound phi (fun k => (sg k)`[↑]) a`[↑] x`[↑] $0.
Proof.
  intros Hphi HI Ha Hx Hsg.
  assert (Hpw : incl powL_insts G) by
    (intros f Hf; apply HI, in_or_app; now left).
  assert (Hri : incl (refl_insts (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta)) G) by
    (intros f Hf; apply HI, in_or_app; now right).
  assert (Hfb : fb (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta)) by
    (apply fb_reflection_pair; [exact (fb_witness_theta n phi Hphi)|apply fb_upper_cp_theta]).
  fobtain (tuple_L_level (S n) G HG HR HOm HL (x .: sg) a Ha
    ltac:(intros [|k] Hk; cbn; [exact Hx|apply Hsg; lia])) as beta HB.
  fex HB Y HY. fdestr HY HY1 HY2. fdestr HY1 Hbo HBY. fdestr HY2 HaY Htuple.
  fassert HTuple : (tuple_in (S n) (x .: sg) Y).
  { cbn. fsplit; [exact (CE1 Htuple)|].
    pose proof (CE2 Htuple) as Htail. tuple_convert Htail. }
  fassert Hr : (∃ ((Ord0 $0 ∧ beta`[↑] ∈' $0) ∧
    Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) $0)).
  { eapply reflection; eassumption. }
  fex_raw Hr gamma HC. fdestr HC HC1 HRf. fdestr HC1 Hgo Hbg.
  simp_in Hgo. simp_in Hbg.
  fassert HRf' : (Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) gamma).
  { replace (Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) gamma)
      with ((Refl (2+(4+n)) (reflection_pair (witness_theta phi) upper_cp_theta) $0)[gamma..]).
    - exact HRf.
    - rewrite (Refl_subst _ _ _ _ Hfb). reflexivity. }
  fobtain (LL_ex HG HR HOm HL gamma Hgo) as Yn HGZ.
  fassert Hmono : (Y ∈' Yn ∧ Sub0 Y Yn).
  { eapply LL_mono with (a:=gamma) (b:=beta); eassumption. }
  fdestr Hmono HYZ Hsub.
  fassert HaZ : (a ∈' Yn). { exact (sub0_use Y Yn a Hsub HaY). }
  fassert HTZ : (tuple_in (S n) (x .: sg) Yn).
  { exact (tuple_in_mono (S n) _ (x .: sg) Y Yn Hsub HTuple). }
  fassert HxZ : (x ∈' Yn). { exact (tuple_in_get (S n) _ (x .: sg) Yn 0 ltac:(lia) HTZ). }
  fexists Yn. unfold L_bound. simp. fsplit; [fsplit|fsplit].
  - eapply L_LL; eassumption.
  - exact HaZ.
  - exact HxZ.
  - fsplit.
    + eapply reflected_subset_closed with (n:=n) (phi:=phi) (beta:=gamma) (s:=a) (t:=Y); eassumption.
    + fassert HW : (rel Lform (witness_closed phi sg Yn)).
      { eapply reflected_witness_closed with (n:=n) (beta:=gamma) (s:=a) (t:=Y); try eassumption.
        intros k Hk. exact (tuple_in_get (S n) _ (x .: sg) Yn (S k) ltac:(lia) HTZ). }
      unfold witness_closed, matrix_request in HW |- *. simp_in HW. fconv_h HW.
Qed.
