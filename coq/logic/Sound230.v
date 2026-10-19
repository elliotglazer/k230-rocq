(** Soundness of K230's numeric calculus in its decoded theory plus IR. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd.
From K230S Require Import KP0 KPrimeTheory KDecodeTheory KDecoder230 KDecodeBundle KDecodeFresh.
From K230L Require Import Codes230 Thm230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition DecodedK230IR (phi : form) := DecodedK230Ord phi \/ phi = irreflexivity.
Lemma K230IR_EqAx psi : In psi EqAx -> DecodedK230IR psi.
Proof. intros H. left. now apply DecodedK230Ord_eq. Qed.
Definition V (a : wff) : Prop := Fvalid DecodedK230IR a.
Lemma V_mp a b : V (Wim a b) -> V a -> V b.
Proof.
  intros [A1 [G1 H1]] [A2 [G2 H2]]. exists (A1 ++ A2). split.
  - intros psi [Hp|Hp]%in_app_iff; auto.
  - intro rho. eapply IE.
    + eapply Weak; [apply (H1 rho) | apply incl_appl, incl_refl].
    + eapply Weak; [apply (H2 rho) | apply incl_appr, incl_refl].
Qed.

Lemma V_gen x a : V a -> V (Wal x a).
Proof.
  intros [A [G H]]. exists A. split; [exact G|]. intro rho. cbn [dB]. apply AllI_named. intro t.
  rewrite dB_inst. apply H.
Qed.

Lemma V_lprov a : lprov a -> V a.
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz
                  | x y a | x a | x y | x y z | x y z | x y z].
  - exact (V_mp _ _ IH1 IH2).
  - now apply V_gen.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B1.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B2.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B3.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B4.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; now apply nd_B6a.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B6b.
  - apply (@Fvalid_nil DecodedK230IR K230IR_EqAx). intro; apply nd_B6c.
  - apply (@Fvalid_EqAx DecodedK230IR K230IR_EqAx). intro; apply nd_B7.
  - apply (@Fvalid_EqAx DecodedK230IR K230IR_EqAx). intro; apply nd_B8a.
  - apply (@Fvalid_EqAx DecodedK230IR K230IR_EqAx). intro; apply nd_B8b.
  - apply (@Fvalid_EqAx DecodedK230IR K230IR_EqAx). intro; apply nd_B8c.
Qed.

Lemma V_ir : V (Wal 1 (Wn (Wel 1 1))).
Proof.
  exists [irreflexivity]. split; [intros psi [<-|[]]; now right|].
  intro rho. apply Ctx. left. reflexivity.
Qed.

Lemma V_bundle a b c : c <> a -> c <> b -> V (D (bundle a b c)).
Proof.
  intros Hca Hcb. unfold bundle. rewrite <- (gated230_enabled a b c Hca Hcb).
  set (n := S (maxfr (D (gated230 a b c)))).
  exists [Lib n (D (gated230 a b c))]. split.
  - intros psi [<-|[]]. left.
    apply DecodedK230Ord_bundle. unfold n. lia.
  - intros rho. apply (Lib_inst _ n _ rho).
    + unfold n. lia.
    + apply Ctx. now left.
Qed.

Local Notation FF := (Wel 0 0).

Lemma V_lp a b : lprov (Wim a b) -> V a -> V b.
Proof. intros H Ha. exact (V_mp _ _ (V_lprov _ H) Ha). Qed.

Lemma V_nF : V (Wn FF).
Proof.
  apply (V_lp _ _ (spec_sf 1 0 (Wn (Wel 1 1)) ltac:(lia) eq_refl)). exact V_ir.
Qed.

(** ** Equivalence in V and congruence *)
Definition E (a b : wff) : Prop := V (Wim a b) /\ V (Wim b a).

Lemma E_refl a : E a a.
Proof. split; apply V_lprov, lpc_id. Qed.

Lemma E_sym a b : E a b -> E b a.
Proof. intros [H1 H2]. now split. Qed.

Lemma E_trans a b c : E a b -> E b c -> E a c.
Proof.
  intros [H1 H2] [H3 H4]. split.
  - apply (V_mp _ _ (V_mp _ _ (V_lprov _ (LB1 a b c)) H1) H3).
  - apply (V_mp _ _ (V_mp _ _ (V_lprov _ (LB1 c b a)) H4) H2).
Qed.

Lemma E_V a b : E a b -> V a -> V b.
Proof. intros [H _] Ha. exact (V_mp _ _ H Ha). Qed.

(* (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b')) *)
Lemma l_imp_mono a a' b b' : lprov (Wim (Wim a' a) (Wim (Wim b b') (Wim (Wim a b) (Wim a' b')))).
Proof.
  apply der_lprov. do 4 apply ded.
  apply (dmp _ b); [apply dhyp; simpl; tauto|].
  apply (dmp _ a); [apply dhyp; simpl; tauto|].
  apply (dmp _ a'); apply dhyp; simpl; tauto.
Qed.

Lemma E_im a a' b b' : E a a' -> E b b' -> E (Wim a b) (Wim a' b').
Proof.
  intros [H1 H2] [H3 H4]. split.
  - exact (V_mp _ _ (V_mp _ _ (V_lprov _ (l_imp_mono a a' b b')) H2) H3).
  - exact (V_mp _ _ (V_mp _ _ (V_lprov _ (l_imp_mono a' a b' b)) H1) H4).
Qed.

Lemma E_n a a' : E a a' -> E (Wn a) (Wn a').
Proof.
  intros [H1 H2]. split.
  - exact (V_mp _ _ (V_lprov _ (lpc_contra a' a)) H2).
  - exact (V_mp _ _ (V_lprov _ (lpc_contra a a')) H1).
Qed.

Lemma E_al x a a' : E a a' -> E (Wal x a) (Wal x a').
Proof.
  intros [H1 H2]. split.
  - exact (V_mp _ _ (V_lprov _ (LB4 x a a')) (V_gen x _ H1)).
  - exact (V_mp _ _ (V_lprov _ (LB4 x a' a)) (V_gen x _ H2)).
Qed.

(** x -> F  is  -. x  under IR *)
Lemma E_F a : E (Wim a FF) (Wn a).
Proof.
  split.
  - assert (L : lprov (Wim (Wn FF) (Wim (Wim a FF) (Wn a)))).
    { apply der_lprov. do 2 apply ded. apply (dmp _ (Wn FF)); [|apply dhyp; simpl; tauto].
      apply (dmp _ (Wim a FF)); [apply dthm, lpc_contra | apply dhyp; simpl; tauto]. }
    exact (V_mp _ _ (V_lprov _ L) V_nF).
  - apply V_lprov. apply der_lprov. do 2 apply ded.
    apply (dmp _ (Wn a)); [|apply dhyp; simpl; tauto].
    apply (dmp _ a); [apply dthm, LB3 | apply dhyp; simpl; tauto].
Qed.

Lemma T0_prov : lprov T0.
Proof. apply lpc_id. Qed.

Lemma D_F : D F = FF.
Proof. exact (D_wel 0 0). Qed.

Lemma D_wim_E x y : E (D (wim x y)) (Wim (D x) (D y)).
Proof.
  destruct (Nat.eq_dec y 1) as [->|Hy].
  - change (wim x 1) with (wn x). rewrite D_wn. change 1 with F. rewrite D_F. apply E_sym, E_F.
  - destruct (Nat.eq_dec x 0) as [->|Hx]; [destruct (Nat.eq_dec y 0) as [->|Hy0]|].
    + rewrite D_wim00, D_0. split; apply V_lprov.
      * exact (lpc_K T0 T0).
      * exact (LDET _ _ (lpc_K T0 (Wim T0 T0)) T0_prov).
    + rewrite D_wim by (try lia; intro E; injection E; lia). apply E_refl.
    + rewrite D_wim by (try lia; intro E; injection E; lia). apply E_refl.
Qed.

Ltac Etac :=
  first [ apply E_refl
        | (eapply E_trans; [apply D_wim_E | apply E_im; Etac])
        | (rewrite D_wal; apply E_al; Etac)
        | (rewrite D_F; apply E_refl)
        | (rewrite D_wel; apply E_refl)
        | (rewrite D_weq; apply E_refl)
        | (apply E_im; Etac)
        | (apply E_al; Etac) ].

Local Opaque wim wel wal weq P.

(** ** The rows *)
Lemma V_r1 a b : V (D (rho1 a b)).
Proof.
  unfold rho1, wex, wn.
  assert (Ea : E (D (wim (wal a (wim (weq a b) F)) F)) (Wim (Wal a (Wim (Weq a b) FF)) FF)) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)).
  apply (E_V (Wex a (Weq a b))); [|apply V_lprov, LB7].
  unfold Wex. eapply E_trans; [|apply E_sym, E_F]. apply E_n, E_al, E_sym, E_F.
Qed.

Lemma V_r6 a b : V (D (rho6 a b)).
Proof.
  unfold rho6, wex, wn.
  assert (Ea : E (D (wim (wim (wal a (wim (wal a b) F)) F) b))
                 (Wim (Wim (Wal a (Wim (Wal a (D b)) FF)) FF) (D b))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)).
  apply (E_V (Wim (Wex a (Wal a (D b))) (D b))); [|apply V_lprov, LB6c].
  apply E_im; [|apply E_refl]. unfold Wex.
  eapply E_trans; [|apply E_sym, E_F]. apply E_n, E_al, E_sym, E_F.
Qed.

Lemma V_r2 a b c : V (D (rho2 a b c)).
Proof.
  unfold rho2.
  assert (Ea : E (D (wim (wal a (wim b c)) (wim (wal a b) (wal a c))))
                 (Wim (Wal a (Wim (D b) (D c))) (Wim (Wal a (D b)) (Wal a (D c))))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, LB4.
Qed.

Lemma V_r3 a b c : V (D (rho3 a b c)).
Proof.
  unfold rho3.
  assert (Ea : E (D (wim (weq a b) (wim (wel c a) (wel c b))))
                 (Wim (Weq a b) (Wim (Wel c a) (Wel c b)))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, LB8c.
Qed.

Lemma V_r4 a b c : V (D (rho4 a b c)).
Proof.
  unfold rho4.
  assert (Ea : E (D (wim (wal a (wal b c)) (wal b (wal a c))))
                 (Wim (Wal a (Wal b (D c))) (Wal b (Wal a (D c))))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, LB6b.
Qed.

Lemma V_r5 a b c : V (D (rho5 a b c)).
Proof.
  unfold rho5.
  assert (Ea : E (D (wim (weq c a) (wim (wel c b) (wel a b))))
                 (Wim (Weq c a) (Wim (Wel c b) (Wel a b)))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, LB8b.
Qed.

Lemma V_r7 a b c : V (D (rho7 a b c)).
Proof.
  unfold rho7.
  assert (Ea : E (D (wim (weq c a) (wim (weq c b) (weq a b))))
                 (Wim (Weq c a) (Wim (Weq c b) (Weq a b)))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, LB8a.
Qed.

(* ((c -> u) -> a) -> ((a -> c) -> (b -> c)) *)
Lemma l_luk a b c u : lprov (Wim (Wim (Wim c u) a) (Wim (Wim a c) (Wim b c))).
Proof.
  apply der_lprov. do 3 apply ded.
  apply (dmp _ (Wim (Wim c u) c)); [apply dthm, llp369|].
  apply ded. apply (dmp _ a); [apply dhyp; simpl; tauto|].
  apply (dmp _ (Wim c u)); apply dhyp; simpl; tauto.
Qed.

Lemma V_r8 a b c u : V (D (rho8 a b c u)).
Proof.
  unfold rho8.
  assert (Ea : E (D (wim (wim (wim c u) a) (wim (wim a c) (wim b c))))
                 (Wim (Wim (Wim (D c) (D u)) (D a)) (Wim (Wim (D a) (D c)) (Wim (D b) (D c))))) by Etac.
  apply (E_V _ _ (E_sym _ _ Ea)). apply V_lprov, l_luk.
Qed.

(** ** Self-freshness of the decoder *)
Lemma D_fr v n : fr v (D n) = true -> v < n.
Proof.
  induction n as [n IH] using lt_wf_ind. intro H.
  destruct n as [|m]; [rewrite D_0 in H; unfold T0 in H; destruct v; cbn in H; discriminate|].
  rewrite D_unfold in H by lia. unfold Dbody in H.
  pose proof (div4_lt (S m) ltac:(lia)) as Hd.
  pose proof (unP_le (S m / 4)) as [Hx Hy].
  destruct (unP (S m / 4)) as [x y]. cbn [fst snd] in Hx, Hy.
  destruct (S m mod 4) as [|[|[|k]]]; cbn [fr] in H.
  - destruct (Nat.eqb y 1); cbn [fr] in H.
    + apply IH in H; lia.
    + apply orb_true_iff in H as [H|H]; apply IH in H; lia.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; lia.
  - destruct (Nat.eqb x v); [discriminate|]. apply IH in H; lia.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; lia.
Qed.

Lemma D_fr_self c : fr c (D c) = false.
Proof. destruct (fr c (D c)) eqn:E; [apply D_fr in E; lia | reflexivity]. Qed.

(** ** Soundness of the code-level calculus *)
Theorem thm_V n : thm230 n -> V (D n).
Proof.
  induction 1 as [| t b _ IH1 _ IH2 | a hh _ IH | a b | a b c | a b c | a b c | a b c | a b
                  | a b c | a b c u | a b c H1 H2].
  - rewrite D_0. apply V_lprov, T0_prov.
  - destruct (D_wim_E t b) as [H _]. exact (V_mp _ _ (V_mp _ _ H IH2) IH1).
  - rewrite D_wal. now apply V_gen.
  - apply V_r1.
  - apply V_r2.
  - apply V_r3.
  - apply V_r4.
  - apply V_r5.
  - apply V_r6.
  - apply V_r7.
  - apply V_r8.
  - exact (V_bundle a b c H1 H2).
Qed.

Theorem thm_to_DecodedK230IR : thm230 1 -> @tprv _ _ falsity_on class DecodedK230IR falsity.
Proof.
  intro H. apply thm_V in H. change 1 with (wel 0 0) in H. rewrite D_wel in H.
  destruct H as [A [HA Hd]]. exists (irreflexivity :: A). split.
  - intros psi [<-|Hp]; [now right | exact (HA psi Hp)].
  - specialize (Hd var). cbn [dB] in Hd.
    eapply IE; [|eapply Weak; [exact Hd | intros z Hz; now right]].
    change (¬ $0 ∈' $0) with ((¬ $0 ∈' $0)[($0)..]). apply AllE. apply Ctx. now left.
Qed.
