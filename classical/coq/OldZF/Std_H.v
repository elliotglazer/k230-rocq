(** * Std_H: soundness of the library's classical natural deduction (minimal signature) for
    O'Rear's Hilbert system: if [A ⊢C phi] then [der (map (tr eta) A) (tr eta phi)] (pure logic,
    [lprov]) for every environment [eta] with odd values. *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_tr.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

(** ** Hypothesis lists and generalization *)
Lemma der_weak G G' a : der G a -> incl G G' -> der G' a.
Proof. induction 1; intros HG; [apply dhyp; auto | apply dthm; auto | eapply dmp; eauto]. Qed.

Definition foldi (G : list wff) (a : wff) : wff := fold_left (fun acc h => Wim h acc) G a.

Lemma der_foldi G a : der G a -> lprov (foldi G a).
Proof.
  revert a; induction G as [|h G IH]; intros a H.
  - exact (der_lprov _ H).
  - apply IH. exact (ded _ _ _ H).
Qed.

Lemma foldi_der G a : lprov (foldi G a) -> der G a.
Proof.
  revert a; induction G as [|h G IH]; intros a H.
  - exact (dthm _ _ H).
  - specialize (IH _ H). eapply dmp; [eapply der_weak; [exact IH | intros ? ?; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma foldi_mono G a b : lprov (Wim a b) -> lprov (Wim (foldi G a) (foldi G b)).
Proof.
  revert a b; induction G as [|h G IH]; intros a b H; [exact H|].
  apply IH. apply der_lprov, ded, ded. eapply dmp; [apply dthm, H|]. eapply dmp; apply dhyp; simpl; auto.
Qed.

Lemma all_imp_vac y h c : occ y h = false -> lprov (Wim (Wal y (Wim h c)) (Wim h (Wal y c))).
Proof.
  intro Hy. apply der_lprov, ded, ded.
  eapply dmp; [eapply dmp; [apply dthm, (LB4 y h c) | apply dhyp; simpl; auto]|].
  eapply dmp; [apply dthm, (lvac y h Hy) | apply dhyp; simpl; auto].
Qed.

Lemma push_all G y c : (forall h, In h G -> occ y h = false) ->
  lprov (Wal y (foldi G c)) -> lprov (foldi G (Wal y c)).
Proof.
  revert c; induction G as [|h G IH]; intros c HG H; [exact H|].
  cbn [foldi fold_left] in *.
  assert (H1 : lprov (foldi G (Wal y (Wim h c)))) by (apply IH; [intros h0 Hh0; apply HG; simpl; auto | exact H]).
  exact (LDET _ _ (foldi_mono G _ _ (all_imp_vac y h c (HG h (or_introl eq_refl)))) H1).
Qed.

Lemma der_gen G y a : (forall h, In h G -> occ y h = false) -> der G a -> der G (Wal y a).
Proof.
  intros HG H. apply foldi_der. apply push_all; [exact HG|]. apply LGEN. now apply der_foldi.
Qed.

(** ** Propositional helpers *)
Lemma l_botw_elim a : lprov (Wim botw a).
Proof.
  unfold botw. apply der_lprov, ded.
  eapply dmp; [eapply dmp; [apply dthm, (LB3 (Wal 0 (Weq 0 0)) a) | apply dthm, LGEN, leq_refl] | apply dhyp; simpl; auto].
Qed.

Lemma l_not_botw : lprov (Wn botw).
Proof. unfold botw. exact (LDET _ _ (lpc_nn_intro _) (LGEN 0 _ (leq_refl 0))). Qed.

Lemma tr_imp_equiv eta (phi psi : form) :
  leqv (tr eta (bin Impl phi psi)) (Wim (tr eta phi) (tr eta psi)).
Proof.
  destruct psi; cbn [tr]; try (split; apply lpc_id).
  set (p := tr eta phi). split; apply der_lprov, ded.
  - apply ded. eapply dmp; [eapply dmp; [apply dthm, (LB3 p botw) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
  - eapply dmp; [eapply dmp; [apply dthm, (lpc_contra p botw) | apply dhyp; simpl; auto] | apply dthm, l_not_botw].
Qed.

Lemma der_leqv G a b : leqv a b -> der G a -> der G b.
Proof. intros [H _] Ha. exact (dmp _ _ _ (dthm _ _ H) Ha). Qed.

Lemma leqv_sym a b : leqv a b -> leqv b a.
Proof. intros [H1 H2]; split; assumption. Qed.

Lemma leqv_im a a' b b' : leqv a a' -> leqv b b' -> leqv (Wim a b) (Wim a' b').
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_lprov, ded, ded.
  - eapply dmp; [apply dthm, H3|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H2 | apply dhyp; simpl; auto].
  - eapply dmp; [apply dthm, H4|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H1 | apply dhyp; simpl; auto].
Qed.

Lemma leqv_refl a : leqv a a.
Proof. split; apply lpc_id. Qed.

Lemma lprov_leqv a b : leqv a b -> lprov a -> lprov b.
Proof. intros [H _] Ha. exact (LDET _ _ H Ha). Qed.

Lemma l_peirce p q : lprov (Wim (Wim (Wim p q) p) p).
Proof.
  apply der_lprov, ded. eapply dmp; [apply dthm, (LB2 p)|]. apply ded.
  eapply dmp; [apply dhyp; simpl; right; left; reflexivity|].
  apply ded. eapply dmp; [eapply dmp; [apply dthm, (LB3 p q) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma l_case a b c : lprov (Wim (Wim (Wn a) b) (Wim (Wim a c) (Wim (Wim b c) c))).
Proof.
  apply der_lprov, ded, ded, ded.
  eapply dmp; [apply dthm, (LB2 c)|]. apply ded.
  (* G = [-.c; b -> c; a -> c; -.a -> b] *)
  eapply dmp; [apply dhyp; simpl; right; left; reflexivity|].
  eapply dmp; [apply dhyp; simpl; right; right; right; left; reflexivity|].
  eapply dmp; [eapply dmp; [apply dthm, (lpc_contra a c) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma l_ex_elim y p c : occ y c = false -> lprov (Wim (Wal y (Wim p c)) (Wim (Wex y p) c)).
Proof.
  intro Hy. apply der_lprov, ded, ded.
  eapply dmp; [apply dthm, (LB6c y c)|].
  eapply dmp; [apply dthm, (lex y _ _ (lvac y c Hy))|].
  eapply dmp; [eapply dmp; [apply dthm, (lall_ex y p c) | apply dhyp; simpl; auto] | apply dhyp; simpl; auto].
Qed.

Lemma l_ex_intro x y a : x <> y -> bnd x a = false -> bnd y a = false ->
  lprov (Wim (ren x y a) (Wex x a)).
Proof.
  intros H1 H2 H3. unfold Wex. pose proof (lspec x y (Wn a) H1 H2 H3) as H. cbn [ren] in H.
  exact (lsyl _ _ _ (lpc_nn_intro _) (lcontra _ _ H)).
Qed.

Lemma lalpha_ex x y a : x <> y -> bnd x a = false -> occ y a = false ->
  leqv (Wex x a) (Wex y (ren x y a)).
Proof.
  intros H1 H2 H3. unfold Wex. split; apply lcontra.
  - pose proof (lalpha_back x y (Wn a) H1 H2 H3) as H. exact H.
  - pose proof (lalpha x y (Wn a) H1 H2 H3) as H. exact H.
Qed.

(** ** Environments and fresh names *)
Definition oddenv (eta : nat -> nat) : Prop := forall n, Nat.odd (eta n) = true.

Fixpoint sumenv (eta : nat -> nat) (N : nat) : nat :=
  match N with 0 => 0 | S N => eta N + sumenv eta N end.

Lemma sumenv_ge eta N n : n < N -> eta n <= sumenv eta N.
Proof. induction N; intros H; cbn; [lia|]. destruct (Nat.eq_dec n N); [subst; lia | specialize (IHN ltac:(lia)); lia]. Qed.

Definition fresh (eta : nat -> nat) (N : nat) : nat := 2 * sumenv eta N + 1.

Lemma fresh_odd eta N : Nat.odd (fresh eta N) = true.
Proof. unfold fresh. rewrite Nat.odd_add, Nat.odd_mul. reflexivity. Qed.

Lemma fresh_neq eta N n : n < N -> eta n <> fresh eta N.
Proof. intros H. pose proof (sumenv_ge eta N n H). unfold fresh. lia. Qed.

Lemma odd_neq_bname y k : Nat.odd y = true -> y <> bname k.
Proof. intros H ->. unfold bname in H. rewrite Nat.odd_add, Nat.odd_mul in H. discriminate. Qed.

Lemma oddenv_cons y eta : Nat.odd y = true -> oddenv eta -> oddenv (scons y eta).
Proof. intros Hy He [|n]; cbn; auto. Qed.

Lemma tr_shift eta y (psi : form) : tr (scons y eta) (psi[↑]) = tr eta psi.
Proof. rewrite (@tr_subst _ psi (scons y eta) _ S); [apply tr_ext; reflexivity | intros n; reflexivity]. Qed.

Lemma tr_inst eta m (phi : form) : tr eta (phi[($m)..]) = tr (scons (eta m) eta) phi.
Proof.
  rewrite (@tr_subst _ phi eta _ (fun n => match n with 0 => m | S n => n end)).
  - apply tr_ext. intros []; reflexivity.
  - intros []; reflexivity.
Qed.

Lemma tr_ext_fb (phi : form) N eta eta' : fb N phi -> (forall n, n < N -> eta n = eta' n) -> tr eta phi = tr eta' phi.
Proof.
  enough (G : forall ff (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) N eta eta',
             fb N phi -> (forall n, n < N -> eta n = eta' n) -> tr eta phi = tr eta' phi) by apply G.
  clear. intros ff phi; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N eta eta' Hfb H; cbn in *.
  - reflexivity.
  - destruct P; cbn in *; rewrite !tv_idx, !H by tauto; reflexivity.
  - destruct Hfb as [Ha Hb]. rewrite (IHa N eta eta' Ha H).
    destruct op; [now rewrite (IHb N eta eta' Hb H) | now rewrite (IHb N eta eta' Hb H) |].
    destruct b; try reflexivity; now rewrite (IHb N eta eta' Hb H).
  - destruct q; [apply (f_equal (Wal _)) | apply (f_equal (Wex _))];
      apply (IHa (S N)); auto; intros [|n] Hn; cbn; auto; apply H; lia.
Qed.

(** The binder of [quant q phi] vs. a fresh odd name [y]: alpha-conversion. *)
Lemma alpha_tr eta y N (phi : form) :
  oddenv eta -> Nat.odd y = true -> fb (S N) phi -> (forall n, n < N -> eta n <> y) ->
  let B := bname (qd phi) in
  y <> B /\ bnd y (tr (scons y eta) phi) = false /\ occ B (tr (scons y eta) phi) = false /\
  ren y B (tr (scons y eta) phi) = tr (scons B eta) phi.
Proof.
  intros He Hy Hfb Hn B.
  assert (HyB : y <> B) by (apply odd_neq_bname; exact Hy).
  assert (HnbB : notbinder B phi).
  { split; [unfold B, bname; lia | intros k Hk E; unfold B, bname in E; lia]. }
  assert (Hnby : notbinder y phi) by (apply notbinder_odd; exact Hy).
  split; [exact HyB|]. split; [apply (@bnd_tr _ phi (scons y eta) y Hnby)|]. split.
  - apply (@occ_tr _ phi (S N) (scons y eta) B); [exact Hfb | | exact HnbB].
    intros [|n] _; cbn; [congruence|]. intro E. pose proof (He n) as O. rewrite E in O.
    unfold B, bname in O. rewrite Nat.odd_add, Nat.odd_mul in O. discriminate.
  - rewrite (@ren_tr _ phi (scons y eta) y B Hnby HnbB). apply (tr_ext_fb _ (S N)); [exact Hfb|].
    intros [|n] Hlt; cbn; unfold rv; [now rewrite Nat.eqb_refl|].
    assert (E : Nat.eqb (eta n) y = false) by (apply Nat.eqb_neq, Hn; lia). now rewrite E.
Qed.

Lemma leqv_trans a b c : leqv a b -> leqv b c -> leqv a c.
Proof. intros [H1 H2] [H3 H4]. split; eapply lsyl; eassumption. Qed.

Lemma notbinder_bname (phi : form) : notbinder (bname (qd phi)) phi.
Proof. split; [unfold bname; lia | intros k Hk E; unfold bname in E; lia]. Qed.

Lemma oddenv_neq_bname eta n k : oddenv eta -> eta n <> bname k.
Proof. intros He. apply odd_neq_bname, He. Qed.

(** instantiation of the binder of [quant q phi] by the (odd) name [eta m] *)
Lemma inst_tr eta m (phi : form) : oddenv eta ->
  let B := bname (qd phi) in
  B <> eta m /\ bnd B (tr (scons B eta) phi) = false /\ bnd (eta m) (tr (scons B eta) phi) = false /\
  ren B (eta m) (tr (scons B eta) phi) = tr (scons (eta m) eta) phi.
Proof.
  intros He B.
  assert (Hm : notbinder (eta m) phi) by (apply notbinder_odd, He).
  split; [intro E; symmetry in E; exact (oddenv_neq_bname eta m _ He E)|].
  split; [apply (@bnd_tr _ phi (scons B eta) B (notbinder_bname phi))|].
  split; [apply (@bnd_tr _ phi (scons B eta) (eta m) Hm)|].
  rewrite (@ren_tr _ phi (scons B eta) B (eta m) (notbinder_bname phi) Hm).
  apply tr_ext. intros [|n]; cbn; unfold rv; [now rewrite Nat.eqb_refl|].
  assert (E : Nat.eqb (eta n) B = false) by (apply Nat.eqb_neq, (oddenv_neq_bname eta n _ He)). now rewrite E.
Qed.

Lemma map_tr_shift eta y (A : list form) : map (tr (scons y eta)) (map (subst_form ↑) A) = map (tr eta) A.
Proof. rewrite map_map. apply map_ext. intro. apply tr_shift. Qed.

Lemma fresh_not_occ eta N (A : list form) : (forall psi, In psi A -> fb N psi) ->
  forall h, In h (map (tr eta) A) -> occ (fresh eta N) h = false.
Proof.
  intros HA h Hh. apply in_map_iff in Hh as [psi [<- Hpsi]].
  apply (@occ_tr _ psi N eta); [apply HA, Hpsi | intros n Hn; apply fresh_neq, Hn | apply notbinder_odd, fresh_odd].
Qed.

Theorem nd_sound (A : list form) (phi : form) :
  A ⊢C phi -> forall eta, oddenv eta -> der (map (tr eta) A) (tr eta phi).
Proof.
  intro D.
  pattern class, A, phi. revert D. generalize class. intros p D. pattern p, A, phi.
  revert p A phi D. apply prv_ind_full.
  - (* II *) intros p A phi psi _ IH eta He. specialize (IH eta He). cbn [map] in IH.
    apply (der_leqv _ _ _ (leqv_sym _ _ (tr_imp_equiv eta phi psi))). now apply ded.
  - (* IE *) intros p A phi psi _ IH1 _ IH2 eta He.
    specialize (IH1 eta He). apply (der_leqv _ _ _ (tr_imp_equiv eta phi psi)) in IH1. exact (dmp _ _ _ IH1 (IH2 eta He)).
  - (* AllI *) intros p A phi _ IH eta He.
    destruct (fb_exists_L A) as [N1 HN1]. destruct (fb_exists phi) as [N2 HN2].
    set (N := N1 + N2). set (y := fresh eta N).
    assert (HA : forall psi, In psi A -> fb N psi) by (intros; eapply fb_mono; eauto; lia).
    assert (Hphi : fb (S N) phi) by (eapply fb_mono; eauto; lia).
    specialize (IH (scons y eta) (oddenv_cons _ _ (fresh_odd eta N) He)).
    rewrite map_tr_shift in IH.
    apply (der_gen _ y) in IH; [| apply fresh_not_occ, HA].
    destruct (alpha_tr eta y N phi He (fresh_odd eta N) Hphi (fun n Hn => fresh_neq eta N n Hn))
      as (Hne & Hbnd & Hocc & Hren).
    pose proof (lalpha y _ _ Hne Hbnd Hocc) as Hal. rewrite Hren in Hal.
    exact (dmp _ _ _ (dthm _ _ Hal) IH).
  - (* AllE *) intros p A t phi _ IH eta He. destruct t as [m|[]].
    rewrite tr_inst. specialize (IH eta He). cbn [tr] in IH.
    destruct (inst_tr eta m phi He) as (Hne & Hb1 & Hb2 & Hren).
    pose proof (lspec _ _ _ Hne Hb1 Hb2) as Hs. rewrite Hren in Hs.
    exact (dmp _ _ _ (dthm _ _ Hs) IH).
  - (* ExI *) intros p A t phi _ IH eta He. destruct t as [m|[]].
    specialize (IH eta He). rewrite tr_inst in IH. cbn [tr].
    destruct (inst_tr eta m phi He) as (Hne & Hb1 & Hb2 & Hren).
    pose proof (l_ex_intro _ _ _ Hne Hb1 Hb2) as Hs. rewrite Hren in Hs.
    exact (dmp _ _ _ (dthm _ _ Hs) IH).
  - (* ExE *) intros p A phi psi _ IH1 _ IH2 eta He.
    destruct (fb_exists_L A) as [N1 HN1]. destruct (fb_exists phi) as [N2 HN2].
    destruct (fb_exists psi) as [N3 HN3].
    set (N := N1 + N2 + N3). set (y := fresh eta N).
    assert (HA : forall chi, In chi A -> fb N chi) by (intros; eapply fb_mono; eauto; lia).
    assert (Hphi : fb (S N) phi) by (eapply fb_mono; eauto; lia).
    assert (Hpsi : fb N psi) by (eapply fb_mono; eauto; lia).
    specialize (IH2 (scons y eta) (oddenv_cons _ _ (fresh_odd eta N) He)).
    cbn [map] in IH2. rewrite map_tr_shift, tr_shift in IH2.
    apply ded in IH2. apply (der_gen _ y) in IH2; [| apply fresh_not_occ, HA].
    assert (Hy : occ y (tr eta psi) = false).
    { apply (@occ_tr _ psi N eta); [exact Hpsi | intros n Hn; apply fresh_neq, Hn | apply notbinder_odd, fresh_odd]. }
    pose proof (dmp _ _ _ (dthm _ _ (l_ex_elim _ _ _ Hy)) IH2) as Hel.
    refine (dmp _ _ _ Hel _). specialize (IH1 eta He). cbn [tr] in IH1.
    destruct (alpha_tr eta y N phi He (fresh_odd eta N) Hphi (fun n Hn => fresh_neq eta N n Hn))
      as (Hne & Hbnd & Hocc & Hren).
    pose proof (lalpha_ex y _ _ Hne Hbnd Hocc) as Hal. rewrite Hren in Hal.
    exact (der_leqv _ _ _ (leqv_sym _ _ Hal) IH1).
  - (* Exp *) intros p A phi _ IH eta He. exact (dmp _ _ _ (dthm _ _ (l_botw_elim _)) (IH eta He)).
  - (* Ctx *) intros p A phi H eta He. apply dhyp. now apply in_map.
  - (* CI *) intros p A phi psi _ IH1 _ IH2 eta He. cbn [tr].
    exact (dmp _ _ _ (dmp _ _ _ (dthm _ _ (lpc_andi _ _)) (IH1 eta He)) (IH2 eta He)).
  - (* CE1 *) intros p A phi psi _ IH eta He. exact (dmp _ _ _ (dthm _ _ (lpc_andl _ _)) (IH eta He)).
  - (* CE2 *) intros p A phi psi _ IH eta He. exact (dmp _ _ _ (dthm _ _ (lpc_andr _ _)) (IH eta He)).
  - (* DI1 *) intros p A phi psi _ IH eta He. cbn [tr].
    exact (dmp _ _ _ (dthm _ _ (LB3 _ _)) (IH eta He)).
  - (* DI2 *) intros p A phi psi _ IH eta He. cbn [tr].
    exact (dmp _ _ _ (dthm _ _ (lpc_K _ _)) (IH eta He)).
  - (* DE *) intros p A phi psi theta _ IH1 _ IH2 _ IH3 eta He.
    specialize (IH1 eta He). specialize (IH2 eta He). specialize (IH3 eta He). cbn [map tr] in *.
    apply ded in IH2. apply ded in IH3.
    exact (dmp _ _ _ (dmp _ _ _ (dmp _ _ _ (dthm _ _ (l_case _ _ _)) IH1) IH2) IH3).
  - (* Pc *) intros A phi psi eta He. apply dthm.
    refine (lprov_leqv _ _ _ (l_peirce (tr eta phi) (tr eta psi))).
    apply leqv_sym. eapply leqv_trans; [apply tr_imp_equiv|]. apply leqv_im; [|apply leqv_refl].
    eapply leqv_trans; [apply tr_imp_equiv|]. apply leqv_im; [apply tr_imp_equiv | apply leqv_refl].
Qed.
