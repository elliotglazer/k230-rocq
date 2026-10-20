(** * Std_gen: universal closures of named wffs, their de Bruijn images, instantiation in ND,
    and the round trip [tr] after [dB] (used to show that closures of [prov]-theorems translate back
    to [prov]-theorems). *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

(** [genall n a] = A. v_(n-1) ... A. v_0 a *)
Fixpoint genall (n : nat) (a : wff) : wff :=
  match n with 0 => a | S n => Wal n (genall n a) end.

Lemma prov_genall n a : prov a -> prov (genall n a).
Proof. induction n; cbn; auto. intro H. apply GEN, IHn, H. Qed.

Fixpoint maxfr (a : wff) : nat :=
  match a with
  | Weq u v | Wel u v => Nat.max u v
  | Wim a b => Nat.max (maxfr a) (maxfr b)
  | Wn a => maxfr a
  | Wal _ a => maxfr a
  end.

Lemma fr_maxfr v a : fr v a = true -> v <= maxfr a.
Proof.
  induction a as [u w|u w|a IHa b IHb|a IHa|z a IHa]; cbn; intro H;
    rewrite ?orb_true_iff in H; try destruct H as [H|H];
    try (apply Nat.eqb_eq in H; lia); try (specialize (IHa H); lia); try (specialize (IHb H); lia).
  destruct (Nat.eqb z v); [discriminate | specialize (IHa H); lia].
Qed.

(** ** Instantiating a closure in natural deduction *)
Lemma shift_env_inst' x (rho : nat -> term) t v :
  (shift_env x rho >> subst_term (t..)) v = if Nat.eqb v x then t else rho v.
Proof. unfold shift_env, funcomp. destruct (Nat.eqb v x); cbn; [reflexivity | apply subst_term_shift]. Qed.

Lemma gen_inst A n a (rho sigma : nat -> term) :
  A ⊢C dB rho (genall n a) -> A ⊢C dB (fun v => if Nat.ltb v n then sigma v else rho v) a.
Proof.
  revert rho; induction n as [|n IH]; intros rho H.
  - erewrite dB_ext; [exact H|]. intro v. reflexivity.
  - cbn [genall dB] in H. apply (AllE (sigma n)) in H. rewrite dB_subst in H.
    erewrite (dB_ext _ (shift_env_inst' n rho (sigma n))) in H.
    specialize (IH _ H). erewrite dB_ext; [exact IH|].
    intro v. cbv beta. destruct (Nat.ltb_spec v n), (Nat.ltb_spec v (S n)), (Nat.eqb_spec v n); try lia; auto.
    all: subst; reflexivity.
Qed.

Lemma gen_inst_full A n a (rho sigma : nat -> term) : maxfr a < n ->
  A ⊢C dB rho (genall n a) -> A ⊢C dB sigma a.
Proof.
  intros Hn H. apply (gen_inst A n a rho sigma) in H.
  rewrite (dB_ext_fr sigma (fun v => if Nat.ltb v n then sigma v else rho v) a); [exact H|].
  intros v Hv. apply fr_maxfr in Hv. destruct (Nat.ltb_spec v n); [reflexivity | lia].
Qed.

(** ** Free indices of [dB] images and the [->]/[A.]-fragment *)
Lemma fb_dB N (rho : nat -> term) a : (forall v, fr v a = true -> idx (rho v) < N) -> fb N (dB rho a).
Proof.
  revert N rho; induction a as [u w|u w|a IHa b IHb|a IHa|z a IHa]; intros N rho H; cbn [dB fb fr] in *.
  - cbn. split; apply H; apply orb_true_iff; [left|right]; apply Nat.eqb_refl.
  - cbn. split; apply H; apply orb_true_iff; [left|right]; apply Nat.eqb_refl.
  - split; [apply IHa | apply IHb]; intros v Hv; apply H; apply orb_true_iff; auto.
  - split; [apply IHa; auto | exact I].
  - apply IHa. intros v Hv. unfold shift_env. destruct (Nat.eqb_spec v z); [cbn; lia|].
    destruct (rho v) as [k|[]] eqn:E; cbn. specialize (H v). rewrite E in H. cbn in H.
    destruct (Nat.eqb_spec z v); [congruence|]. specialize (H Hv). lia.
Qed.

Fixpoint frag {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : Prop :=
  match phi with
  | falsity => False
  | atom _ _ => True
  | bin Impl a b => frag a /\ (match b with falsity => True | _ => frag b end)
  | bin _ _ _ => False
  | quant All a => frag a
  | quant Ex _ => False
  end.

Lemma frag_dB (rho : nat -> term) a : frag (dB rho a).
Proof.
  revert rho; induction a as [u w|u w|a IHa b IHb|a IHa|z a IHa]; intros rho; cbn; auto.
  split; auto. destruct b; cbn; auto; apply IHb.
Qed.

Lemma subst_ext_fb {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) N (sg tau : nat -> term) :
  fb N phi -> (forall n, n < N -> sg n = tau n) -> phi[sg] = phi[tau].
Proof.
  revert N sg tau; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N sg tau Hfb H; cbn in *.
  - reflexivity.
  - destruct P; cbn in v, Hfb |- *; rewrite (vec2 v); cbn;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *;
      rewrite !H by tauto; reflexivity.
  - destruct Hfb. now rewrite (IHa N sg tau), (IHb N sg tau).
  - f_equal. apply (IHa (S N)); auto. intros [|n] Hn; cbn; [reflexivity|]. unfold funcomp. rewrite H; auto; lia.
Qed.

Definition isbot {ff} (b : @Core.form sig_empty ZF_pred_sig full_operators ff) : bool :=
  match b with falsity => true | _ => false end.

Lemma tr_impl_cases {ff} eta (a b : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  tr eta (bin Impl a b) = if isbot b then Wn (tr eta a) else Wim (tr eta a) (tr eta b).
Proof. destruct b; reflexivity. Qed.

Lemma frag_impl_cases {ff} (a b : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  frag (bin Impl a b) <-> frag a /\ (if isbot b then True else frag b).
Proof. destruct b; cbn; tauto. Qed.

Lemma isbot_true (b : form) : isbot b = true -> b = falsity.
Proof. induction b using form_ind_falsity; cbn; intro H; try discriminate; reflexivity. Qed.

Lemma dB_tr (phi : form) : forall N eta (rho : nat -> term),
  frag phi -> fb N phi -> (forall n k, n < N -> k < qd phi -> eta n <> bname k) ->
  dB rho (tr eta phi) = phi[fun n => rho (eta n)].
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity; intros N eta rho Hfr Hfb Hn; cbn in Hfr.
  - contradiction.
  - destruct P; cbn in v, Hfb |- *; rewrite (vec2 v); cbn;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; reflexivity.
  - destruct op; try contradiction. apply frag_impl_cases in Hfr. destruct Hfr as [Ha Hb]. destruct Hfb as [Fa Fb].
    assert (Hna : forall n k, n < N -> k < qd a -> eta n <> bname k) by (intros; apply Hn; cbn; lia).
    rewrite tr_impl_cases. destruct (isbot b) eqn:Eb.
    + apply isbot_true in Eb. subst b. cbn [dB subst_form]. now rewrite (IHa N eta rho Ha Fa Hna).
    + cbn [dB subst_form]. rewrite (IHa N eta rho Ha Fa Hna). f_equal.
      apply (IHb N); auto. intros; apply Hn; cbn; lia.
  - destruct q; try contradiction. cbn [tr dB subst_form]. f_equal.
    rewrite (IHa (S N) (scons (bname (qd a)) eta) (shift_env (bname (qd a)) rho) Hfr Hfb).
    + apply (subst_ext_fb _ (S N)); [exact Hfb|]. intros [|n] Hlt; cbn.
      * unfold shift_env. now rewrite Nat.eqb_refl.
      * unfold shift_env, funcomp. destruct (Nat.eqb_spec (eta n) (bname (qd a))) as [E|E]; [|reflexivity].
        exfalso. apply (Hn n (qd a)); [lia | cbn; lia | exact E].
    + intros [|n] k Hlt Hk; cbn.
      * unfold bname. lia.
      * apply Hn; cbn; lia.
Qed.

Lemma fr_genall v n a : fr v (genall n a) = true -> n <= v /\ fr v a = true.
Proof.
  induction n; cbn; [split; [lia | auto]|]. destruct (Nat.eqb_spec n v); [discriminate|].
  intros H. destruct (IHn H). split; [lia | auto].
Qed.

Lemma fb_cl n a : maxfr a < n -> fb 0 (dB var (genall n a)).
Proof.
  intro Hn. apply fb_dB. intros v Hv. apply fr_genall in Hv as [H1 H2]. apply fr_maxfr in H2. lia.
Qed.

Lemma injective_var : injective var.
Proof. intros u v H. now inversion H. Qed.

(** the de Bruijn closure of a prov-theorem translates back to a prov-theorem, for any environment
    that avoids the binder names (in particular any odd-valued one) *)
Lemma tr_cl_prov eta n a : prov a -> maxfr a < n -> prov (tr eta (dB var (genall n a))).
Proof.
  intros Ha Hn. set (th := dB var (genall n a)).
  assert (Hfb : fb 0 th) by now apply fb_cl.
  assert (E : dB var (tr eta th) = dB var (genall n a)).
  { rewrite (dB_tr th 0 eta var (frag_dB _ _) Hfb) by (intros; lia).
    rewrite (subst_ext_fb _ 0 _ var Hfb) by (intros; lia). apply subst_var. }
  destruct (alpha_dB _ _ var injective_var E) as [_ H2].
  exact (DET _ _ (lprov_prov _ H2) (prov_genall n a Ha)).
Qed.
