(** * Std_alpha: alpha-equivalent named wffs are provably equivalent in pure logic.

    [alpha_dB]: if [dB rho a = dB rho b] for an injective variable environment [rho], then
    [leqv a b].  The proof develops capture-avoiding renaming of FREE occurrences ([sf]) with a
    substitutability side condition ([sok]), vacuous generalization for non-free variables ([vac]),
    specialization and alphabetic variance, by a joint induction on formula size. *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Syntax *)
Fixpoint fr (y : nat) (a : wff) : bool :=
  match a with
  | Weq u v | Wel u v => Nat.eqb u y || Nat.eqb v y
  | Wim a b => fr y a || fr y b
  | Wn a => fr y a
  | Wal z a => if Nat.eqb z y then false else fr y a
  end.

Fixpoint sf (x y : nat) (a : wff) : wff :=
  match a with
  | Weq u v => Weq (rv x y u) (rv x y v)
  | Wel u v => Wel (rv x y u) (rv x y v)
  | Wim a b => Wim (sf x y a) (sf x y b)
  | Wn a => Wn (sf x y a)
  | Wal z a => if Nat.eqb z x then Wal z a else Wal z (sf x y a)
  end.

Fixpoint sok (x y : nat) (a : wff) : bool :=
  match a with
  | Weq _ _ | Wel _ _ => true
  | Wim a b => sok x y a && sok x y b
  | Wn a => sok x y a
  | Wal z a => if Nat.eqb z x then true else if Nat.eqb z y then negb (fr x a) else sok x y a
  end.

Fixpoint size (a : wff) : nat :=
  match a with
  | Weq _ _ | Wel _ _ => 1
  | Wim a b => S (size a + size b)
  | Wn a => S (size a)
  | Wal _ a => S (size a)
  end.

Fixpoint maxv (a : wff) : nat :=
  match a with
  | Weq u v | Wel u v => Nat.max u v
  | Wim a b => Nat.max (maxv a) (maxv b)
  | Wn a => maxv a
  | Wal z a => Nat.max z (maxv a)
  end.

Ltac eqb_cases := repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end.
Ltac eqb_hyps := repeat match goal with h : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in h end.
Ltac orb_hyps := repeat match goal with h : _ || _ = false |- _ => apply orb_false_iff in h as [? ?] end.

Lemma occ_maxv y a : maxv a < y -> occ y a = false.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; rewrite ?orb_false_iff;
    repeat split; try (apply Nat.eqb_neq; lia); try apply IHa; try apply IHa1; try apply IHa2; lia.
Qed.

Lemma size_sf x y a : size (sf x y a) = size a.
Proof. induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; auto. destruct (Nat.eqb w x); cbn; auto. Qed.

Lemma fr_occ y a : occ y a = false -> fr y a = false.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps;
    rewrite ?orb_false_iff; try (split; auto; fail); auto.
  destruct (Nat.eqb w y); auto.
Qed.

Lemma sok_occ x y a : occ y a = false -> sok x y a = true.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps; auto.
  - rewrite IHa1, IHa2 by assumption. reflexivity.
  - destruct (Nat.eqb w x); auto. match goal with h : Nat.eqb w y = false |- _ => rewrite h end. auto.
Qed.

Lemma sf_nofree x y a : fr x a = false -> sf x y a = a.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps.
  - unfold rv. match goal with h1 : Nat.eqb u x = false, h2 : Nat.eqb v x = false |- _ => now rewrite h1, h2 end.
  - unfold rv. match goal with h1 : Nat.eqb u x = false, h2 : Nat.eqb v x = false |- _ => now rewrite h1, h2 end.
  - now rewrite IHa1, IHa2.
  - now rewrite IHa.
  - destruct (Nat.eqb_spec w x); auto. now rewrite IHa.
Qed.

Lemma fr_sf_self x y a : x <> y -> fr x (sf x y a) = false.
Proof.
  intro Hxy. induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn.
  - unfold rv. destruct (Nat.eqb_spec u x); destruct (Nat.eqb_spec v x); cbn;
      apply orb_false_iff; split; apply Nat.eqb_neq; congruence.
  - unfold rv. destruct (Nat.eqb_spec u x); destruct (Nat.eqb_spec v x); cbn;
      apply orb_false_iff; split; apply Nat.eqb_neq; congruence.
  - now rewrite IHa1, IHa2.
  - exact IHa.
  - destruct (Nat.eqb_spec w x) as [->|Hw]; cbn.
    + now rewrite Nat.eqb_refl.
    + apply Nat.eqb_neq in Hw. rewrite Hw. exact IHa.
Qed.

Lemma fr_sf_other x y z a : z <> y -> fr z a = false -> fr z (sf x y a) = false.
Proof.
  intros Hzy. induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps.
  - unfold rv. eqb_hyps. destruct (Nat.eqb_spec u x); destruct (Nat.eqb_spec v x); cbn;
      apply orb_false_iff; split; apply Nat.eqb_neq; congruence.
  - unfold rv. eqb_hyps. destruct (Nat.eqb_spec u x); destruct (Nat.eqb_spec v x); cbn;
      apply orb_false_iff; split; apply Nat.eqb_neq; congruence.
  - rewrite IHa1, IHa2 by assumption. reflexivity.
  - auto.
  - destruct (Nat.eqb w x); cbn; [exact H|]. destruct (Nat.eqb w z); auto.
Qed.

Lemma sf_sf x z a : occ z a = false -> sf z x (sf x z a) = a.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps.
  - eqb_hyps. now rewrite !rv_rv.
  - eqb_hyps. now rewrite !rv_rv.
  - rewrite IHa1, IHa2 by assumption. reflexivity.
  - now rewrite IHa.
  - match goal with h : Nat.eqb w z = false |- _ => rename h into Hwz end.
    destruct (Nat.eqb_spec w x); cbn; rewrite Hwz; [now rewrite sf_nofree by (apply fr_occ; assumption) | now rewrite IHa].
Qed.

Lemma sok_sf_back x z a : occ z a = false -> sok z x (sf x z a) = true.
Proof.
  induction a as [u v|u v|a1 IHa1 a2 IHa2|a IHa|w a IHa]; cbn; intro H; orb_hyps; auto.
  - rewrite IHa1, IHa2 by assumption. reflexivity.
  - match goal with h : Nat.eqb w z = false |- _ => rename h into Hwz end.
    destruct (Nat.eqb_spec w x) as [->|Hwx].
    + cbn. rewrite Hwz, Nat.eqb_refl. now rewrite fr_occ.
    + cbn. rewrite Hwz. apply Nat.eqb_neq in Hwx. rewrite Hwx. auto.
Qed.

(** ** Equivalence congruences *)
Lemma leqv_refl a : leqv a a.
Proof. split; apply lpc_id. Qed.
Lemma leqv_sym a b : leqv a b -> leqv b a.
Proof. intros [H1 H2]; split; assumption. Qed.
Lemma leqv_trans a b c : leqv a b -> leqv b c -> leqv a c.
Proof. intros [H1 H2] [H3 H4]. split; eapply lsyl; eassumption. Qed.
Lemma leqv_im a a' b b' : leqv a a' -> leqv b b' -> leqv (Wim a b) (Wim a' b').
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_lprov, ded, ded.
  - eapply dmp; [apply dthm, H3|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H2 | apply dhyp; simpl; auto].
  - eapply dmp; [apply dthm, H4|]. eapply dmp; [apply dhyp; simpl; auto|]. eapply dmp; [apply dthm, H1 | apply dhyp; simpl; auto].
Qed.
Lemma leqv_n a a' : leqv a a' -> leqv (Wn a) (Wn a').
Proof. intros [H1 H2]. split; apply lcontra; assumption. Qed.
Lemma leqv_al x a a' : leqv a a' -> leqv (Wal x a) (Wal x a').
Proof. intros [H1 H2]. split; apply lal; assumption. Qed.

(** ** Leibniz substitution for free occurrences *)
Lemma leib_sf x y a : sok x y a = true ->
  lprov (Wim (Weq x y) (Wim a (sf x y a))) /\ lprov (Wim (Weq x y) (Wim (sf x y a) a)).
Proof.
  set (h := Weq x y).
  induction a as [u v|u v|a IHa b IHb|a IHa|w c IHc]; cbn [sf sok]; intros Hs.
  - destruct (eq_rv x y u) as [U1 U2]. destruct (eq_rv x y v) as [V1 V2].
    split; apply der_lprov, ded.
    + mp (Weq v (rv x y v)); [mp (Weq u (rv x y u)); [dt (leq_tr_eq u (rv x y u) v (rv x y v))|]|].
      * mp h; [dt U1 | dh].
      * mp h; [dt V1 | dh].
    + mp (Weq (rv x y v) v); [mp (Weq (rv x y u) u); [dt (leq_tr_eq (rv x y u) u (rv x y v) v)|]|].
      * mp h; [dt U2 | dh].
      * mp h; [dt V2 | dh].
  - destruct (eq_rv x y u) as [U1 U2]. destruct (eq_rv x y v) as [V1 V2].
    split; apply der_lprov, ded.
    + mp (Weq v (rv x y v)); [mp (Weq u (rv x y u)); [dt (leq_tr_el u (rv x y u) v (rv x y v))|]|].
      * mp h; [dt U1 | dh].
      * mp h; [dt V1 | dh].
    + mp (Weq (rv x y v) v); [mp (Weq (rv x y u) u); [dt (leq_tr_el (rv x y u) u (rv x y v) v)|]|].
      * mp h; [dt U2 | dh].
      * mp h; [dt V2 | dh].
  - apply andb_true_iff in Hs as [Ha Hb].
    destruct (IHa Ha) as [A1 A2]. destruct (IHb Hb) as [B1' B2'].
    split; apply der_lprov, ded, ded, ded.
    + mp b; [mp h; [dt B1' | dh] | mp a; [dh | mp (sf x y a); [mp h; [dt A2 | dh] | dh]]].
    + mp (sf x y b); [mp h; [dt B2' | dh] | mp (sf x y a); [dh | mp a; [mp h; [dt A1 | dh] | dh]]].
  - destruct (IHa Hs) as [A1 A2].
    split; apply der_lprov, ded.
    + mp (Wim (sf x y a) a); [dt (lpc_contra (sf x y a) a) | mp h; [dt A2 | dh]].
    + mp (Wim a (sf x y a)); [dt (lpc_contra a (sf x y a)) | mp h; [dt A1 | dh]].
  - assert (Triv : lprov (Wim h (Wim (Wal w c) (Wal w c)))) by exact (LDET _ _ (lpc_K _ _) (lpc_id _)).
    destruct (Nat.eqb_spec w x) as [Hwx|Hwx]; [split; exact Triv|].
    destruct (Nat.eqb_spec w y) as [Hwy|Hwy].
    + rewrite sf_nofree by (now apply negb_true_iff in Hs). split; exact Triv.
    + destruct (IHc Hs) as [A1 A2].
      assert (V : lprov (Wim h (Wal w h))).
      { apply lvac. cbn. apply orb_false_iff. split; apply Nat.eqb_neq; congruence. }
      split.
      * exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 w h _) (LGEN w _ A1)) (LB4 w c _))).
      * exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 w h _) (LGEN w _ A2)) (LB4 w _ c))).
Qed.

(** ** Vacuous generalization, specialization, alphabetic variance (joint size induction) *)
Definition PM (n : nat) : Prop :=
  forall a y, size a <= n -> fr y a = false -> lprov (Wim a (Wal y a)).

Lemma spec_n n (HM : PM n) x y a : size a <= n -> x <> y -> sok x y a = true ->
  lprov (Wim (Wal x a) (sf x y a)).
Proof.
  intros Hn Hxy Hs. set (a' := sf x y a).
  destruct (leib_sf x y a Hs) as [L _].
  pose proof (LDET _ _ (lpc_C _ _ _) L) as L'.
  pose proof (lal x _ _ L') as H1.
  pose proof (lsyl _ _ _ H1 (lall_ex x (Weq x y) a')) as H2.
  pose proof (LDET _ _ (LDET _ _ (lpc_C _ _ _) H2) (LB7 x y)) as H3.
  assert (Ha' : lprov (Wim a' (Wal x a'))).
  { apply HM; [unfold a'; now rewrite size_sf | now apply fr_sf_self]. }
  exact (lsyl _ _ _ H3 (lsyl _ _ _ (lex x _ _ Ha') (LB6c x a'))).
Qed.

Lemma alpha_n n (HM : PM n) x z a : size a <= n -> x <> z -> fr z a = false -> sok x z a = true ->
  lprov (Wim (Wal x a) (Wal z (sf x z a))).
Proof.
  intros Hn Hxz Hz Hs.
  pose proof (spec_n n HM x z a Hn Hxz Hs) as H1.
  pose proof (lal z _ _ H1) as G.
  pose proof (lal x _ _ (HM a z Hn Hz)) as V.
  exact (lsyl _ _ _ (lsyl _ _ _ V (LB6b x z a)) G).
Qed.

Lemma PM_S n : PM n -> PM (S n).
Proof.
  intros HM a y Hn Hy. destruct a as [u v|u v|a b|a|w c]; cbn [fr size] in *.
  - apply orb_false_iff in Hy as [H1 H2]. apply Nat.eqb_neq in H1, H2.
    exact (LDET _ _ (lpc_andl _ _) (LB6a u v y H1 H2)).
  - apply orb_false_iff in Hy as [H1 H2]. apply Nat.eqb_neq in H1, H2.
    exact (LDET _ _ (lpc_andr _ _) (LB6a u v y H1 H2)).
  - apply orb_false_iff in Hy as [Ha Hb].
    set (X := Wal y (Wim a b)).
    assert (H1 : lprov (Wim (Wn a) X)).
    { pose proof (lneg_vac y a (HM a y ltac:(lia) Ha)) as N.
      refine (lsyl _ _ _ N (lal y _ _ _)).
      exact (LDET _ _ (lpc_C _ _ _) (LB3 a b)). }
    assert (H2 : lprov (Wim b X)).
    { exact (lsyl _ _ _ (HM b y ltac:(lia) Hb) (lal y _ _ (lpc_K b a))). }
    apply der_lprov, ded. mp (Wim (Wn X) X); [dt (LB2 X)|]. apply ded.
    mp (Wn a); [dt H1|]. mp (Wn b).
    + mp (Wim a b); [dt (lpc_contra a b) | dh].
    + mp (Wn X); [dt (lcontra _ _ H2) | dh].
  - exact (lneg_vac y a (HM a y ltac:(lia) Hy)).
  - destruct (Nat.eqb_spec w y) as [->|Hwy].
    + set (z := S (maxv c + y)). set (c' := sf y z c).
      assert (Hzc : occ z c = false) by (apply occ_maxv; unfold z; lia).
      assert (Hyz : y <> z) by (unfold z; lia).
      assert (A1 : lprov (Wim (Wal y c) (Wal z c'))).
      { apply (alpha_n n HM); [lia | exact Hyz | now apply fr_occ | now apply sok_occ]. }
      assert (Hyc' : fr y c' = false) by (now apply fr_sf_self).
      assert (A2 : lprov (Wim (Wal z c') (Wal y (Wal z c')))).
      { refine (lsyl _ _ _ (lal z _ _ (HM c' y _ Hyc')) (LB6b z y c')). unfold c'; rewrite size_sf; lia. }
      assert (A3 : lprov (Wim (Wal z c') (Wal y c))).
      { pose proof (alpha_n n HM z y c') as H.
        assert (E : sf z y c' = c) by (unfold c'; now rewrite sf_sf). rewrite E in H.
        apply H; [unfold c'; rewrite size_sf; lia | congruence | exact Hyc' | now apply sok_sf_back]. }
      exact (lsyl _ _ _ A1 (lsyl _ _ _ A2 (lal y _ _ A3))).
    + cbn in Hy.
      exact (lsyl _ _ _ (lal w _ _ (HM c y ltac:(lia) Hy)) (LB6b w y c)).
Qed.

Lemma PM_all n : PM n.
Proof.
  induction n as [|n IH]; [intros a y Hn; destruct a; cbn in Hn; lia | now apply PM_S].
Qed.

Theorem vac a y : fr y a = false -> lprov (Wim a (Wal y a)).
Proof. apply (PM_all (size a)). lia. Qed.

Theorem spec_sf x y a : x <> y -> sok x y a = true -> lprov (Wim (Wal x a) (sf x y a)).
Proof. apply (spec_n (size a) (PM_all _)). lia. Qed.

Theorem alpha_sf x z a : x <> z -> fr z a = false -> sok x z a = true ->
  lprov (Wim (Wal x a) (Wal z (sf x z a))).
Proof. apply (alpha_n (size a) (PM_all _)). lia. Qed.

Lemma alpha_fresh x z a : x <> z -> occ z a = false -> leqv (Wal x a) (Wal z (sf x z a)).
Proof.
  intros Hxz Hz. split.
  - apply alpha_sf; [exact Hxz | now apply fr_occ | now apply sok_occ].
  - pose proof (alpha_sf z x (sf x z a)) as H. rewrite sf_sf in H by exact Hz.
    apply H; [congruence | now apply fr_sf_self | now apply sok_sf_back].
Qed.

(** ** de Bruijn images *)
Notation form := (@Core.form sig_empty ZF_pred_sig full_operators falsity_on).

Lemma dB_ext_fr (rho rho' : nat -> term) a : (forall v, fr v a = true -> rho v = rho' v) -> dB rho a = dB rho' a.
Proof.
  revert rho rho'; induction a as [u v|u v|a IHa b IHb|a IHa|w c IHc]; intros rho rho' H; cbn [dB fr] in *.
  - rewrite (H u), (H v); auto; apply orb_true_iff; [right|left]; apply Nat.eqb_refl.
  - rewrite (H u), (H v); auto; apply orb_true_iff; [right|left]; apply Nat.eqb_refl.
  - rewrite (IHa rho rho'), (IHb rho rho'); auto; intros v Hv; apply H; apply orb_true_iff; auto.
  - now rewrite (IHa rho rho').
  - f_equal. apply IHc. intros v Hv. unfold shift_env. destruct (Nat.eqb_spec v w); [reflexivity|].
    f_equal. apply H. destruct (Nat.eqb_spec w v); [congruence | exact Hv].
Qed.

Definition upd (rho : nat -> term) (x : nat) (t : term) : nat -> term :=
  fun v => if Nat.eqb v x then t else rho v.

Lemma dB_sf (rho : nat -> term) x y a : sok x y a = true -> dB rho (sf x y a) = dB (upd rho x (rho y)) a.
Proof.
  revert rho; induction a as [u v|u v|a IHa b IHb|a IHa|w c IHc]; intros rho Hs; cbn [dB sf sok] in *.
  - unfold rv, upd. destruct (Nat.eqb u x), (Nat.eqb v x); reflexivity.
  - unfold rv, upd. destruct (Nat.eqb u x), (Nat.eqb v x); reflexivity.
  - apply andb_true_iff in Hs as [Ha Hb]. now rewrite IHa, IHb.
  - now rewrite IHa.
  - destruct (Nat.eqb_spec w x) as [->|Hwx].
    + cbn. f_equal. apply dB_ext. intros v. unfold shift_env, upd. destruct (Nat.eqb_spec v x); reflexivity.
    + destruct (Nat.eqb_spec w y) as [->|Hwy].
      * apply negb_true_iff in Hs. rewrite sf_nofree by exact Hs.
        cbn. f_equal. apply dB_ext_fr. intros v Hv. unfold shift_env, upd.
        destruct (Nat.eqb_spec v y); [reflexivity|]. destruct (Nat.eqb_spec v x); [subst; congruence | reflexivity].
      * cbn. f_equal. rewrite IHc by exact Hs. apply dB_ext. intros v. unfold shift_env, upd.
        eqb_cases; subst; try congruence; reflexivity.
Qed.

Definition injective (rho : nat -> term) : Prop := forall u v, rho u = rho v -> u = v.

Lemma shift_inj (s t : term) : s`[↑] = t`[↑] -> s = t.
Proof. destruct s as [m|[]], t as [n|[]]; cbn; intros H; inversion H; reflexivity. Qed.

Lemma shift_neq0 (t : term) : t`[↑] <> var 0.
Proof. destruct t as [m|[]]; cbn; discriminate. Qed.

Lemma injective_shift (rho : nat -> term) z : injective rho -> injective (shift_env z rho).
Proof.
  intros H u v. unfold shift_env. destruct (Nat.eqb_spec u z), (Nat.eqb_spec v z); intros E; subst; auto.
  - symmetry in E. now apply shift_neq0 in E.
  - now apply shift_neq0 in E.
  - now apply H, shift_inj.
Qed.

(** projections used to invert equalities of library formulas *)
Definition kind (phi : form) : nat :=
  match phi with
  | falsity => 0
  | atom P _ => match P with elem => 1 | equal => 2 end
  | bin _ _ _ => 3
  | quant _ _ => 4
  end.

Definition arg1 (phi : form) : term :=
  match phi with
  | atom P v => (match P return Vector.t term (ar_preds P) -> term with
                 | elem => fun v => Vector.hd v | equal => fun v => Vector.hd v end) v
  | _ => var 0
  end.

Definition arg2 (phi : form) : term :=
  match phi with
  | atom P v => (match P return Vector.t term (ar_preds P) -> term with
                 | elem => fun v => Vector.hd (Vector.tl v) | equal => fun v => Vector.hd (Vector.tl v) end) v
  | _ => var 0
  end.

Definition left {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : @Core.form sig_empty ZF_pred_sig full_operators ff :=
  match phi in Core.form ff' return Core.form ff' with
  | falsity => falsity | atom P v => atom P v | bin _ a _ => a | quant q a => quant q a end.
Definition right {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : @Core.form sig_empty ZF_pred_sig full_operators ff :=
  match phi in Core.form ff' return Core.form ff' with
  | falsity => falsity | atom P v => atom P v | bin _ _ b => b | quant q a => quant q a end.
Definition body {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : @Core.form sig_empty ZF_pred_sig full_operators ff :=
  match phi in Core.form ff' return Core.form ff' with
  | falsity => falsity | atom P v => atom P v | bin o a b => bin o a b | quant _ a => a end.

Lemma dB_kind (rho : nat -> term) a : kind (dB rho a) <> 0.
Proof. destruct a; cbn; discriminate. Qed.

Theorem alpha_dB_n n : forall a b (rho : nat -> term), size a <= n -> injective rho ->
  dB rho a = dB rho b -> leqv a b.
Proof.
  induction n as [|n IH]; intros a b rho Hn Hr E; [destruct a; cbn in Hn; lia|].
  destruct a as [u v|u v|a1 a2|a1|x c], b as [u' v'|u' v'|b1 b2|b1|y d];
    pose proof (f_equal kind E) as Ek; cbn in Ek; try discriminate.
  - apply (f_equal arg1) in E as E1. apply (f_equal arg2) in E as E2. cbn in E1, E2.
    apply Hr in E1. apply Hr in E2. subst. apply leqv_refl.
  - apply (f_equal arg1) in E as E1. apply (f_equal arg2) in E as E2. cbn in E1, E2.
    apply Hr in E1. apply Hr in E2. subst. apply leqv_refl.
  - apply (f_equal left) in E as E1. apply (f_equal right) in E as E2. cbn in E1, E2, Hn.
    apply leqv_im; [eapply (IH _ _ rho) | eapply (IH _ _ rho)]; eauto; lia.
  - apply (f_equal right) in E. cbn in E. exfalso. apply (dB_kind rho a2). now rewrite E.
  - apply (f_equal right) in E. cbn in E. exfalso. apply (dB_kind rho b2). now rewrite <- E.
  - apply (f_equal left) in E. cbn in E, Hn. apply leqv_n. eapply (IH _ _ rho); eauto; lia.
  - apply (f_equal body) in E. cbn in E, Hn.
    set (z := S (maxv c + maxv d + x + y)).
    assert (Hzc : occ z c = false) by (apply occ_maxv; unfold z; lia).
    assert (Hzd : occ z d = false) by (apply occ_maxv; unfold z; lia).
    assert (Hxz : x <> z) by (unfold z; lia). assert (Hyz : y <> z) by (unfold z; lia).
    assert (Ec : dB (shift_env z rho) (sf x z c) = dB (shift_env x rho) c).
    { rewrite dB_sf by (now apply sok_occ). apply dB_ext_fr. intros v Hv. unfold upd, shift_env.
      destruct (Nat.eqb_spec v x); [now rewrite Nat.eqb_refl|].
      destruct (Nat.eqb_spec v z); [subst; rewrite fr_occ in Hv by exact Hzc; discriminate | reflexivity]. }
    assert (Ed : dB (shift_env z rho) (sf y z d) = dB (shift_env y rho) d).
    { rewrite dB_sf by (now apply sok_occ). apply dB_ext_fr. intros v Hv. unfold upd, shift_env.
      destruct (Nat.eqb_spec v y); [now rewrite Nat.eqb_refl|].
      destruct (Nat.eqb_spec v z); [subst; rewrite fr_occ in Hv by exact Hzd; discriminate | reflexivity]. }
    assert (Hcd : leqv (sf x z c) (sf y z d)).
    { apply (IH _ _ (shift_env z rho)); [rewrite size_sf; lia | now apply injective_shift | congruence]. }
    eapply leqv_trans; [apply (alpha_fresh x z c Hxz Hzc)|].
    eapply leqv_trans; [apply leqv_al, Hcd|].
    apply leqv_sym, (alpha_fresh y z d Hyz Hzd).
Qed.

Theorem alpha_dB a b (rho : nat -> term) : injective rho -> dB rho a = dB rho b -> leqv a b.
Proof. apply (alpha_dB_n (size a)). lia. Qed.
