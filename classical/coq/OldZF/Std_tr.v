(** * Std_tr: library de Bruijn formulas (minimal signature) -> named wffs (Logic.v).

    [tr eta phi]: [eta] maps de Bruijn indices to named variables.  A quantifier over [phi] binds the
    name [bname (qd phi)] (even, >= 2), where [qd] is the quantifier depth; so the names a formula's
    binders get do not depend on its context, and translation commutes EXACTLY with renaming
    substitutions (no alpha-conversion needed).  Free variables are given odd names by the caller.
    [falsity] becomes the closed refutable wff [botw] := -. A. v0 v0 = v0 (name 0 is never a binder
    name or a free name).  [phi -> falsity] becomes a negation, so the image of [dB] round-trips. *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF.
From OldZF Require Import Logic L1_LMeta.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Notation form := (@Core.form sig_empty ZF_pred_sig full_operators falsity_on).

Definition botw : wff := Wn (Wal 0 (Weq 0 0)).
Definition bname (k : nat) : nat := 2 * k + 2.
Arguments bname : simpl never.

Fixpoint qd {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 0
  | atom _ _ => 0
  | bin _ a b => Nat.max (qd a) (qd b)
  | quant _ a => S (qd a)
  end.

Definition tv (eta : nat -> nat) (t : term) : nat :=
  match t with
  | var n => eta n
  | func f _ => match f with end
  end.

Fixpoint tr {ff} (eta : nat -> nat) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : wff :=
  match phi with
  | falsity => botw
  | atom P v =>
      match P return Vector.t term (ar_preds P) -> wff with
      | elem => fun v => Wel (tv eta (Vector.hd v)) (tv eta (Vector.hd (Vector.tl v)))
      | equal => fun v => Weq (tv eta (Vector.hd v)) (tv eta (Vector.hd (Vector.tl v)))
      end v
  | bin Conj a b => Wa (tr eta a) (tr eta b)
  | bin Disj a b => Wim (Wn (tr eta a)) (tr eta b)
  | bin Impl a b =>
      match b with
      | falsity => Wn (tr eta a)
      | _ => Wim (tr eta a) (tr eta b)
      end
  | quant All a => Wal (bname (qd a)) (tr (scons (bname (qd a)) eta) a)
  | quant Ex a => Wex (bname (qd a)) (tr (scons (bname (qd a)) eta) a)
  end.

(** ** Basic properties *)
Definition idx (t : term) : nat :=
  match t with
  | var n => n
  | func f _ => match f with end
  end.

Lemma tv_idx eta t : tv eta t = eta (idx t).
Proof. destruct t as [n|[]]. reflexivity. Qed.

Lemma vec2 (v : Vector.t term 2) : v = Vector.cons _ (Vector.hd v) _ (Vector.cons _ (Vector.hd (Vector.tl v)) _ (Vector.nil _)).
Proof.
  assert (E3 : Vector.tl (Vector.tl v) = Vector.nil _)
    by (apply (Vector.case0 (fun u => u = Vector.nil _)); reflexivity).
  rewrite (Vector.eta v) at 1. f_equal. rewrite (Vector.eta (Vector.tl v)) at 1. f_equal. exact E3.
Qed.

Lemma tr_ext {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta eta' :
  (forall n, eta n = eta' n) -> tr eta phi = tr eta' phi.
Proof.
  revert eta eta'; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta eta' H; cbn.
  - reflexivity.
  - destruct P; cbn; now rewrite !tv_idx, !H.
  - destruct op.
    + now rewrite (IHa eta eta'), (IHb eta eta').
    + now rewrite (IHa eta eta'), (IHb eta eta').
    + destruct b; try now rewrite (IHa eta eta').
      all: now rewrite (IHa eta eta'), (IHb eta eta').
  - destruct q; f_equal; apply IHa; intros []; cbn; auto.
Qed.

Lemma qd_subst {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) sigma : qd (phi[sigma]) = qd phi.
Proof.
  revert sigma; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros sigma; cbn; auto.
Qed.

Lemma tr_subst {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta sigma s :
  (forall n, sigma n = var (s n)) -> tr eta (phi[sigma]) = tr (fun n => eta (s n)) phi.
Proof.
  revert eta sigma s; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta sigma s H; cbn.
  - reflexivity.
  - destruct P; cbn in v |- *; rewrite (vec2 v); cbn; rewrite !tv_idx;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn;
      rewrite !H; reflexivity.
  - destruct op.
    + now rewrite (IHa eta sigma s H), (IHb eta sigma s H).
    + now rewrite (IHa eta sigma s H), (IHb eta sigma s H).
    + destruct b; cbn; try now rewrite (IHa eta sigma s H).
      all: rewrite (IHa eta sigma s H); f_equal; exact (IHb eta sigma s H).
  - rewrite qd_subst. destruct q; f_equal;
      (rewrite (IHa _ _ (fun n => match n with 0 => 0 | S n => S (s n) end));
       [apply tr_ext; intros []; reflexivity | intros []; cbn; [reflexivity | unfold funcomp; now rewrite H]]).
Qed.

(** ** Free indices, occurrence, binders, renaming *)
Fixpoint fb {ff} (N : nat) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : Prop :=
  match phi with
  | falsity => True
  | atom P v =>
      match P return Vector.t term (ar_preds P) -> Prop with
      | elem => fun v => idx (Vector.hd v) < N /\ idx (Vector.hd (Vector.tl v)) < N
      | equal => fun v => idx (Vector.hd v) < N /\ idx (Vector.hd (Vector.tl v)) < N
      end v
  | bin _ a b => fb N a /\ fb N b
  | quant _ a => fb (S N) a
  end.

Lemma fb_mono {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) N M :
  fb N phi -> N <= M -> fb M phi.
Proof.
  revert N M; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N M H HM; cbn in *.
  - exact I.
  - destruct P; cbn in *; lia.
  - destruct H; split; eauto.
  - apply (IHa (S N)); [exact H | lia].
Qed.

Lemma fb_exists {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : exists N, fb N phi.
Proof.
  induction phi as [|ff P v|ff op a [N HN] b [M HM]|ff q a [N HN]].
  - exists 0. exact I.
  - destruct P; cbn; exists (S (idx (Vector.hd v) + idx (Vector.hd (Vector.tl v)))); lia.
  - exists (N + M). split; eapply fb_mono; eauto; lia.
  - exists N. cbn. eapply fb_mono; eauto.
Qed.

Lemma fb_exists_L (A : list form) : exists N, forall phi, In phi A -> fb N phi.
Proof.
  induction A as [|a A [N HN]].
  - exists 0. intros _ [].
  - destruct (fb_exists a) as [M HM]. exists (N + M). intros phi [<-|H].
    + eapply fb_mono; eauto; lia.
    + eapply fb_mono; eauto; lia.
Qed.

Definition notbinder {ff} (y : nat) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : Prop :=
  y <> 0 /\ forall k, k < qd phi -> y <> bname k.

Lemma notbinder_odd {ff} y (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : Nat.odd y = true -> notbinder y phi.
Proof.
  intros H. split.
  - intros ->. discriminate.
  - intros k _ ->. unfold bname in H. rewrite Nat.odd_add, Nat.odd_mul in H. discriminate.
Qed.

Lemma notbinder_bin_l {ff} y op (a b : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  notbinder y (bin op a b) -> notbinder y a.
Proof. intros [H0 H]. split; [exact H0|]. intros k Hk. apply H. cbn. lia. Qed.

Lemma notbinder_bin_r {ff} y op (a b : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  notbinder y (bin op a b) -> notbinder y b.
Proof. intros [H0 H]. split; [exact H0|]. intros k Hk. apply H. cbn. lia. Qed.

Lemma notbinder_quant {ff} y q (a : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  notbinder y (quant q a) -> notbinder y a /\ y <> bname (qd a).
Proof. intros [H0 H]. split; [split; [exact H0|] |]; intros; apply H; cbn; lia. Qed.

Lemma occ_tr {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) N eta y :
  fb N phi -> (forall n, n < N -> eta n <> y) -> notbinder y phi -> occ y (tr eta phi) = false.
Proof.
  revert N eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N eta Hfb Heta Hnb; cbn in *.
  - destruct Hnb as [H0 _]. unfold botw; cbn. destruct y; [congruence | reflexivity].
  - destruct P; cbn in *; rewrite !tv_idx; destruct Hfb as [H1 H2];
      apply orb_false_iff; split; apply Nat.eqb_neq; apply Heta; assumption.
  - destruct Hfb as [Ha Hb].
    assert (Ea : occ y (tr eta a) = false) by (eapply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb N eta Hb Heta (notbinder_bin_r Hnb)).
    + now rewrite Ea, (IHb N eta Hb Heta (notbinder_bin_r Hnb)).
    + destruct b; cbn; try exact Ea.
      all: rewrite Ea; exact (IHb N eta Hb Heta (notbinder_bin_r Hnb)).
  - destruct (notbinder_quant Hnb) as [Hnb' HB].
    assert (E : occ y (tr (scons (bname (qd a)) eta) a) = false).
    { apply (IHa (S N)); [exact Hfb | | exact Hnb']. intros [|n] Hn; cbn; [unfold bname in *; lia | apply Heta; lia]. }
    assert (HB' : Nat.eqb (bname (qd a)) y = false) by (apply Nat.eqb_neq; congruence).
    destruct q; cbn [tr occ Wex]; rewrite HB', E; reflexivity.
Qed.

Lemma bnd_tr {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta z :
  notbinder z phi -> bnd z (tr eta phi) = false.
Proof.
  revert eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta Hnb; cbn in *.
  - destruct Hnb as [H0 _]. unfold botw; cbn. destruct z; [congruence | reflexivity].
  - destruct P; reflexivity.
  - assert (Ea : bnd z (tr eta a) = false) by (eapply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb eta (notbinder_bin_r Hnb)).
    + now rewrite Ea, (IHb eta (notbinder_bin_r Hnb)).
    + destruct b; cbn; try exact Ea.
      all: rewrite Ea; exact (IHb eta (notbinder_bin_r Hnb)).
  - destruct (notbinder_quant Hnb) as [Hnb' HB].
    assert (HB' : Nat.eqb (bname (qd a)) z = false) by (apply Nat.eqb_neq; congruence).
    destruct q; cbn [tr bnd Wex]; rewrite HB', IHa by exact Hnb'; reflexivity.
Qed.

Lemma ren_tr {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta x y :
  notbinder x phi -> notbinder y phi -> ren x y (tr eta phi) = tr (fun n => rv x y (eta n)) phi.
Proof.
  revert eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta Hx Hy; cbn in *.
  - destruct Hx as [H0 _]. unfold botw, rv. cbn. destruct x; [congruence | reflexivity].
  - destruct P; cbn; rewrite !tv_idx; reflexivity.
  - assert (Ea : ren x y (tr eta a) = tr (fun n => rv x y (eta n)) a)
      by (apply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb eta (notbinder_bin_r Hx) (notbinder_bin_r Hy)).
    + now rewrite Ea, (IHb eta (notbinder_bin_r Hx) (notbinder_bin_r Hy)).
    + destruct b; cbn; try now rewrite Ea.
      all: rewrite Ea; f_equal; exact (IHb eta (notbinder_bin_r Hx) (notbinder_bin_r Hy)).
  - destruct (notbinder_quant Hx) as [Hx' HBx]. destruct (notbinder_quant Hy) as [Hy' HBy].
    assert (Hr : rv x y (bname (qd a)) = bname (qd a))
      by (unfold rv; apply Nat.eqb_neq in HBx; rewrite Nat.eqb_sym, HBx; reflexivity).
    destruct q; cbn [tr]; unfold Wex; cbn [ren]; rewrite Hr, IHa by assumption;
      [f_equal | do 3 f_equal]; apply tr_ext; intros []; cbn; auto.
Qed.
