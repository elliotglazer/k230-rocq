(** * L1_LMeta: pure-logic metatheory for [lprov]: a deduction theorem, vacuous generalization,
    Leibniz substitution, specialization and alphabetic variance (renaming bound variables),
    and an equivalence relation [ae] (alpha-renaming, = symmetry, /\ commutativity, congruence)
    that is sound for logical equivalence. *)
From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From OldZF Require Import Logic L1_LDef L1_LProp.
Import ListNotations.

(** ** Derived rules *)
Lemma lsyl a b c : lprov (Wim a b) -> lprov (Wim b c) -> lprov (Wim a c).
Proof. intros H1 H2. exact (LDET _ _ (LDET _ _ (LB1 a b c) H1) H2). Qed.

Lemma lcontra a b : lprov (Wim a b) -> lprov (Wim (Wn b) (Wn a)).
Proof. intro H. exact (LDET _ _ (lpc_contra a b) H). Qed.

Lemma lal x a b : lprov (Wim a b) -> lprov (Wim (Wal x a) (Wal x b)).
Proof. intro H. exact (LDET _ _ (LB4 x a b) (LGEN x _ H)). Qed.

Lemma lex x a b : lprov (Wim a b) -> lprov (Wim (Wex x a) (Wex x b)).
Proof. intro H. unfold Wex. apply lcontra, lal, lcontra, H. Qed.

(** ** Deduction theorem (propositional, no GEN under hypotheses) *)
Inductive der (G : list wff) : wff -> Prop :=
  | dhyp a : In a G -> der G a
  | dthm a : lprov a -> der G a
  | dmp a b : der G (Wim a b) -> der G a -> der G b.

Lemma ruleS G h a b : der G (Wim h (Wim a b)) -> der G (Wim h a) -> der G (Wim h b).
Proof.
  intros H1 H2.
  assert (H3 : der G (Wim a (Wim h b))) by exact (dmp _ _ _ (dthm _ _ (lpc_C h a b)) H1).
  assert (H4 : der G (Wim h (Wim h b))).
  { exact (dmp _ _ _ (dmp _ _ _ (dthm _ _ (LB1 h a (Wim h b))) H2) H3). }
  exact (dmp _ _ _ (dthm _ _ (lpc_W h b)) H4).
Qed.

Lemma ded G h a : der (h :: G) a -> der G (Wim h a).
Proof.
  induction 1 as [a [<-|Ha] | a Ha | a b _ IH1 _ IH2].
  - apply dthm, lpc_id.
  - exact (dmp _ _ _ (dthm _ _ (lpc_K a h)) (dhyp _ _ Ha)).
  - exact (dmp _ _ _ (dthm _ _ (lpc_K a h)) (dthm _ _ Ha)).
  - exact (ruleS _ _ _ _ IH1 IH2).
Qed.

Lemma der_lprov a : der [] a -> lprov a.
Proof. induction 1 as [a []| |]; [assumption | exact (LDET _ _ IHder1 IHder2)]. Qed.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ a).

(** ** Equality *)
Lemma leq_refl x : lprov (Weq x x).
Proof.
  set (z := S x).
  assert (h3 : lprov (Wim (Weq z x) (Weq x x))) by exact (LDET _ _ (lpc_W _ _) (LB8a z x x)).
  assert (h5 : lprov (Wim (Weq x x) (Wal z (Weq x x)))).
  { exact (LDET _ _ (lpc_andl _ _) (LB6a x x z ltac:(lia) ltac:(lia))). }
  pose proof (lex z _ _ (lsyl _ _ _ h3 h5)) as h7.
  exact (LDET _ _ (LB6c z (Weq x x)) (LDET _ _ h7 (LB7 z x))).
Qed.

Lemma leq_sym x y : lprov (Wim (Weq x y) (Weq y x)).
Proof.
  apply der_lprov, ded. mp (Weq x x); [mp (Weq x y); [dt (LB8a x y x) | dh] | dt (leq_refl x)].
Qed.

(** u = u', v = v' transport atoms *)
Lemma leq_tr_eq u u' v v' : lprov (Wim (Weq u u') (Wim (Weq v v') (Wim (Weq u v) (Weq u' v')))).
Proof.
  apply der_lprov, ded, ded, ded.
  (* G = [u=v; v=v'; u=u'] *)
  assert (Hu'v : der [Weq u v; Weq v v'; Weq u u'] (Weq u' v)).
  { mp (Weq u v); [mp (Weq u u'); [dt (LB8a u u' v) | dh] | dh]. }
  assert (Hvu' : der [Weq u v; Weq v v'; Weq u u'] (Weq v u')).
  { mp (Weq u' v); [dt (leq_sym u' v) | exact Hu'v]. }
  mp (Weq v v'); [mp (Weq v u'); [dt (LB8a v u' v') | exact Hvu'] | dh].
Qed.

Lemma leq_tr_el u u' v v' : lprov (Wim (Weq u u') (Wim (Weq v v') (Wim (Wel u v) (Wel u' v')))).
Proof.
  apply der_lprov, ded, ded, ded.
  mp (Wel u' v).
  - mp (Weq v v'); [dt (LB8c v v' u') | dh].
  - mp (Wel u v); [mp (Weq u u'); [dt (LB8b u u' v) | dh] | dh].
Qed.

(** ** Syntax: occurrence, binders, renaming *)
Definition rv (x y v : nat) : nat := if Nat.eqb v x then y else v.

Fixpoint ren (x y : nat) (a : wff) : wff :=
  match a with
  | Weq u v => Weq (rv x y u) (rv x y v)
  | Wel u v => Wel (rv x y u) (rv x y v)
  | Wim a b => Wim (ren x y a) (ren x y b)
  | Wn a => Wn (ren x y a)
  | Wal z a => Wal (rv x y z) (ren x y a)
  end.

Fixpoint occ (y : nat) (a : wff) : bool :=
  match a with
  | Weq u v | Wel u v => Nat.eqb u y || Nat.eqb v y
  | Wim a b => occ y a || occ y b
  | Wn a => occ y a
  | Wal z a => Nat.eqb z y || occ y a
  end.

Fixpoint bnd (y : nat) (a : wff) : bool :=
  match a with
  | Weq _ _ | Wel _ _ => false
  | Wim a b => bnd y a || bnd y b
  | Wn a => bnd y a
  | Wal z a => Nat.eqb z y || bnd y a
  end.

Lemma occ_bnd y a : occ y a = false -> bnd y a = false.
Proof. induction a; simpl; intros; rewrite ?orb_false_iff in *; intuition. Qed.

Lemma rv_self x y v : x <> y -> Nat.eqb (rv x y v) x = false.
Proof. intro. unfold rv. destruct (Nat.eqb_spec v x); apply Nat.eqb_neq; lia. Qed.

Lemma occ_ren_self x y a : x <> y -> occ x (ren x y a) = false.
Proof. intro H. induction a; simpl; rewrite ?rv_self, ?IHa, ?IHa1, ?IHa2 by exact H; reflexivity. Qed.

Lemma rv_rv x y v : v <> y -> rv y x (rv x y v) = v.
Proof.
  intro. unfold rv. destruct (Nat.eqb_spec v x).
  - rewrite Nat.eqb_refl. congruence.
  - destruct (Nat.eqb_spec v y); congruence.
Qed.

Lemma ren_ren x y a : occ y a = false -> ren y x (ren x y a) = a.
Proof.
  induction a as [u v|u v|a IHa b IHb|a IHa|z a IHa]; simpl; intro H.
  - apply orb_false_iff in H as [H1 H2]. apply Nat.eqb_neq in H1, H2.
    now rewrite !rv_rv by assumption.
  - apply orb_false_iff in H as [H1 H2]. apply Nat.eqb_neq in H1, H2.
    now rewrite !rv_rv by assumption.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHa, IHb.
  - now rewrite IHa.
  - apply orb_false_iff in H as [H1 H2]. apply Nat.eqb_neq in H1.
    now rewrite rv_rv, IHa.
Qed.

Lemma bnd_ren x y z a : bnd x a = false -> bnd z (ren x y a) = bnd z a.
Proof.
  induction a as [u v|u v|a IHa b IHb|a IHa|w a IHa]; simpl; intro H; try reflexivity.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHa, IHb.
  - now rewrite IHa.
  - apply orb_false_iff in H as [H1 H2]. unfold rv. rewrite H1. now rewrite IHa.
Qed.

(** ** Vacuous generalization *)
Lemma lneg_vac y a : lprov (Wim a (Wal y a)) -> lprov (Wim (Wn a) (Wal y (Wn a))).
Proof.
  intro H.
  (* B6c: E. y A. y a -> a, i.e. -. A. y -. A. y a -> a *)
  pose proof (lcontra _ _ (LB6c y a)) as H1.          (* -. a -> -. -. A. y -. A. y a *)
  pose proof (lsyl _ _ _ H1 (lpc_nn_elim _)) as H2.    (* -. a -> A. y -. A. y a *)
  exact (lsyl _ _ _ H2 (lal y _ _ (lcontra _ _ H))).
Qed.

Lemma lvac y a : occ y a = false -> lprov (Wim a (Wal y a)).
Proof.
  induction a as [u v|u v|a IHa b IHb|a IHa|z a IHa]; simpl; intro H;
    try (apply orb_false_iff in H as [H0 H0']);
    repeat match goal with h : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in h end.
  - exact (LDET _ _ (lpc_andl _ _) (LB6a u v y ltac:(assumption) ltac:(assumption))).
  - exact (LDET _ _ (lpc_andr _ _) (LB6a u v y ltac:(assumption) ltac:(assumption))).
  - set (X := Wal y (Wim a b)).
    assert (H1 : lprov (Wim (Wn a) X)).
    { pose proof (lneg_vac y a (IHa ltac:(assumption))) as N.
      refine (lsyl _ _ _ N (lal y _ _ _)).
      exact (LDET _ _ (lpc_C _ _ _) (LB3 a b)). }
    assert (H2 : lprov (Wim b X)).
    { exact (lsyl _ _ _ (IHb ltac:(assumption)) (lal y _ _ (lpc_K b a))). }
    apply der_lprov, ded. mp (Wim (Wn X) X); [dt (LB2 X)|]. apply ded.
    mp (Wn a); [dt H1|]. mp (Wn b).
    + mp (Wim a b); [dt (lpc_contra a b) | dh].
    + mp (Wn X); [dt (lcontra _ _ H2) | dh].
  - exact (lneg_vac y a (IHa H)).
  - pose proof (lal z _ _ (IHa ltac:(assumption))) as H1.
    exact (lsyl _ _ _ H1 (LB6b z y a)).
Qed.

(** ** Leibniz substitution: x = y -> (a <-> a[x:=y]) when neither x nor y is bound in a *)
Lemma eq_rv x y u : lprov (Wim (Weq x y) (Weq u (rv x y u))) /\ lprov (Wim (Weq x y) (Weq (rv x y u) u)).
Proof.
  unfold rv. destruct (Nat.eqb_spec u x) as [->|_].
  - split; [apply lpc_id | apply leq_sym].
  - split; exact (LDET _ _ (lpc_K _ _) (leq_refl u)).
Qed.

Lemma leib x y a : bnd x a = false -> bnd y a = false ->
  lprov (Wim (Weq x y) (Wim a (ren x y a))) /\ lprov (Wim (Weq x y) (Wim (ren x y a) a)).
Proof.
  set (h := Weq x y).
  induction a as [u v|u v|a IHa b IHb|a IHa|z a IHa]; simpl; intros Hx Hy.
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
  - apply orb_false_iff in Hx as [Hxa Hxb]. apply orb_false_iff in Hy as [Hya Hyb].
    destruct (IHa Hxa Hya) as [A1 A2]. destruct (IHb Hxb Hyb) as [B1' B2'].
    split; apply der_lprov, ded, ded, ded.
    + mp b; [mp h; [dt B1' | dh] | mp a; [dh | mp (ren x y a); [mp h; [dt A2 | dh] | dh]]].
    + mp (ren x y b); [mp h; [dt B2' | dh] | mp (ren x y a); [dh | mp a; [mp h; [dt A1 | dh] | dh]]].
  - destruct (IHa Hx Hy) as [A1 A2].
    split; apply der_lprov, ded.
    + mp (Wim (ren x y a) a); [dt (lpc_contra (ren x y a) a) | mp h; [dt A2 | dh]].
    + mp (Wim a (ren x y a)); [dt (lpc_contra a (ren x y a)) | mp h; [dt A1 | dh]].
  - apply orb_false_iff in Hx as [Hzx Hx]. apply orb_false_iff in Hy as [Hzy Hy].
    destruct (IHa Hx Hy) as [A1 A2].
    assert (Hz : rv x y z = z) by (unfold rv; now rewrite Hzx).
    rewrite Hz. apply Nat.eqb_neq in Hzx, Hzy.
    assert (V : lprov (Wim h (Wal z h))).
    { apply lvac. simpl. apply orb_false_iff. split; apply Nat.eqb_neq; congruence. }
    split.
    + exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 z h _) (LGEN z _ A1)) (LB4 z a _))).
    + exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 z h _) (LGEN z _ A2)) (LB4 z _ a))).
Qed.

(** ** Specialization and alphabetic variance *)
Lemma lall_ex x p q : lprov (Wim (Wal x (Wim p q)) (Wim (Wex x p) (Wex x q))).
Proof.
  unfold Wex.
  pose proof (LDET _ _ (LB4 x (Wim p q) (Wim (Wn q) (Wn p))) (LGEN x _ (lpc_contra p q))) as H1.
  apply der_lprov, ded.
  mp (Wim (Wal x (Wn q)) (Wal x (Wn p))); [dt (lpc_contra (Wal x (Wn q)) (Wal x (Wn p)))|].
  mp (Wal x (Wim (Wn q) (Wn p))); [dt (LB4 x (Wn q) (Wn p))|].
  mp (Wal x (Wim p q)); [dt H1 | dh].
Qed.

Lemma lspec x y a : x <> y -> bnd x a = false -> bnd y a = false ->
  lprov (Wim (Wal x a) (ren x y a)).
Proof.
  intros Hxy Hx Hy. set (a' := ren x y a).
  destruct (leib x y a Hx Hy) as [L _].
  pose proof (LDET _ _ (lpc_C _ _ _) L) as L'.                (* a -> (x = y -> a') *)
  pose proof (lal x _ _ L') as H1.                            (* A. x a -> A. x (x = y -> a') *)
  pose proof (lsyl _ _ _ H1 (lall_ex x (Weq x y) a')) as H2.  (* A. x a -> (E. x x = y -> E. x a') *)
  pose proof (LDET _ _ (LDET _ _ (lpc_C _ _ _) H2) (LB7 x y)) as H3.  (* A. x a -> E. x a' *)
  pose proof (lex x _ _ (lvac x a' (occ_ren_self x y a Hxy))) as H4.  (* E. x a' -> E. x A. x a' *)
  exact (lsyl _ _ _ H3 (lsyl _ _ _ H4 (LB6c x a'))).
Qed.

Lemma lalpha x y a : x <> y -> bnd x a = false -> occ y a = false ->
  lprov (Wim (Wal x a) (Wal y (ren x y a))).
Proof.
  intros Hxy Hx Hy.
  pose proof (lspec x y a Hxy Hx (occ_bnd y a Hy)) as H1.
  refine (lsyl _ _ _ (lvac y (Wal x a) _) (lal y _ _ H1)).
  simpl. rewrite Hy, orb_false_r. apply Nat.eqb_neq. exact Hxy.
Qed.

Lemma lalpha_back x y a : x <> y -> bnd x a = false -> occ y a = false ->
  lprov (Wim (Wal y (ren x y a)) (Wal x a)).
Proof.
  intros Hxy Hx Hy.
  pose proof (lalpha y x (ren x y a) ltac:(congruence)) as H.
  rewrite ren_ren in H by exact Hy. apply H.
  - rewrite bnd_ren by exact Hx. exact (occ_bnd y a Hy).
  - exact (occ_ren_self x y a Hxy).
Qed.

Lemma lperm_neg a b : lprov (Wim (Wim b (Wn a)) (Wim a (Wn b))).
Proof.
  apply der_lprov, ded, ded.
  mp (Wn (Wn a)); [mp (Wim b (Wn a)); [dt (lpc_contra b (Wn a)) | dh] | mp a; [dt (lpc_nn_intro a) | dh]].
Qed.

(** ** Equivalence up to alpha-renaming, = symmetry and /\ commutativity *)
Definition leqv a b : Prop := lprov (Wim a b) /\ lprov (Wim b a).

Inductive ae : wff -> wff -> Prop :=
  | ae_refl a : ae a a
  | ae_sym a b : ae a b -> ae b a
  | ae_trans a b c : ae a b -> ae b c -> ae a c
  | ae_im a a' b b' : ae a a' -> ae b b' -> ae (Wim a b) (Wim a' b')
  | ae_n a a' : ae a a' -> ae (Wn a) (Wn a')
  | ae_al x a a' : ae a a' -> ae (Wal x a) (Wal x a')
  | ae_alpha x y a b : x <> y -> bnd x a = false -> occ y a = false -> ren x y a = b ->
      ae (Wal x a) (Wal y b)
  | ae_eqsym x y : ae (Weq x y) (Weq y x)
  | ae_andcomm a b : ae (Wa a b) (Wa b a).

Lemma ae_sound a b : ae a b -> leqv a b.
Proof.
  induction 1 as [a|a b _ [H1 H2]|a b c _ [H1 H2] _ [H3 H4]|a a' b b' _ [H1 H2] _ [H3 H4]
                 |a a' _ [H1 H2]|x a a' _ [H1 H2]|x y a b Hxy Hx Hy <-|x y|a b].
  - split; apply lpc_id.
  - split; assumption.
  - split; eapply lsyl; eassumption.
  - split; apply der_lprov, ded, ded.
    + mp b; [dt H3 | mp a; [dh | mp a'; [dt H2 | dh]]].
    + mp b'; [dt H4 | mp a'; [dh | mp a; [dt H1 | dh]]].
  - split; apply lcontra; assumption.
  - split; apply lal; assumption.
  - split; [apply lalpha | apply lalpha_back]; assumption.
  - split; apply leq_sym.
  - unfold Wa. split; apply lcontra, lperm_neg.
Qed.
