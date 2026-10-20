(** * Std_F: every theorem of O'Rear's [prov] translates to a theorem (classical natural deduction)
    of any library theory [T] containing the equality axioms and proving (the translations of)
    O'Rear's ZF axioms; [Fvalid T a]: one fixed list of [T]-axioms proves every instance [dB rho a]. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic Std_dB.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

Ltac ctx := apply Ctx; simpl; tauto.

(** ** Basic facts *)
Lemma subst_shift_term (t s : term) : t`[↑]`[s..] = t.
Proof. apply subst_term_shift. Qed.

Lemma shift_env_inst x rho t v :
  (shift_env x rho >> subst_term (t..)) v = if Nat.eqb v x then t else rho v.
Proof. unfold shift_env, funcomp. destruct (Nat.eqb v x); cbn; [reflexivity | apply subst_term_shift]. Qed.

Lemma dB_inst x rho t a :
  (dB (shift_env x rho) a)[t..] = dB (fun v => if Nat.eqb v x then t else rho v) a.
Proof. rewrite dB_subst. apply dB_ext. apply shift_env_inst. Qed.

(** ** Equality axioms *)
Definition EqAx : list form := [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'].


Section Eq.
Variable A : list form.
Hypothesis HA : incl EqAx A.

Lemma nd_refl t : A ⊢C t ≡' t.
Proof.
  change (A ⊢C ($0 ≡' $0)[t..]). apply AllE. apply Ctx, HA. simpl; tauto.
Qed.

Lemma nd_sym s t : A ⊢C s ≡' t → t ≡' s.
Proof.
  assert (H : A ⊢C ax_sym') by (apply Ctx, HA; simpl; tauto).
  apply (AllE s) in H. apply (AllE t) in H. cbn in H. repeat (rewrite ?up_term, ?subst_term_shift in H); exact H.
Qed.

Lemma nd_trans r s t : A ⊢C r ≡' s → s ≡' t → r ≡' t.
Proof.
  assert (H : A ⊢C ax_trans') by (apply Ctx, HA; simpl; tauto).
  apply (AllE r) in H. apply (AllE s) in H. apply (AllE t) in H. cbn in H.
  repeat (rewrite ?up_term, ?subst_term_shift in H); exact H.
Qed.

Lemma nd_elem x y x' y' : A ⊢C x ≡' x' → y ≡' y' → x ∈' y → x' ∈' y'.
Proof.
  assert (H : A ⊢C ax_eq_elem') by (apply Ctx, HA; simpl; tauto).
  apply (AllE x) in H. apply (AllE y) in H. apply (AllE x') in H. apply (AllE y') in H. cbn in H.
  repeat (rewrite ?up_term, ?subst_term_shift in H); exact H.
Qed.
End Eq.

(** helper: modus ponens with an implication proved in the empty context *)
Lemma mp_weak A phi psi : [] ⊢C phi → psi -> A ⊢C phi -> A ⊢C psi.
Proof. intros H1 H2. eapply IE; [eapply Weak; [exact H1 | intros ? []] | exact H2]. Qed.

Lemma shift_env_neq x rho v : v <> x -> shift_env x rho v = (rho v)`[↑].
Proof. intro H. unfold shift_env. apply Nat.eqb_neq in H. now rewrite H. Qed.

Lemma shift_env_eq x rho : shift_env x rho x = var 0.
Proof. unfold shift_env. now rewrite Nat.eqb_refl. Qed.

Lemma prv_dB_ext A r r' a : (forall v, r v = r' v) -> A ⊢C dB r a -> A ⊢C dB r' a.
Proof. intros E H. now rewrite <- (dB_ext a E). Qed.

Lemma prv_dB_subst2 A r sg tau a :
  A ⊢C (dB r a)[sg][tau] -> A ⊢C dB ((r >> subst_term sg) >> subst_term tau) a.
Proof. intro H. now rewrite !dB_subst in H. Qed.

Ltac tsimp := repeat (rewrite ?up_term, ?subst_term_shift).

Ltac env_solve :=
  let v := fresh "v" in
  intros v; unfold shift_env, funcomp;
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
  try subst; cbn; try reflexivity; try (exfalso; congruence);
  rewrite ?subst_term_comp;
  first [ reflexivity
        | apply subst_term_id; intros [|?]; reflexivity
        | symmetry; apply subst_term_id; intros [|?]; reflexivity
        | apply subst_term_ext; intros [|?]; reflexivity ].

(** ** Logical axioms of prov *)
Section LogicAx.
Variable rho : nat -> term.

Lemma nd_B1 a b c : [] ⊢C dB rho (Wim (Wim a b) (Wim (Wim b c) (Wim a c))).
Proof.
  cbn. apply II, II, II. eapply IE; [ctx|]. eapply IE; [ctx | ctx].
Qed.

Lemma nd_B2 a : [] ⊢C dB rho (Wim (Wim (Wn a) a) a).
Proof.
  cbn. apply II. apply DN. apply II.
  eapply IE; [ctx|]. eapply IE; [ctx|]. ctx.
Qed.

Lemma nd_B3 a b : [] ⊢C dB rho (Wim a (Wim (Wn a) b)).
Proof.
  cbn. apply II, II. apply Exp. eapply IE; ctx.
Qed.

Lemma nd_B4 x a b : [] ⊢C dB rho (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b))).
Proof.
  cbn. apply II, II. apply AllI_named. intro t. rewrite dB_inst.
  assert (H1 : [quant All (dB (shift_env x rho) a); quant All (bin Impl (dB (shift_env x rho) a) (dB (shift_env x rho) b))]
            ⊢C (bin Impl (dB (shift_env x rho) a) (dB (shift_env x rho) b))[t..]) by (apply AllE; ctx).
  assert (H2 : [quant All (dB (shift_env x rho) a); quant All (bin Impl (dB (shift_env x rho) a) (dB (shift_env x rho) b))]
            ⊢C (dB (shift_env x rho) a)[t..]) by (apply AllE; ctx).
  cbn in H1. rewrite (dB_inst x rho t a), (dB_inst x rho t b) in H1. rewrite dB_inst in H2.
  eapply IE; eassumption.
Qed.

Lemma nd_B6a x y z : x <> z -> y <> z ->
  [] ⊢C dB rho (Wa (Wim (Weq x y) (Wal z (Weq x y))) (Wim (Wel x y) (Wal z (Wel x y)))).
Proof.
  intros Hx Hy. cbn [dB Wa]. rewrite !shift_env_neq by congruence.
  apply II. eapply IE; [eapply IE; [ctx|] |].
  - apply II, AllI. apply Ctx. cbn. now left.
  - apply II, AllI. apply Ctx. cbn. now left.
Qed.

Lemma nd_B6b x y a : [] ⊢C dB rho (Wim (Wal x (Wal y a)) (Wal y (Wal x a))).
Proof.
  cbn [dB]. apply II. apply AllI_named. intro t. cbn. apply AllI_named. intro s.
  rewrite !dB_subst.
  destruct (Nat.eqb_spec x y) as [<-|Hxy].
  - assert (H : [quant All (quant All (dB (shift_env x (shift_env x rho)) a))]
                ⊢C (quant All (dB (shift_env x (shift_env x rho)) a))[t..]) by (apply AllE; ctx).
    cbn in H. apply (AllE s) in H. rewrite !dB_subst in H.
    refine (prv_dB_ext _ H). env_solve.
  - assert (H : [quant All (quant All (dB (shift_env y (shift_env x rho)) a))]
                ⊢C (quant All (dB (shift_env y (shift_env x rho)) a))[s..]) by (apply AllE; ctx).
    cbn in H. apply (AllE t) in H. rewrite !dB_subst in H.
    refine (prv_dB_ext _ H). env_solve.
Qed.

Lemma nd_B6c x a : [] ⊢C dB rho (Wim (Wex x (Wal x a)) a).
Proof.
  cbn [dB Wex]. apply II. apply DN. apply II.
  eapply IE; [apply Ctx; simpl; right; left; reflexivity|].
  apply AllI_named. intro t. cbn. apply II.
  eapply IE; [apply Ctx; simpl; right; left; reflexivity|].
  assert (H : [quant All (dB (shift_env x (shift_env x rho)) a)[up (t..)];
               bin Impl (dB rho a) falsity;
               bin Impl (quant All (bin Impl (quant All (dB (shift_env x (shift_env x rho)) a)) falsity)) falsity]
              ⊢C (dB (shift_env x (shift_env x rho)) a)[up (t..)][(rho x)..]) by (apply AllE; ctx).
  apply prv_dB_subst2 in H. refine (prv_dB_ext _ H). env_solve.
Qed.

Lemma nd_B7 x y : EqAx ⊢C dB rho (Wex x (Weq x y)).
Proof.
  cbn [dB Wex]. apply II.
  assert (H : ((quant All (bin Impl (dB (shift_env x rho) (Weq x y)) falsity)) :: EqAx)
              ⊢C (bin Impl (dB (shift_env x rho) (Weq x y)) falsity)[(rho y)..])
    by (apply AllE; ctx).
  cbn in H. eapply IE; [exact H|].
  replace ((shift_env x rho x)`[(rho y)..]) with (rho y) by (rewrite shift_env_eq; reflexivity).
  replace ((shift_env x rho y)`[(rho y)..]) with (rho y)
    by (unfold shift_env; destruct (Nat.eqb_spec y x); [subst; reflexivity | symmetry; apply subst_term_shift]).
  apply nd_refl. intros ? ?; simpl; tauto.
Qed.

Lemma nd_B8a x y z : EqAx ⊢C dB rho (Wim (Weq x y) (Wim (Weq x z) (Weq y z))).
Proof.
  cbn [dB]. apply II, II. set (G := _ :: _ :: EqAx).
  assert (HG : incl EqAx G) by (intros ? ?; simpl; tauto).
  eapply IE; [eapply IE; [apply (nd_trans HG) | ] | ctx].
  eapply IE; [apply (nd_sym HG) | ctx].
Qed.

Lemma nd_B8b x y z : EqAx ⊢C dB rho (Wim (Weq x y) (Wim (Wel x z) (Wel y z))).
Proof.
  cbn [dB]. apply II, II. set (G := _ :: _ :: EqAx).
  assert (HG : incl EqAx G) by (intros ? ?; simpl; tauto).
  eapply IE; [eapply IE; [eapply IE; [apply (nd_elem HG) | ctx] | apply (nd_refl HG)] | ctx].
Qed.

Lemma nd_B8c x y z : EqAx ⊢C dB rho (Wim (Weq x y) (Wim (Wel z x) (Wel z y))).
Proof.
  cbn [dB]. apply II, II. set (G := _ :: _ :: EqAx).
  assert (HG : incl EqAx G) by (intros ? ?; simpl; tauto).
  eapply IE; [eapply IE; [eapply IE; [apply (nd_elem HG) | apply (nd_refl HG)] | ctx] | ctx].
Qed.

End LogicAx.

(** ** The translation theorem, given the ZF axioms, for any theory containing the equality axioms *)
Section Main.
Variable T : form -> Prop.
Hypothesis T_EqAx : forall psi, In psi EqAx -> T psi.

Definition good_list (A : list form) : Prop := forall psi, In psi A -> T psi.

Definition Fvalid (a : wff) : Prop := exists A, good_list A /\ forall rho, A ⊢C dB rho a.

Lemma Fvalid_EqAx (a : wff) : (forall rho, EqAx ⊢C dB rho a) -> Fvalid a.
Proof. intro H. exists EqAx. split; [exact T_EqAx | exact H]. Qed.

Lemma Fvalid_nil (a : wff) : (forall rho, [] ⊢C dB rho a) -> Fvalid a.
Proof. intro H. apply Fvalid_EqAx. intro rho. eapply Weak; [apply H | intros ? []]. Qed.

Hypothesis F_EXT : Fvalid EXT.
Hypothesis F_POW : Fvalid POW.
Hypothesis F_UNI : Fvalid UNI.
Hypothesis F_INF : Fvalid INF.
Hypothesis F_REP : forall ph, Fvalid (REP ph).

Theorem prov_Fvalid a : prov a -> Fvalid a.
Proof.
  induction 1 as [a b _ [A1 [G1 H1]] _ [A2 [G2 H2]] | x a _ [A [G H]]
    | a b c | a | a b | x a b | x y z Hxz Hyz | x y a | x a | x y | x y z | x y z | x y z
    | | a | | | ].
  - exists (A1 ++ A2). split.
    + intros psi [Hp|Hp]%in_app_iff; auto.
    + intro rho. eapply IE.
      * eapply Weak; [apply (H1 rho) | apply incl_appl, incl_refl].
      * eapply Weak; [apply (H2 rho) | apply incl_appr, incl_refl].
  - exists A. split; [exact G|]. intro rho. cbn [dB]. apply AllI_named. intro t.
    rewrite dB_inst. apply H.
  - apply Fvalid_nil. intro; apply nd_B1.
  - apply Fvalid_nil. intro; apply nd_B2.
  - apply Fvalid_nil. intro; apply nd_B3.
  - apply Fvalid_nil. intro; apply nd_B4.
  - apply Fvalid_nil. intro; now apply nd_B6a.
  - apply Fvalid_nil. intro; apply nd_B6b.
  - apply Fvalid_nil. intro; apply nd_B6c.
  - apply Fvalid_EqAx. intro; apply nd_B7.
  - apply Fvalid_EqAx. intro; apply nd_B8a.
  - apply Fvalid_EqAx. intro; apply nd_B8b.
  - apply Fvalid_EqAx. intro; apply nd_B8c.
  - exact F_EXT.
  - apply F_REP.
  - exact F_POW.
  - exact F_UNI.
  - exact F_INF.
Qed.
End Main.
