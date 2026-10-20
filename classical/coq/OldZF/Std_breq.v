(** * Std_breq: equality reasoning from the equality axioms alone ([incl EqAx G]), introduction
    rules for universal closures ([forall_times], [genall]), and the separation-from-replacement
    and closure-introduction helpers used by the bridges. *)
From Coq Require Import Arith Lia List Bool.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_iface Std_iface2.
From OldZF Require Import Std_setnd Std_setbase.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Lemma EqAx_ZF0base G : incl ZF0base G -> incl EqAx G.
Proof. intros H x Hx. apply H. cbn in *. tauto. Qed.

(** ** Equality from [EqAx] *)
Section EqE.
Context {G : list form} (HE : incl EqAx G).

Lemma eqE_refl x : G ⊢C x ≡' x.
Proof. assert (H : G ⊢C ax_refl') by (apply Ctx, HE; cbn; tauto). finst H x. exact H. Qed.

Lemma eqE_sym x y : G ⊢C x ≡' y -> G ⊢C y ≡' x.
Proof. intros H1. assert (H : G ⊢C ax_sym') by (apply Ctx, HE; cbn; tauto). finst H x y. now fmp H H1. Qed.

Lemma eqE_trans x y z : G ⊢C x ≡' y -> G ⊢C y ≡' z -> G ⊢C x ≡' z.
Proof.
  intros H1 H2. assert (H : G ⊢C ax_trans') by (apply Ctx, HE; cbn; tauto). finst H x y z.
  fmp H H1. now fmp H H2.
Qed.

Lemma elemE_cong x y x' y' : G ⊢C x ≡' x' -> G ⊢C y ≡' y' -> G ⊢C x ∈' y -> G ⊢C x' ∈' y'.
Proof.
  intros H1 H2 H3. assert (H : G ⊢C ax_eq_elem') by (apply Ctx, HE; cbn; tauto).
  finst H x y x'. finst H y'. fmp H H1. fmp H H2. now fmp H H3.
Qed.
End EqE.

Lemma leibE_gen (phi : form) : forall G (sg tau : nat -> term), incl EqAx G ->
  (forall n, G ⊢C sg n ≡' tau n) -> G ⊢C phi[sg] -> G ⊢C phi[tau].
Proof.
  induction phi as [| P v | op a IHa b IHb | q a IHa] using form_ind_falsity;
    intros G sg tau HG Hst H.
  - exact H.
  - destruct P; cbn in v |- *; rewrite (vec2 v) in H |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *.
    + eapply elemE_cong; eauto.
    + eapply eqE_trans; [exact HG| |]. apply eqE_sym; [exact HG|]. apply Hst.
      eapply eqE_trans; eauto.
  - assert (Hts : forall n, G ⊢C tau n ≡' sg n) by (intros n; apply eqE_sym; auto).
    destruct op; cbn in H |- *.
    + apply CI; [eapply IHa|eapply IHb]; eauto; [eapply CE1|eapply CE2]; exact H.
    + apply (DE H).
      * apply DI1. eapply IHa; [| |apply Ctx; now left]. now apply incl_cons_r.
        intros n. apply weak_cons, Hst.
      * apply DI2. eapply IHb; [| |apply Ctx; now left]. now apply incl_cons_r.
        intros n. apply weak_cons, Hst.
    + apply II. eapply IHb; [now apply incl_cons_r| intros n; apply weak_cons, Hst|].
      eapply IE; [apply weak_cons, H|]. eapply IHa; [now apply incl_cons_r| intros n; apply weak_cons, Hts|].
      apply Ctx; now left.
  - destruct q; cbn in H |- *.
    + apply AllI_named. intros t. apply (AllE t) in H. rewrite up_inst_form in H |- *.
      eapply IHa; [exact HG| |exact H]. intros [|n]; cbn; [apply eqE_refl; exact HG|]. apply Hst.
    + apply (ExE_named H). intros t. rewrite up_inst_form. apply (ExI t). rewrite up_inst_form.
      eapply IHa; [now apply incl_cons_r| |apply Ctx; now left].
      intros [|n]; cbn; [apply eqE_refl; now apply incl_cons_r|]. apply weak_cons, Hst.
Qed.

Lemma leibE G (phi : form) x y : incl EqAx G -> G ⊢C x ≡' y -> G ⊢C phi[x..] -> G ⊢C phi[y..].
Proof.
  intros HG Hxy H. eapply leibE_gen; [exact HG| |exact H]. intros [|n]; cbn; [exact Hxy|]. now apply eqE_refl.
Qed.

Ltac getHE := match goal with H : incl EqAx _ |- _ => constr:(H) end.

Ltac feqE_at n :=
  let HE := getHE in
  match goal with
  | |- _ ⊢C ?a ≡' ?a => apply (eqE_refl HE)
  | H : _ ⊢C ?a ≡' ?b |- _ ⊢C ?a ≡' ?b => exact H
  | H : _ ⊢C ?b ≡' ?a |- _ ⊢C ?a ≡' ?b => exact (eqE_sym HE _ _ H)
  | _ => match n with
        | S ?m =>
          match goal with
          | H : _ ⊢C ?a ≡' ?c |- _ ⊢C ?a ≡' ?b => apply (eqE_trans HE a c b H); feqE_at m
          | H : _ ⊢C ?c ≡' ?a |- _ ⊢C ?a ≡' ?b => apply (eqE_trans HE a c b (eqE_sym HE _ _ H)); feqE_at m
          end
        end
  end.
Ltac feqE := feqE_at 3.

Ltac fmemE :=
  let HE := getHE in
  match goal with
  | H : _ ⊢C ?a ∈' ?b |- _ ⊢C ?a ∈' ?b => exact H
  | H : _ ⊢C ?c ∈' ?d |- _ ⊢C ?a ∈' ?b => apply (elemE_cong HE c d a b); [feqE|feqE|exact H]
  end.

Ltac frewE_in Heq phi H :=
  let HE := getHE in
  let H' := fresh in
  first [ pose proof (leibE _ phi _ _ HE Heq) as H'; simp_in H'; specialize (H' H)
        | pose proof (leibE _ phi _ _ HE (eqE_sym HE _ _ Heq)) as H'; simp_in H'; specialize (H' H) ];
  clear H; rename H' into H.
Ltac frewE Heq phi :=
  let HE := getHE in
  let H' := fresh in
  first [ pose proof (leibE _ phi _ _ HE Heq) as H'; simp_in H'; apply H'; clear H'
        | pose proof (leibE _ phi _ _ HE (eqE_sym HE _ _ Heq)) as H'; simp_in H'; apply H'; clear H' ].

(** ** Introducing universal closures *)
Lemma ft_intro G k : forall (psi : form), (forall sg, G ⊢C psi[sg]) -> G ⊢C forall_times k psi.
Proof.
  induction k as [|k IH]; intros psi H.
  - cbn. specialize (H var). now rewrite subst_var in H.
  - unfold forall_times. cbn [iter]. rewrite iter_switch. apply (IH (∀ psi)). intros sg. cbn.
    apply AllI_named. intros t. rewrite up_inst_form. apply H.
Qed.

Lemma genall_intro G a n : forall (rho : nat -> term), (forall sg, G ⊢C dB sg a) -> G ⊢C dB rho (genall n a).
Proof.
  induction n as [|n IH]; intros rho H; [apply H|].
  cbn [genall dB]. apply AllI_named. intros t. rewrite dB_inst. apply IH, H.
Qed.

Lemma Lib_intro G n a : (forall sg, G ⊢C dB sg a) -> G ⊢C Lib n a.
Proof. intros H. apply genall_intro, H. Qed.
