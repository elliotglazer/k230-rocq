(** * Std_setnd: a natural-deduction toolkit for set theory in the library's minimal signature.

    Style: Coq is the meta logic; object-level facts are Coq hypotheses [H : Γ ⊢C φ] about one
    abstract context [Γ].  Tactics that extend the context ([fintro], [fex], [fcases], [fcontra])
    weaken every fact (and every [incl _ Γ] / [In _ Γ] hypothesis) and then generalize the new
    context to a fresh variable, so the proof state always shows a single abstract context.
    Fresh variables come from [AllI_named] / [ExE_named]. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Substitution simplification *)
Lemma shift_scons_term (t s : term) (sg : nat -> term) : t`[↑]`[s .: sg] = t`[sg].
Proof. rewrite subst_term_comp. apply subst_term_ext. now intros n. Qed.

Lemma shift_scons_form (phi : form) (s : term) (sg : nat -> term) : phi[↑][s .: sg] = phi[sg].
Proof. rewrite subst_comp. apply subst_ext. now intros n. Qed.

Lemma up_form_comm (phi : form) (sg : nat -> term) : phi[↑][up sg] = phi[sg][↑].
Proof. apply up_form. Qed.

Lemma up_inst_form (phi : form) (sg : nat -> term) (t : term) : phi[up sg][t..] = phi[t .: sg].
Proof. rewrite subst_comp. apply subst_ext. intros [|n]; cbn; [reflexivity|]. apply subst_term_shift. Qed.

Create HintDb fsub.
#[global] Hint Rewrite up_term subst_term_shift shift_scons_term subst_term_var : fsub.
#[global] Hint Rewrite shift_scons_form subst_shift up_form_comm subst_var up_inst_form : fsub.

Ltac fix_up :=
  repeat match goal with |- context [(S >> var) ?n] => change ((S >> var) n) with (var (S n)) end.
Ltac fix_up_in H :=
  repeat match type of H with context [(S >> var) ?n] => change ((S >> var) n) with (var (S n)) in H end.

Ltac simp := cbn; autorewrite with fsub; cbn; autorewrite with fsub; fix_up.
Ltac simp_in H := cbn in H; autorewrite with fsub in H; cbn in H; autorewrite with fsub in H; fix_up_in H.

(** equalities between two substitution instances of the same formula / term *)
Ltac term_eq :=
  unfold funcomp; cbn; unfold funcomp; cbn; rewrite ?subst_term_comp;
  first [ reflexivity
        | (apply subst_term_ext; intros; unfold funcomp; cbn; reflexivity)
        | (apply subst_term_id; intros; unfold funcomp; cbn; reflexivity)
        | (symmetry; apply subst_term_id; intros; unfold funcomp; cbn; reflexivity) ].
Ltac form_subst_eq := rewrite ?subst_comp; apply subst_ext; let k := fresh "k" in intros [|[|[|[|[|[|k]]]]]]; term_eq.

(** ** Context management *)
Lemma weak_cons (G : list form) (a phi : form) : G ⊢C phi -> (a :: G) ⊢C phi.
Proof. intros H. eapply Weak; [exact H|]. intros ? ?; now right. Qed.

Lemma incl_cons_r {X} (L G : list X) (a : X) : incl L G -> incl L (a :: G).
Proof. intros H x Hx; right; auto. Qed.

Lemma in_cons_r {X} (x a : X) (G : list X) : In x G -> In x (a :: G).
Proof. now right. Qed.

Ltac weaken_facts a G :=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  end.

(** push the head of the context into a fact [H] and generalize the context *)
Ltac ctx_push H :=
  match goal with
  | |- (?a :: ?G) ⊢C _ =>
      weaken_facts a G;
      assert (H : (a :: G) ⊢C a) by (apply Ctx; now left);
      let G' := fresh "Γ" in
      set (G' := a :: G) in *; clearbody G'; try clear G
  end.

(** ** Fact-level tactics *)
Ltac fintro H := apply II; ctx_push H; try simp_in H.
Ltac fall x := apply AllI_named; intros x; simp.
Ltac fex H x Hx := apply (ExE_named H); intros x; ctx_push Hx; simp_in Hx; try clear H.
Ltac finst1 H t := apply (AllE t) in H; simp_in H.
Tactic Notation "finst" hyp(H) constr(t1) := finst1 H t1.
Tactic Notation "finst" hyp(H) constr(t1) constr(t2) := finst1 H t1; finst1 H t2.
Tactic Notation "finst" hyp(H) constr(t1) constr(t2) constr(t3) := finst1 H t1; finst1 H t2; finst1 H t3.
Tactic Notation "finst" hyp(H) constr(t1) constr(t2) constr(t3) constr(t4) :=
  finst1 H t1; finst1 H t2; finst1 H t3; finst1 H t4.
Ltac fexists t := apply (ExI t); simp.
Ltac fsplit := apply CI.
Ltac fdestr H H1 H2 := pose proof (CE1 H) as H1; pose proof (CE2 H) as H2; clear H.
Ltac fleft := apply DI1.
Ltac fright := apply DI2.
Ltac fcases H H1 H2 := apply (DE H); [ctx_push H1 | ctx_push H2]; try clear H.
Ltac fapply H := eapply IE; [exact H|].
Ltac fmp H H' := let T := fresh in pose proof (IE H H') as T; clear H; rename T into H.
Ltac fabsurd := apply Exp.

Lemma DN_rule (G : list form) (phi : form) : ((¬ phi) :: G) ⊢C ⊥ -> G ⊢C phi.
Proof. intros H. apply DN. now apply II. Qed.

Ltac fcontra H := apply DN_rule; ctx_push H.

Tactic Notation "fassert" ident(H) ":" constr(phi) :=
  match goal with |- ?G ⊢C _ => assert (H : G ⊢C phi) end.
Tactic Notation "fenough" constr(phi) "as" ident(H) :=
  match goal with |- ?G ⊢C ?g => enough (H : G ⊢C phi) end.

(** forward use of a lemma whose remaining premises are context hypotheses *)
Ltac discharge H :=
  repeat match type of H with
  | incl _ _ -> _ => specialize (H ltac:(eassumption))
  | In _ _ -> _ => specialize (H ltac:(eassumption))
  end.
Tactic Notation "fhave" ident(H) ":" constr(X) := epose proof X as H; discharge H; try simp_in H.
Tactic Notation "fobtain" constr(X) "as" ident(x) ident(Hx) :=
  let T := fresh "T" in epose proof X as T; discharge T; try simp_in T; fex T x Hx.

(** ** Derived propositional rules *)
Section Rules.
Context (G : list form).

Lemma iff_l (phi psi : form) : G ⊢C phi ↔ psi -> G ⊢C phi -> G ⊢C psi.
Proof. intros H1 H2. exact (IE (CE1 H1) H2). Qed.

Lemma iff_r (phi psi : form) : G ⊢C phi ↔ psi -> G ⊢C psi -> G ⊢C phi.
Proof. intros H1 H2. exact (IE (CE2 H1) H2). Qed.

Lemma neg_elim (phi psi : form) : G ⊢C ¬ phi -> G ⊢C phi -> G ⊢C psi.
Proof. intros H1 H2. apply Exp. exact (IE H1 H2). Qed.

Lemma imp_trans (a b c : form) : G ⊢C a → b -> G ⊢C b → c -> G ⊢C a → c.
Proof. intros H1 H2. apply II. eapply IE; [apply (weak_cons _ _ _ H2)|]. eapply IE; [apply (weak_cons _ _ _ H1)|]. apply Ctx; now left. Qed.

Lemma imp_refl (a : form) : G ⊢C a → a.
Proof. apply II. apply Ctx. now left. Qed.

Lemma DE_rule (phi psi theta : form) : G ⊢C phi ∨ psi -> G ⊢C phi → theta -> G ⊢C psi → theta -> G ⊢C theta.
Proof.
  intros H H1 H2. apply (DE H).
  - eapply IE; [apply (weak_cons _ _ _ H1)|]. apply Ctx; now left.
  - eapply IE; [apply (weak_cons _ _ _ H2)|]. apply Ctx; now left.
Qed.

Lemma XM_rule (phi theta : form) : G ⊢C phi → theta -> G ⊢C (¬ phi) → theta -> G ⊢C theta.
Proof. intros H1 H2. eapply DE_rule; [apply XM|exact H1|exact H2]. Qed.

Lemma ExE_rule (chi psi : form) : G ⊢C ∃ chi -> (forall t, G ⊢C chi[t..] → psi) -> G ⊢C psi.
Proof.
  intros H1 H2. apply (ExE_named H1). intros t. eapply IE; [apply weak_cons, H2|]. apply Ctx; now left.
Qed.

End Rules.

(** ** Instantiating universally closed formulas *)
Lemma ft_inst_gen (G : list form) n : forall (psi : form) (sg : nat -> term),
  G ⊢C forall_times n psi -> G ⊢C psi[fun k => if k <? n then sg k else $(k - n)].
Proof.
  induction n as [|n IH]; intros psi sg H.
  - cbn. erewrite subst_ext; [rewrite subst_var; exact H|]. intros k; cbn. f_equal; lia.
  - unfold forall_times in H. cbn [iter] in H. rewrite iter_switch in H.
    apply (IH (∀ psi) (fun k => sg (S k))) in H. cbn in H. apply (AllE (sg 0)) in H.
    rewrite subst_comp in H. erewrite subst_ext; [exact H|].
    intros [|k]; [reflexivity|]. cbn -[Nat.ltb]. unfold funcomp.
    etransitivity; [|symmetry; apply subst_term_shift].
    change (match n with 0 => false | S m' => k <=? m' end) with (k <? n).
    destruct (Nat.ltb_spec k n), (Nat.ltb_spec (S k) (S n)); try lia; try reflexivity.
Qed.

Lemma ft_inst (G : list form) n (psi : form) (sg : nat -> term) :
  fb n psi -> G ⊢C forall_times n psi -> G ⊢C psi[sg].
Proof.
  intros Hfb H. apply (ft_inst_gen _ _ _ sg) in H. erewrite subst_ext_fb; [exact H|exact Hfb|].
  intros k Hk. cbv beta. destruct (Nat.ltb_spec k n); [reflexivity|lia].
Qed.

Lemma fb_forall_times n : forall (psi : form) N, fb N (forall_times n psi) -> fb (n + N) psi.
Proof.
  induction n as [|n IH]; intros psi N H; [exact H|].
  unfold forall_times in H. cbn [iter] in H. rewrite iter_switch in H. apply (IH (∀ psi)) in H. cbn in H.
  eapply fb_mono; [exact H|lia].
Qed.

Lemma closed_inst (G : list form) n (psi : form) (sg : nat -> term) :
  closedf (forall_times n psi) -> G ⊢C forall_times n psi -> G ⊢C psi[sg].
Proof. intros Hc H. apply (ft_inst _ n); [|exact H]. apply fb_forall_times in Hc. now rewrite Nat.add_0_r in Hc. Qed.

(** ** Free-index bounds under substitution *)
Lemma fb_subst (phi : form) : forall N M (sg : nat -> term),
  fb N phi -> (forall i, i < N -> idx (sg i) < M) -> fb M phi[sg].
Proof.
  induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N M sg Hfb H; cbn in *.
  - exact I.
  - destruct P; cbn in v, Hfb |- *; rewrite (vec2 v) in Hfb |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *;
      split; apply H; tauto.
  - destruct Hfb. split; [eapply IHa|eapply IHb]; eauto.
  - eapply IHa; [exact Hfb|]. intros [|i] Hi; cbn; [lia|]. unfold funcomp.
    destruct (sg i) as [k|[]] eqn:E; cbn. specialize (H i). rewrite E in H. cbn in H. lia.
Qed.
