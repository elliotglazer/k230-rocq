(** * Relativization of first-order natural deduction to a definable class

    For a formula [M] with one free variable [$0] (a class), [rel phi] bounds every quantifier
    of [phi] by [M].  The main lemma [rel_prv]: if [A ⊢ phi] then [rel phi] is derivable from
    any context [Gamma] that proves [M] of every value of the variable assignment [sigma] and the
    relativization of every hypothesis in [A] (all under [sigma]), provided [M] is closed under
    the function symbols (relative to a fixed list [B] of closed sentences contained in [Gamma]). *)

From OldUndecidability Require Import FOL.Syntax.Facts FOL.Deduction.FullNDFacts.
From OldUndecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationFacts ListAutomationHints ListAutomationInstances.
Require Import Lia List.

Section Rel.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Variable M : form falsity_on.
  Hypothesis HM : bounded 1 M.

  Fixpoint rel {ff} (phi : form ff) : form falsity_on :=
    match phi with
    | falsity => falsity
    | atom P v => @atom _ _ _ falsity_on P v
    | bin b phi psi => bin b (rel phi) (rel psi)
    | quant All phi => ∀ (M → rel phi)
    | quant Ex phi => ∃ (M ∧ rel phi)
    end.

  Lemma M_up sigma : M[up sigma] = M.
  Proof.
    erewrite (bounded_subst HM). apply subst_var.
    intros [|k] Hk; [reflexivity | lia].
  Qed.

  Lemma M_subst t sigma : M[t..][sigma] = M[t`[sigma]..].
  Proof.
    rewrite subst_comp. apply (bounded_subst HM).
    intros [|k] Hk; [reflexivity | lia].
  Qed.

  Lemma M_var0 : M[$0..] = M.
  Proof.
    erewrite (bounded_subst HM). apply subst_var.
    intros [|k] Hk; [reflexivity | lia].
  Qed.

  Lemma rel_subst {ff} (phi : form ff) sigma : (rel phi)[sigma] = rel (phi[sigma]).
  Proof.
    induction phi in sigma |- *; cbn; try reflexivity.
    - now rewrite IHphi1, IHphi2.
    - destruct q; cbn; now rewrite M_up, IHphi.
  Qed.

  Lemma subst_inst (phi : form falsity_on) t sigma :
    phi[up sigma][t`[sigma]..] = phi[t..][sigma].
  Proof.
    rewrite !subst_comp. apply subst_ext. intros [|n]; cbn; trivial.
    unfold funcomp. apply subst_term_shift.
  Qed.

  Lemma closed_shift (L Gamma : list (form falsity_on)) :
    (forall b sigma, b el L -> b[sigma] = b) -> L <<= Gamma -> L <<= map (subst_form ↑) Gamma.
  Proof.
    intros HL H b Hb. rewrite <- (HL b ↑ Hb). apply in_map, H, Hb.
  Qed.

  Variable p0 : peirce.
  Variable B : list (form falsity_on).
  Hypothesis HB : forall b sigma, b el B -> b[sigma] = b.
  Hypothesis Hclos : forall Gamma f v, let p := p0 in B <<= Gamma ->
      (forall t, Vector.In t v -> @prv _ _ falsity_on p Gamma (M[t..])) ->
      @prv _ _ falsity_on p Gamma (M[(func f v)..]).

  Lemma rel_term Gamma sigma t : let p := p0 in
    B <<= Gamma -> (forall k, @prv _ _ falsity_on p Gamma (M[(sigma k)..])) ->
    @prv _ _ falsity_on p Gamma (M[(t`[sigma])..]).
  Proof.
    intros p HG Hs. induction t as [k|f v IH]; cbn.
    - apply Hs.
    - apply Hclos; trivial. intros t Ht.
      apply vector_in_map in Ht as [s [Hs' <-]]. now apply IH.
  Qed.

  Lemma M_shift p Gamma sigma :
    (forall k, @prv _ _ falsity_on p Gamma (M[(sigma k)..])) ->
    forall k, @prv _ _ falsity_on p (map (subst_form ↑) Gamma) (M[(up sigma (S k))..]).
  Proof.
    intros Hs k. cbn. unfold funcomp. rewrite <- M_subst. apply subst_Weak, Hs.
  Qed.

  Lemma A_shift p Gamma sigma (a : form falsity_on) :
    @prv _ _ falsity_on p Gamma ((rel a)[sigma]) ->
    @prv _ _ falsity_on p (map (subst_form ↑) Gamma) ((rel a[↑])[up sigma]).
  Proof.
    intros H. rewrite <- rel_subst, up_form. now apply subst_Weak.
  Qed.

  Ltac spec_refl := repeat match goal with H : ?x = ?x -> _ |- _ => specialize (H eq_refl) end.

  Theorem rel_prv A (phi : form falsity_on) : let p := p0 in
    @prv _ _ falsity_on p A phi -> forall Gamma sigma, B <<= Gamma ->
    (forall k, @prv _ _ falsity_on p Gamma (M[(sigma k)..])) ->
    (forall a, a el A -> @prv _ _ falsity_on p Gamma ((rel a)[sigma])) ->
    @prv _ _ falsity_on p Gamma ((rel phi)[sigma]).
  Proof.
    intros p H. assert (Hp : p = p0) by reflexivity. clearbody p. revert Hp. revert p A phi H.
    apply (prv_ind_full (P := fun p A phi => p = p0 -> forall Gamma sigma, B <<= Gamma ->
      (forall k, @prv _ _ falsity_on p Gamma (M[(sigma k)..])) ->
      (forall a, a el A -> @prv _ _ falsity_on p Gamma ((rel a)[sigma])) ->
      @prv _ _ falsity_on p Gamma ((rel phi)[sigma]))); cbn.
    - (* II *) intros p A phi psi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      apply II. apply IH.
      + now apply incl_tl.
      + intros k. apply (Weak (Hs k)). auto.
      + intros a [<-|Ha]; [apply Ctx; auto | apply (Weak (HA a Ha)); auto].
    - (* IE *) intros p A phi psi _ IH1 _ IH2 Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      eapply IE; [apply IH1 | apply IH2]; trivial.
    - (* AllI *) intros p A phi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      rewrite M_up. apply AllI, II. apply IH.
      + now apply incl_tl, closed_shift.
      + intros [|k].
        * cbn. rewrite M_var0. apply Ctx. auto.
        * apply (Weak (M_shift Hs k)). auto.
      + intros a' Ha'. apply in_map_iff in Ha' as [a [<- Ha]].
        apply (Weak (A_shift (HA a Ha))). auto.
    - (* AllE *) intros p A t phi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      rewrite <- rel_subst. specialize (IH Gamma sigma HG Hs HA). cbn in IH.
      rewrite M_up in IH. apply (AllE (t`[sigma])) in IH. cbn in IH.
      rewrite <- subst_inst. eapply IE; [apply IH | now apply rel_term].
    - (* ExI *) intros p A t phi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      rewrite M_up. apply (ExI (t`[sigma])). cbn. apply CI.
      + now apply rel_term.
      + rewrite subst_inst, rel_subst. now apply IH.
    - (* ExE *) intros p A phi psi _ IH1 _ IH2 Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      specialize (IH1 Gamma sigma HG Hs HA). cbn in IH1. rewrite M_up in IH1.
      eapply ExE; [apply IH1 |].
      rewrite <- up_form, (rel_subst psi). apply IH2.
      + now apply incl_tl, closed_shift.
      + intros [|k].
        * cbn. rewrite M_var0. eapply CE1, Ctx. auto.
        * apply (Weak (M_shift Hs k)). auto.
      + intros a' [<-|Ha'].
        * eapply CE2, Ctx. auto.
        * apply in_map_iff in Ha' as [a [<- Ha]].
          apply (Weak (A_shift (HA a Ha))). auto.
    - (* Exp *) intros p A phi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      apply Exp. now apply (IH Gamma sigma).
    - (* Ctx *) intros p A phi Hphi Hp Gamma sigma HG Hs HA. subst p. spec_refl. now apply HA.
    - (* CI *) intros p A phi psi _ IH1 _ IH2 Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      apply CI; [apply IH1 | apply IH2]; trivial.
    - (* CE1 *) intros p A phi psi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      eapply CE1. now apply IH.
    - (* CE2 *) intros p A phi psi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      eapply CE2. now apply IH.
    - (* DI1 *) intros p A phi psi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      apply DI1. now apply IH.
    - (* DI2 *) intros p A phi psi _ IH Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      apply DI2. now apply IH.
    - (* DE *) intros p A phi psi theta _ IH1 _ IH2 _ IH3 Hp Gamma sigma HG Hs HA. subst p. spec_refl.
      eapply DE; [now apply IH1 | apply IH2 | apply IH3].
      1,4: now apply incl_tl.
      1,3: intros k; apply (Weak (Hs k)); auto.
      all: intros a [<-|Ha]; [apply Ctx; auto | apply (Weak (HA a Ha)); auto].
    - (* Pc *) intros A phi psi Hp Gamma sigma HG Hs HA. subst p0. apply Pc.
  Qed.

  (* ** Auxiliary facts used to relativize concrete axioms *)

  Lemma rel_bounded {ff} n (phi : form ff) : bounded n phi -> bounded n (rel phi).
  Proof.
    induction 1; cbn.
    - now constructor.
    - now constructor.
    - destruct quantop; constructor; constructor; trivial; eapply bounded_up; try apply HM; lia.
    - constructor.
  Qed.

  Lemma rel_closed (phi : form falsity_on) sigma : bounded 0 phi -> (rel phi)[sigma] = rel phi.
  Proof.
    intros H. apply bounded_0_subst, rel_bounded, H.
  Qed.

  (* Relativizing a universally closed formula: it suffices to prove the relativized matrix
     under every substitution. *)
  Lemma rel_forall_times L n (theta : form falsity_on) :
    (forall b sigma, b el L -> b[sigma] = b) ->
    (forall Gamma tau, L <<= Gamma -> @prv _ _ falsity_on p0 Gamma ((rel theta)[tau])) ->
    forall Gamma sigma, L <<= Gamma -> @prv _ _ falsity_on p0 Gamma ((rel (forall_times n theta))[sigma]).
  Proof.
    intros HL Ht. induction n; intros Gamma sigma HG.
    - now apply Ht.
    - change (forall_times (S n) theta) with (∀ forall_times n theta). cbn.
      rewrite M_up. apply AllI, II. apply IHn. now apply incl_tl, closed_shift.
  Qed.

End Rel.
