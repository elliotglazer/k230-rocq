(** Canonical Separation and Replacement schemes in the quotient. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KDomain KPSeparation KTagged KDSeparation KCollection KQuot KQuotFormula KQuotSeparation KQuotReplacement KQuotAxioms KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** An unrestricted proof of every instance suffices for restricted universal
    quantifiers. The same finite context is used at every instance. *)
Lemma qtrans_ft_intro G n : forall phi t,
  (forall sg, G ⊢C qtrans t phi[sg]) -> G ⊢C qtrans t (forall_times n phi).
Proof.
  induction n as [|n IH]; intros phi t H.
  - cbn. specialize (H var). now rewrite subst_var in H.
  - unfold forall_times. cbn [iter]. rewrite iter_switch.
    apply (IH (∀ phi) t). intros sg. cbn.
    apply AllI_named. intros u. simp. apply II. apply weak_cons.
    apply H.
Qed.

Lemma qsep_matrix G (HL : incl KLogic G) m phi (sg : nat -> term) t :
  fb (S m) phi ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S (S (S m))))))
    (kp0 (tagged_matrix (domain_cut (quotient_predicate phi))))) G ->
  G ⊢C raw_empty t -> G ⊢C qtrans t (ax_sep' phi)[sg].
Proof.
  intros Hfb Henv Hinst Hempty. cbn [qtrans ax_sep'].
  fall a. fintro Hta.
  pose proof (qseparation_exists _ HL m phi sg t a Hfb Henv Hinst Hempty Hta) as T.
  unfold qseparation in T. kconv T.
Qed.

Theorem K0_qsep n phi : K0 ⊢TC qaxiom (forall_times n (ax_sep' phi)).
Proof.
  destruct (fb_exists phi) as [m Hm].
  assert (Hfb : fb (S m) phi) by (eapply fb_mono; [exact Hm|lia]).
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (si := forall_times (S (S (S (S (S (S m))))))
    (kp0 (tagged_matrix (domain_cut (quotient_predicate phi))))).
  set (B0 := KLogic ++ [ei; si]).
  assert (HL : incl KLogic B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HSI : In si B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KLogic_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded,
        quotient_predicate_bounded, Hfb.
  - unfold qaxiom. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HL' : incl KLogic G) by exact HL;
      assert (HEI' : In ei G) by exact HEI;
      assert (HSI' : In si G) by exact HSI
    end.
    fintro Hempty. apply qtrans_ft_intro. intros sg.
    exact (qsep_matrix _ HL' m phi sg t Hfb HEI' HSI' Hempty).
Qed.

Corollary KPrimeOrd_qsep n phi : KPrimeOrd ⊢TC qaxiom (forall_times n (ax_sep' phi)).
Proof. apply K0_derivation_to_KPrimeOrd, K0_qsep. Qed.
