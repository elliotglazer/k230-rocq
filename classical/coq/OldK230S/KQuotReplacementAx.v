(** The reference Replacement axiom orders input before output. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KDomain KPSeparation KTagged KCollection KQuot KQuotFormula KQuotReplacement KQuotAxioms KQuotSchema KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition swap_relation (phi : form) : form := phi[$1 .: $0 .: (fun k => $(2 + k))].
Lemma swap_relation_bounded m phi : fb (S (S m)) phi -> fb (S (S m)) (swap_relation phi).
Proof.
  intros H. unfold swap_relation. eapply fb_subst; [exact H|].
  intros [|[|k]] Hk; cbn; lia.
Qed.

Lemma canonical_functional G t a phi (sg : nat -> term) :
  G ⊢C qtrans t (fun_rel' phi)[sg] ->
  G ⊢C qfunctional t a (swap_relation phi) sg.
Proof.
  intros H. cbn [qtrans fun_rel'] in H. unfold qfunctional.
  fall x. fintro Hx. fdestr Hx Htx Hxa.
  fall y. fintro Hty. fall z. fintro Htz. fintro Hxy. fintro Hxz.
  finst H x. fmp H Htx. finst H y. fmp H Hty. finst H z. fmp H Htz.
  unfold swap_relation in Hxy, Hxz.
  match type of H with _ ⊢C ?P → _ => fassert HP : P end.
  { kconv Hxy. }
  fmp H HP.
  match type of H with _ ⊢C ?P → _ => fassert HQ : P end.
  { kconv Hxz. }
  exact (IE H HQ).
Qed.

Lemma qrep_matrix G (HL : incl KLogic G) m phi (sg : nat -> term) t :
  fb (S (S m)) phi ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S (S m)))))
    (kp0 (collection_matrix (replacement_predicate (swap_relation phi))))) G ->
  G ⊢C raw_empty t -> G ⊢C qtrans t (ax_rep' phi)[sg].
Proof.
  intros Hfb Henv Hinst Hempty. cbn [qtrans ax_rep'].
  fintro Hfun. fall a. fintro Hta.
  fassert HF : (qfunctional t a (swap_relation phi) sg).
  { apply canonical_functional. kconv Hfun. }
  pose proof (qreplacement_exists _ HL m (swap_relation phi) sg t a
    (swap_relation_bounded m phi Hfb) Henv Hinst Hempty Hta HF) as T.
  fex T c HC. unfold qimage in HC. fdestr HC Htc Hmembers.
  fexists c. fsplit; [exact Htc|]. fall y. fintro Hty.
  pose proof Hmembers as HM. finst HM y. fmp HM Hty. fsplit.
  - fintro Hyc. pose proof (iff_l _ _ _ HM Hyc) as HX.
    fex HX x Hx. fdestr Hx Hxm Hphi. fdestr Hxm Htx Hxa.
    fexists x. fsplit; [exact Htx|]. fsplit; [exact Hxa|].
    unfold swap_relation in Hphi. kconv Hphi.
  - fintro HX. fex HX x Hx. fdestr Hx Htx Hrest. fdestr Hrest Hxa Hphi.
    apply (iff_r _ _ _ HM). fexists x. fsplit.
    + fsplit; assumption.
    + unfold swap_relation. kconv Hphi.
Qed.

Theorem K0_qrep n phi : K0 ⊢TC qaxiom (forall_times n (ax_rep' phi)).
Proof.
  destruct (fb_exists phi) as [m Hm].
  assert (Hfb : fb (S (S m)) phi) by (eapply fb_mono; [exact Hm|lia]).
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (ri := forall_times (S (S (S (S (S m)))))
    (kp0 (collection_matrix (replacement_predicate (swap_relation phi))))).
  set (B0 := KLogic ++ [ei; ri]).
  assert (HL : incl KLogic B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KLogic_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, collection_matrix_bounded,
        replacement_predicate_bounded, swap_relation_bounded, Hfb.
  - unfold qaxiom. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HL' : incl KLogic G) by exact HL;
      assert (HEI' : In ei G) by exact HEI;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty. apply qtrans_ft_intro. intros sg.
    exact (qrep_matrix _ HL' m phi sg t Hfb HEI' HRI' Hempty).
Qed.

Corollary KPrimeOrd_qrep n phi : KPrimeOrd ⊢TC qaxiom (forall_times n (ax_rep' phi)).
Proof. apply K0_derivation_to_KPrimeOrd, K0_qrep. Qed.

Theorem K0_qZF0 phi : ZF0 phi -> K0 ⊢TC qaxiom phi.
Proof.
  intros H. destruct H as [phi H|phi n H|phi n H].
  - now apply K0_qbase.
  - apply K0_qsep.
  - apply K0_qrep.
Qed.

Corollary KPrimeOrd_qZF0 phi : ZF0 phi -> KPrimeOrd ⊢TC qaxiom phi.
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_qZF0, H. Qed.
