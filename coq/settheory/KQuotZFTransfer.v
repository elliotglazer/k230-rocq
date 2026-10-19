(** Closed source proofs transferred by direct natural deduction. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq Std_setinf.
From K230S Require Import KP0 KP0Use KBase KMarkers KDomain KQuotFormula KQuotDeduction KQuotAxioms KQuotReplacementAx KQuotInfinity KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ZF0_closed a : ZF0 a -> closedf a.
Proof. intros [phi H|phi n H|phi n H]; [now apply ZF0base_closed|exact H|exact H]. Qed.
Lemma ZFc_closed a : ZFc a -> closedf a.
Proof. intros [H| ->]; [now apply ZF0_closed|apply ax_om'_closed]. Qed.

Theorem K0_qtranslate_closed (T : form -> Prop) phi :
  (forall a, T a -> closedf a) ->
  (forall a, T a -> K0 ⊢TC qaxiom a) ->
  T ⊢TC phi -> closedf phi -> K0 ⊢TC qaxiom phi.
Proof.
  intros HTclosed HT [A [HA DA]] Hphi.
  destruct (collect_theory_proofs K0 (map qaxiom A)) as [B [HB DB]].
  { intros b Hb. apply in_map_iff in Hb as [a [<- Ha]]. apply HT, HA, Ha. }
  exists (KBase ++ B). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply KBase_ok|apply HB]; assumption.
  - assert (HK : incl KBase (KBase ++ B)) by (intros b Hb; apply in_or_app; now left).
    assert (HB' : incl B (KBase ++ B)) by (intros b Hb; apply in_or_app; now right).
    unfold qaxiom. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HK' : incl KBase G) by exact HK;
      assert (HB'' : incl B G) by exact HB'
    end.
    fintro Hempty. fobtain (domain_empty_exists _ HK' t Hempty) as e HE.
    unfold domain_empty in HE. pose proof (CE1 HE) as Hte.
    match goal with |- ?G ⊢C _ =>
      assert (DAx : forall a, In a A -> G ⊢C qtrans t a[(fun _ => e)])
    end.
    { intros a Ha.
      assert (HC : closedf a) by (apply HTclosed, HA, Ha).
      pose proof (Weak (DB (qaxiom a) (in_map qaxiom A a Ha)) HB'') as H.
      unfold qaxiom in H. finst H t. fmp H Hempty.
      rewrite (closed_subst a (fun _ => e) HC). exact H. }
    pose proof (qtrans_prv A phi DA _ t (fun _ => e) (fun _ => Hte) DAx) as F.
    rewrite (closed_subst phi (fun _ => e) Hphi) in F. exact F.
Qed.

Theorem K0_qINF : K0 ⊢TC qaxiom INF_lib.
Proof.
  destruct K0_proves_qtranslated_infinity as [B [HB H]]. exists B. split; [exact HB|].
  unfold qaxiom, qtranslated_infinity in *. rewrite (closed_subst INF_lib ↑ INF_lib_closed). exact H.
Qed.

Theorem K0_qomega : K0 ⊢TC qaxiom ax_om'.
Proof.
  apply (K0_qtranslate_closed (fun a => ZF0 a \/ a = INF_lib) ax_om').
  - intros a [H| ->]; [now apply ZF0_closed|apply INF_lib_closed].
  - intros a [H| ->]; [now apply K0_qZF0|apply K0_qINF].
  - exact inf_or_to_zf.
  - apply ax_om'_closed.
Qed.

Theorem K0_qZFc a : ZFc a -> K0 ⊢TC qaxiom a.
Proof. intros [H| ->]; [now apply K0_qZF0|apply K0_qomega]. Qed.

Theorem K0_ZFc_inconsistent : ZFc ⊢TC ⊥ -> K0 ⊢TC ⊥.
Proof.
  intros H.
  destruct (K0_qtranslate_closed ZFc ⊥ ZFc_closed K0_qZFc H I) as [B [HB D]].
  destruct K0_proves_empty as [E [HE DE]].
  exists (B ++ E). split.
  - intros a Ha. apply in_app_or in Ha as [Ha|Ha]; [apply HB|apply HE]; assumption.
  - assert (DB : (B ++ E) ⊢C qaxiom ⊥).
    { eapply Weak; [exact D|]. intros a Ha. apply in_or_app. now left. }
    assert (DE' : (B ++ E) ⊢C empty_object).
    { eapply Weak; [exact DE|]. intros a Ha. apply in_or_app. now right. }
    unfold empty_object in DE'. fex DE' t Hempty.
    unfold qaxiom in DB. finst DB t. exact (IE DB Hempty).
Qed.

Corollary KPrimeOrd_ZFc_inconsistent : ZFc ⊢TC ⊥ -> KPrimeOrd ⊢TC ⊥.
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_ZFc_inconsistent, H. Qed.
