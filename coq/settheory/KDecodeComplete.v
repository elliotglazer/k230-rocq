(** Every closed decoded source bundle is derivable in the ordinary core
    theory. Together with KDecodeTheory this compares the two finite-proof
    predicates. It does not yet identify the numerical proof enumerator. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_tr Std_alpha Std_gen Std_F Std_iface
  Std_iface2 Std_setnd Std_setbase Std_breq Std_brnd.
From K230S Require Import KP0 KP0Use KPRaw KPrimeCore KPrimeTheory KCode230 KDecoder230
  KDecodeFresh KDecodeBundle KDecodeLogic KDecodeBridge KDecodeAbstract
  KDecodeReverse KDecodeDegenerate KDecodeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma KPrimeOrd_distinct_named q a b c : a <> b -> c <> a -> c <> b ->
  fr c q = false -> exists B,
  incl EqAx B /\ (forall p, In p B -> KPrimeOrd p) /\
  (forall rho, B ⊢C dB rho (KCore a b c q)).
Proof.
  intros Hab Hca Hcb Hfresh.
  destruct (fb_exists (abstract_matrix a b q)) as [N HN].
  assert (Hfb : fb (S (S N)) (abstract_matrix a b q)) by
    (eapply fb_mono; [exact HN|lia]).
  assert (Hclosed : closedf (forall_times N (kprime_core (abstract_matrix a b q)))) by
    (apply kprime_core_closed; exact Hfb).
  set (B := EqAx ++ [forall_times N (kprime_core (abstract_matrix a b q))]).
  exists B. split.
  - intros p Hp. apply in_or_app. now left.
  - split.
    + intros p Hp. apply in_app_or in Hp as [Hp|[<-|[]]].
      * now apply KPrimeOrd_eq.
      * now apply KPrimeOrd_instance.
    + intros rho. apply ordinary_to_named_source; try assumption.
      apply (closed_inst B N _ rho Hclosed).
      apply Ctx, in_or_app. right. now left.
Qed.

Lemma singleton_proves_hosting G : G ⊢C raw_singleton_axiom -> G ⊢C hosting230.
Proof.
  intros H. unfold hosting230. fall x.
  unfold raw_singleton_axiom in H. finst H x. fex H C HC.
  fexists C. unfold raw_singleton in HC. exact (CE1 HC).
Qed.

Lemma KPrimeOrd_same_named q a c : c <> a -> fr c q = false -> exists B,
  incl EqAx B /\ (forall p, In p B -> KPrimeOrd p) /\
  (forall rho, B ⊢C dB rho (KCore a a c q)).
Proof.
  intros Hca Hfresh.
  assert (E : KPrimeOrd ⊢TC empty_object) by
    (apply K0_derivation_to_KPrimeOrd, K0_proves_empty).
  assert (Sg : KPrimeOrd ⊢TC raw_singleton_axiom) by
    (apply K0_derivation_to_KPrimeOrd, K0_proves_singleton).
  destruct E as [E [HE DE]]. destruct Sg as [Sg [HS DS]].
  set (B := EqAx ++ E ++ Sg).
  assert (HEB : incl E B) by
    (intros p Hp; apply in_or_app; right; apply in_or_app; now left).
  assert (HSB : incl Sg B) by
    (intros p Hp; apply in_or_app; right; apply in_or_app; now right).
  exists B. split.
  - intros p Hp. apply in_or_app. now left.
  - split.
    + intros p Hp. apply in_app_or in Hp as [Hp|Hp].
      * now apply KPrimeOrd_eq.
      * apply in_app_or in Hp as [Hp|Hp]; [apply HE|apply HS]; exact Hp.
    + intros rho. apply named_same_roles; try assumption.
      * eapply Weak; [exact DE|exact HEB].
      * apply singleton_proves_hosting. eapply Weak; [exact DS|exact HSB].
Qed.

Lemma decoded_bundle_from_core G a b c n : incl EqAx G -> c <> a -> c <> b ->
  (forall rho, G ⊢C dB rho (KCore a b c (D c))) ->
  G ⊢C Lib n (D (gated230 a b c)).
Proof.
  intros HE Hca Hcb Hcore. apply Lib_intro. intros rho.
  apply (iff_r _ _ _ (leqv_dB230 G rho _ _ HE
    (decoded_enabled_core_equiv a b c Hca Hcb))).
  exact (Hcore rho).
Qed.

Lemma KPrimeOrd_proves_disabled a b c n : c = a \/ c = b ->
  KPrimeOrd ⊢TC Lib n (D (gated230 a b c)).
Proof.
  intros Hgate. exists EqAx. split.
  - intros p Hp. now apply KPrimeOrd_eq.
  - apply Lib_intro. intros rho.
    exact (lprov_dB230 _ (decoded_disabled_pure a b c Hgate) rho).
Qed.

Theorem KPrimeOrd_proves_decoded a b c n :
  KPrimeOrd ⊢TC Lib n (D (gated230 a b c)).
Proof.
  destruct (Nat.eq_dec c a) as [Hca|Hca].
  - apply KPrimeOrd_proves_disabled. now left.
  - destruct (Nat.eq_dec c b) as [Hcb|Hcb].
    + apply KPrimeOrd_proves_disabled. now right.
    + destruct (Nat.eq_dec a b) as [->|Hab].
      * destruct (KPrimeOrd_same_named (D c) b c Hcb (D_private_fresh c))
          as [B [HE [HB Hcore]]].
        exists B. split; [exact HB|].
        exact (decoded_bundle_from_core B b b c n HE Hcb Hcb Hcore).
      * destruct (KPrimeOrd_distinct_named (D c) a b c Hab Hca Hcb (D_private_fresh c))
          as [B [HE [HB Hcore]]].
        exists B. split; [exact HB|].
        exact (decoded_bundle_from_core B a b c n HE Hca Hcb Hcore).
Qed.

Theorem DecodedK230Ord_derivation_to_KPrimeOrd phi :
  DecodedK230Ord ⊢TC phi -> KPrimeOrd ⊢TC phi.
Proof.
  apply theory_derivation_map. intros p Hp. destruct Hp as [p Hp|a b c n Hn].
  - exists [p]. split.
    + intros q [<-|[]]. now apply KPrimeOrd_eq.
    + apply Ctx. now left.
  - apply KPrimeOrd_proves_decoded.
Qed.

Theorem decoded_core_derivations_equivalent phi :
  DecodedK230Ord ⊢TC phi <-> KPrimeOrd ⊢TC phi.
Proof.
  split; [apply DecodedK230Ord_derivation_to_KPrimeOrd|
          apply KPrimeOrd_derivation_to_DecodedK230Ord].
Qed.
