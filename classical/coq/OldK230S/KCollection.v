(** Supported Collection in D_t, with no simultaneous choice of witnesses. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KPRaw KPPair KBase KMarkers KPSeparation KDomain KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma singleton_unique G u v p :
  G ⊢C raw_singleton u p -> G ⊢C raw_singleton v p -> G ⊢C u ≡' v.
Proof.
  intros Hu Hv. unfold raw_singleton in Hu, Hv.
  pose proof (CE2 Hv) as H. finst H u. exact (IE H (CE1 Hu)).
Qed.

Lemma binary_input_congr G (HE : incl EqAx G) psi rho y u v :
  G ⊢C u ≡' v -> G ⊢C psi[y .: u .: rho] -> G ⊢C psi[y .: v .: rho].
Proof.
  intros E H. eapply (leibE_gen psi G (y .: u .: rho) (y .: v .: rho) HE); [|exact H].
  intros [|[|k]]; cbn; [feqE|exact E|feqE].
Qed.

(** Output/input are 0/1. Parameters are B,t,r,A followed by psi's parameters. *)
Definition collection_matrix (psi : form) : form :=
  ($1 ≡' $4 ∧ $0 ≡' $2) ∨
  (($1 ≡' $3 ∧ $0 ≡' $3) ∨
   ∃ (raw_singleton $0 $2 ∧
      (($4 ∈' $0 ∧ $0 ∈' $6) ∧
       ($4 ∈' $1 ∧ psi[$1 .: $0 .: (fun k => $(7 + k))])))).

Lemma collection_matrix_bounded n psi : fb (S (S n)) psi ->
  fb (S (S (S (S (S (S n)))))) (collection_matrix psi).
Proof.
  intros H. unfold collection_matrix, raw_singleton. cbn.
  repeat split; try lia. eapply fb_subst; [exact H|]. intros [|[|k]] Hk; cbn; lia.
Qed.

Definition collection_profile (t a c : term) (psi : form) (rho : nat -> term) : form :=
  t ∈' c ∧
  ((∀ ((t`[↑] ∈' $0 ∧ $0 ∈' a`[↑]) →
       (∃ (t`[↑]`[↑] ∈' $0 ∧ psi[$0 .: $1 .: (fun k => (rho k)`[↑]`[↑])])) →
       ∃ (t`[↑]`[↑] ∈' $0 ∧ ($0 ∈' c`[↑]`[↑] ∧ psi[$0 .: $1 .: (fun k => (rho k)`[↑]`[↑])])))) ∧
   ∀ ((t`[↑] ∈' $0 ∧ $0 ∈' c`[↑]) →
       ∃ ((t`[↑]`[↑] ∈' $0 ∧ $0 ∈' a`[↑]`[↑]) ∧ psi[$1 .: $0 .: (fun k => (rho k)`[↑]`[↑])]))).

#[global] Arguments collection_profile : simpl never.
Lemma collection_profile_subst t a c psi rho sg :
  (collection_profile t a c psi rho)[sg] =
  collection_profile t`[sg] a`[sg] c`[sg] psi (fun k => (rho k)`[sg]).
Proof. unfold collection_profile. cbn. autorewrite with fsub. kform_eq. Qed.
#[global] Hint Rewrite collection_profile_subst : fsub.

Lemma domain_collection G (HB : incl KBase G) n psi (sg : nat -> term) t a :
  fb (S (S n)) psi ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S n)))) (kp0 (collection_matrix psi))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a ->
  G ⊢C ∃ collection_profile t`[↑] a`[↑] $0 psi (fun k => (sg k)`[↑]).
Proof.
  intros Hfb Henv Hinst Hempty Hta. pose proof (KBase_eq _ HB) as HE.
  fobtain (domain_envelope_exists _ HB t a Henv) as B HP.
  pose proof (domain_envelope_facts _ HE t a B Hempty Hta HP) as HF.
  pose proof (CE1 (CE2 HF)) as HnotB. pose proof (CE2 (CE2 HF)) as Hne.
  fobtain (KBase_pair _ HB B t) as r Hr.
  pose proof (pair_not_empty _ HE B t r Hempty Hr) as Hrt.
  fassert HnotSingle : (∀ (raw_singleton $0 r`[↑] → ⊥)).
  { fall x. exact (pair_not_singleton _ HE B t r x Hne Hr). }
  pose proof (kp0_use _ (S (S (S (S n)))) (collection_matrix psi) (B .: t .: r .: a .: sg) r
    Hinst (collection_matrix_bounded n psi Hfb)) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold collection_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fassert HBC : (B ∈' C).
  { pose proof Hrequest as H. finst H r.
    fassert Helig : (r ≡' r ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset r`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp H Helig.
    match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
    { fexists B. fleft. fsplit; feqE. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hroot Hrest.
    - pose proof (CE2 Hroot) as HyB. fmemE.
    - fcases Hrest Hmark Hselected.
      + pose proof (CE1 Hmark) as Hrt'. fabsurd. exact (IE Hrt Hrt').
      + fex Hselected u Hu. pose proof (CE1 Hu) as Hur.
        pose proof HnotSingle as Hns. finst Hns u. fabsurd. exact (IE Hns Hur). }
  fassert HtC : (t ∈' C).
  { pose proof Hrequest as H. finst H t.
    fassert Helig : (t ≡' r ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset t`[↑] $0)).
    { fright. fexists B. fsplit; [exact HBC|].
      unfold raw_subset, raw_empty in *. fall z. fintro Hzt.
      finst Hempty z. fabsurd. exact (IE Hempty Hzt). }
    unfold raw_subset in Helig. fmp H Helig.
    match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
    { fexists t. fright. fleft. fsplit; feqE. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hroot Hrest.
    - pose proof (CE1 Hroot) as Htr. fabsurd. apply (IE Hrt). feqE.
    - fcases Hrest Hmark Hselected.
      + pose proof (CE2 Hmark) as Hyt. fmemE.
      + fex Hselected u Hu. pose proof (CE1 Hu) as Hut. fabsurd.
        exact (empty_not_singleton _ t u Hempty Hut). }
  fexists C. fsplit; [exact HtC|]. fsplit.
  - fall u. fintro Hu. fintro Hex. fdestr Hu Htu Hua. fex Hex w Hw. fdestr Hw Htw Hpsi.
    fobtain (KBase_singleton _ HB u) as p Hp.
    pose proof Hrequest as H. finst H p.
    fassert Helig : (p ≡' r ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset p`[↑] $0)).
    { fright. fexists B. fsplit; [exact HBC|].
      unfold raw_subset. fall z. fintro Hzp.
      pose proof Hp as Hp'. unfold raw_singleton in Hp'.
      pose proof (CE2 Hp') as Hzu. finst Hzu z. fmp Hzu Hzp.
      fassert HuB : (u ∈' B).
      { pose proof HP as P. unfold envelope_profile in P. finst P u.
        apply (iff_r _ _ _ P). fright. fsplit; assumption. }
      fmemE. }
    unfold raw_subset in Helig. fmp H Helig.
    match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
    { fexists w. fright. fright. fexists u. fsplit; [exact Hp|].
      fsplit; [fsplit; assumption|]. fsplit; [exact Htw|]. kconv Hpsi. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hroot Hrest.
    + pose proof (CE1 Hroot) as Hpr.
      pose proof (singleton_container _ HE u p r Hpr Hp) as Hur.
      pose proof HnotSingle as Hns. finst Hns u. fabsurd. exact (IE Hns Hur).
    + fcases Hrest Hmark Hselected.
      * pose proof (CE1 Hmark) as Hpt.
        pose proof (singleton_container _ HE u p t Hpt Hp) as Hut. fabsurd.
        exact (empty_not_singleton _ t u Hempty Hut).
      * fex Hselected v Hv. fdestr Hv Hvp Hfacts.
        pose proof (CE2 Hfacts) as Hyfacts. fdestr Hyfacts Hty Hpsiyv.
        pose proof (singleton_unique _ v u p Hvp Hp) as Evu.
        fexists y. fsplit; [exact Hty|]. fsplit; [exact HyC|].
        fassert Hpsiyv' : (psi[y .: v .: sg]). { kconv Hpsiyv. }
        pose proof (binary_input_congr _ HE psi sg y v u Evu Hpsiyv') as Hpsiyu.
        kconv Hpsiyu.
  - fall y. fintro Hy. fdestr Hy Hty HyC.
    pose proof Hsupport as H. finst H y. fmp H HyC. fex H p Hcases.
    fcases Hcases Hroot Hrest.
    + pose proof (CE2 Hroot) as HyB. fabsurd. apply (IE HnotB). fmemE.
    + fcases Hrest Hmark Hselected.
      * pose proof (CE2 Hmark) as Hyt. unfold raw_empty in Hempty. finst Hempty t.
        fabsurd. apply (IE Hempty). fmemE.
      * fex Hselected u Hu. pose proof (CE2 Hu) as Hfacts.
        fexists u. fsplit; [exact (CE1 Hfacts)|].
        pose proof (CE2 (CE2 Hfacts)) as Hpsi. kconv Hpsi.
Qed.

Definition domain_collection_statement (psi : form) : form :=
  ∀ ∀ (raw_empty $0 → $0 ∈' $1 →
    ∃ collection_profile $1 $2 $0 psi (fun k => $(3 + k))).

Theorem K0_proves_domain_collection n psi : fb (S (S n)) psi ->
  K0 ⊢TC forall_times n (domain_collection_statement psi).
Proof.
  intros Hfb.
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (ci := forall_times (S (S (S (S n)))) (kp0 (collection_matrix psi))).
  set (B0 := KBase ++ [ei; ci]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HCI : In ci B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, collection_matrix_bounded, Hfb.
  - apply ft_intro. intros sg. unfold domain_collection_statement. cbn.
    fall a. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HEI' : In ei G) by exact HEI;
      assert (HCI' : In ci G) by exact HCI
    end.
    fintro Hempty. fintro Hta.
    pose proof (domain_collection _ HB' n psi sg t a Hfb HEI' HCI' Hempty Hta) as T.
    unfold collection_profile in T |- *. cbn. kconv T.
Qed.

Corollary KPrimeOrd_proves_domain_collection n psi : fb (S (S n)) psi ->
  KPrimeOrd ⊢TC forall_times n (domain_collection_statement psi).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_domain_collection, H. Qed.
