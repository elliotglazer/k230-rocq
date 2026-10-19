(** Three-branch tagged comprehension. The auxiliary pair seed is constructed
    and discharged; the empty marker and distinct envelope are parameters. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw KPPair KBase KMarkers KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** Input/output are 1/0. Parameters are B, t, root pair r, then theta's parameters. *)
Definition tagged_matrix (theta : form) : form :=
  ($1 ≡' $4 ∧ $0 ≡' $2) ∨
  (($1 ≡' $3 ∧ $0 ≡' $3) ∨
   (raw_singleton $0 $1 ∧ ($0 ∈' $2 ∧ theta[$0 .: (fun k => $(5 + k))]))).

Lemma tagged_matrix_bounded n theta : fb (S n) theta ->
  fb (S (S (S (S (S n))))) (tagged_matrix theta).
Proof.
  intros H. unfold tagged_matrix, raw_singleton. cbn.
  repeat split; try lia. eapply fb_subst; [exact H|]. intros [|k] Hk; cbn; lia.
Qed.

Lemma raw_tagged_comprehension G (HB : incl KBase G) n theta (sg : nat -> term) B t :
  fb (S n) theta ->
  In (forall_times (S (S (S n))) (kp0 (tagged_matrix theta))) G ->
  G ⊢C raw_empty t -> G ⊢C ¬ (B ≡' t) ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔
    ($0 ≡' B`[↑]`[↑] ∨ ($0 ≡' t`[↑]`[↑] ∨
      ($0 ∈' B`[↑]`[↑] ∧ theta[$0 .: (fun k => (sg k)`[↑]`[↑])])))).
Proof.
  intros Hfb Hinst Hempty Hbt. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_pair _ HB B t) as r Hr.
  pose proof (pair_not_empty _ HE B t r Hempty Hr) as Hrt.
  fassert HnotSingle : (∀ (raw_singleton $0 r`[↑] → ⊥)).
  { fall x. exact (pair_not_singleton _ HE B t r x Hbt Hr). }
  pose proof (kp0_use _ (S (S (S n))) (tagged_matrix theta) (B .: t .: r .: sg) r
    Hinst (tagged_matrix_bounded n theta Hfb)) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold tagged_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
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
    - fcases Hrest Hmark Hsingle.
      + pose proof (CE1 Hmark) as Hrt'. fabsurd. exact (IE Hrt Hrt').
      + pose proof (CE1 Hsingle) as Hyr.
        pose proof HnotSingle as Hns. finst Hns y. fabsurd. exact (IE Hns Hyr). }
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
    - fcases Hrest Hmark Hsingle.
      + pose proof (CE2 Hmark) as Hyt. fmemE.
      + pose proof (CE1 Hsingle) as Hyt. fabsurd.
        exact (empty_not_singleton _ t y Hempty Hyt). }
  fexists C. fall x. fsplit.
  - fintro HxC. pose proof Hsupport as H. finst H x. fmp H HxC.
    fex H p Hp. fcases Hp Hroot Hrest.
    + fleft. exact (CE2 Hroot).
    + fright. fcases Hrest Hmark Hsingle.
      * fleft. exact (CE2 Hmark).
      * fright. pose proof (CE2 Hsingle) as Hselected.
        fsplit; [exact (CE1 Hselected)|]. pose proof (CE2 Hselected) as Htheta. kconv Htheta.
  - fintro Hcases. fcases Hcases HxB Hrest.
    + fmemE.
    + fcases Hrest Hxt Hselected.
      * fmemE.
      * fdestr Hselected HxB Htheta.
        fobtain (KBase_singleton _ HB x) as p Hp.
        pose proof Hrequest as H. finst H p.
        fassert Helig : (p ≡' r ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset p`[↑] $0)).
        { fright. fexists B. fsplit; [exact HBC|].
          unfold raw_subset. fall z. fintro Hzp.
          pose proof Hp as Hp'. unfold raw_singleton in Hp'.
          pose proof (CE2 Hp') as Hprofile. finst Hprofile z. fmp Hprofile Hzp. fmemE. }
        unfold raw_subset in Helig. fmp H Helig.
        match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
        { fexists x. fright. fright. fsplit; [exact Hp|].
          fsplit; [exact HxB|]. kconv Htheta. }
        fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
        fcases Hycases Hroot Hrest.
        -- pose proof (CE1 Hroot) as Hpr.
           pose proof (singleton_container _ HE x p r Hpr Hp) as Hxr.
           pose proof HnotSingle as Hns. finst Hns x. fabsurd. exact (IE Hns Hxr).
        -- fcases Hrest Hmark Hsingle.
           ++ pose proof (CE1 Hmark) as Hpt.
              pose proof (singleton_container _ HE x p t Hpt Hp) as Hxt.
              fabsurd. exact (empty_not_singleton _ t x Hempty Hxt).
           ++ pose proof (CE1 Hsingle) as Hyp.
              unfold raw_singleton in Hp, Hyp.
              pose proof (CE1 Hp) as Hxp. pose proof (CE2 Hyp) as Hprofile.
              finst Hprofile x. fmp Hprofile Hxp. fmemE.
Qed.

Definition tagged_statement (theta : form) : form :=
  ∀ ∀ (raw_empty $0 → ¬ ($1 ≡' $0) →
    ∃ ∀ ($0 ∈' $1 ↔ ($0 ≡' $3 ∨ ($0 ≡' $2 ∨
      ($0 ∈' $3 ∧ theta[$0 .: (fun k => $(4 + k))]))))).

Theorem K0_proves_tagged_comprehension n theta : fb (S n) theta ->
  K0 ⊢TC forall_times n (tagged_statement theta).
Proof.
  intros Hfb.
  set (inst := forall_times (S (S (S n))) (kp0 (tagged_matrix theta))).
  set (B0 := KBase ++ [inst]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HI : In inst B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, Hfb.
  - apply ft_intro. intros sg. unfold tagged_statement. cbn.
    fall B. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HI' : In inst G) by exact HI
    end.
    fintro Hempty. fintro Hbt.
    pose proof (raw_tagged_comprehension _ HB' n theta sg B t Hfb HI' Hempty Hbt) as T.
    kconv T.
Qed.

Corollary KPrimeOrd_proves_tagged_comprehension n theta : fb (S n) theta ->
  KPrimeOrd ⊢TC forall_times n (tagged_statement theta).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_tagged_comprehension, H. Qed.

