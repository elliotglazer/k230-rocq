(** Exact Separation in D_t. The two raw markers are outside D_t. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KPRaw KBase KMarkers KPSeparation KDomain KTagged KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** The selected object is index 0; parameters are carrier a, marker t, then theta's. *)
Definition domain_cut (theta : form) : form :=
  $0 ∈' $1 ∧ ($2 ∈' $0 ∧ theta[$0 .: (fun k => $(3 + k))]).

Lemma domain_cut_bounded n theta : fb (S n) theta -> fb (S (S (S n))) (domain_cut theta).
Proof.
  intros H. unfold domain_cut. cbn. repeat split; try lia.
  eapply fb_subst; [exact H|]. intros [|k] Hk; cbn; lia.
Qed.

Lemma domain_separation G (HB : incl KBase G) n theta (sg : nat -> term) t a :
  fb (S n) theta ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S (S n))))) (kp0 (tagged_matrix (domain_cut theta)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a ->
  G ⊢C ∃ (t`[↑] ∈' $0 ∧
    ∀ (t`[↑]`[↑] ∈' $0 →
       ($0 ∈' $1 ↔ ($0 ∈' a`[↑]`[↑] ∧ theta[$0 .: (fun k => (sg k)`[↑]`[↑])])))).
Proof.
  intros Hfb Henv Htaginst Hempty Hta. pose proof (KBase_eq _ HB) as HE.
  fobtain (domain_envelope_exists _ HB t a Henv) as B HP.
  pose proof (domain_envelope_facts _ HE t a B Hempty Hta HP) as HF.
  pose proof (CE2 HF) as Hnegative.
  pose proof (CE1 Hnegative) as HnotB. pose proof (CE2 Hnegative) as Hne.
  pose proof (raw_tagged_comprehension _ HB (S (S n)) (domain_cut theta) (a .: t .: sg) B t
    (domain_cut_bounded n theta Hfb) Htaginst Hempty Hne) as T.
  fex T C HT. unfold domain_cut in HT. simp_in HT.
  fexists C. fsplit.
  - pose proof HT as H. finst H t. apply (iff_r _ _ _ H).
    fright. fleft. feqE.
  - fall x. fintro Htx. fsplit.
    + fintro HxC. pose proof HT as H. finst H x.
      pose proof (iff_l _ _ _ H HxC) as Hcases. fcases Hcases HxB Hrest.
      * fabsurd. apply (IE HnotB). fmemE.
      * fcases Hrest Hxt Hselected.
        -- unfold raw_empty in Hempty. finst Hempty t. fabsurd.
           apply (IE Hempty). fmemE.
        -- pose proof (CE2 Hselected) as Hcut.
           fsplit; [exact (CE1 Hcut)|]. pose proof (CE2 (CE2 Hcut)) as Htheta. kconv Htheta.
    + fintro Hselected. fdestr Hselected Hxa Htheta.
      pose proof HT as H. finst H x. apply (iff_r _ _ _ H).
      fright. fright. fsplit.
      * pose proof HP as P. unfold envelope_profile in P. finst P x.
        apply (iff_r _ _ _ P). fright. fsplit; assumption.
      * fsplit; [exact Hxa|]. fsplit; [exact Htx|]. kconv Htheta.
Qed.

Definition domain_separation_statement (theta : form) : form :=
  ∀ ∀ (raw_empty $0 → $0 ∈' $1 →
    ∃ ($1 ∈' $0 ∧ ∀ ($2 ∈' $0 →
      ($0 ∈' $1 ↔ ($0 ∈' $3 ∧ theta[$0 .: (fun k => $(4 + k))]))))).

Theorem K0_proves_domain_separation n theta : fb (S n) theta ->
  K0 ⊢TC forall_times n (domain_separation_statement theta).
Proof.
  intros Hfb.
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (ti := forall_times (S (S (S (S (S n))))) (kp0 (tagged_matrix (domain_cut theta)))).
  set (B0 := KBase ++ [ei; ti]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HTI : In ti B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded, Hfb.
  - apply ft_intro. intros sg. unfold domain_separation_statement. cbn.
    fall a. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HEI' : In ei G) by exact HEI;
      assert (HTI' : In ti G) by exact HTI
    end.
    fintro Hempty. fintro Hta.
    pose proof (domain_separation _ HB' n theta sg t a Hfb HEI' HTI' Hempty Hta) as T.
    kconv T.
Qed.

Corollary KPrimeOrd_proves_domain_separation n theta : fb (S n) theta ->
  KPrimeOrd ⊢TC forall_times n (domain_separation_statement theta).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_domain_separation, H. Qed.
