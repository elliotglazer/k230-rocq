(** A fixed raw bound for all representatives produced by domain Separation. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw KPTransitive KBase KMarkers KPSeparation KDomain KTagged KDSeparation KQuot.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma fixed_separation_bound G (HB : incl KBase G) t a :
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a ->
  G ⊢C ∃ (envelope_profile t`[↑] a`[↑] $0 ∧
    ∃ (raw_transitive $0 ∧ ($1 ∈' $0 ∧ t`[↑]`[↑] ∈' $0))).
Proof.
  intros Henv Hempty Hta. pose proof (KBase_eq _ HB) as HE.
  fobtain (domain_envelope_exists _ HB t a Henv) as b HP.
  pose proof (domain_envelope_facts _ HE t a b Hempty Hta HP) as HF.
  pose proof (CE1 (CE1 HF)) as Hab.
  fobtain (KBase_transitive _ HB b) as v HV. fdestr HV HbV Htrans.
  pose proof (raw_transitive_element _ v b a Htrans HbV Hab) as HaV.
  pose proof (raw_transitive_element _ v a t Htrans HaV Hta) as HtV.
  fexists b. fsplit; [exact HP|]. fexists v. fsplit; [exact Htrans|]. fsplit; assumption.
Qed.

Lemma bounded_domain_separation G (HB : incl KBase G) n theta (sg : nat -> term) t a b v :
  fb (S n) theta ->
  In (forall_times (S (S (S (S (S n))))) (kp0 (tagged_matrix (domain_cut theta)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C envelope_profile t a b ->
  G ⊢C raw_transitive v -> G ⊢C b ∈' v -> G ⊢C t ∈' v ->
  G ⊢C ∃ (raw_subset $0 v`[↑] ∧ (t`[↑] ∈' $0 ∧
    ∀ (t`[↑]`[↑] ∈' $0 →
      ($0 ∈' $1 ↔ ($0 ∈' a`[↑]`[↑] ∧ theta[$0 .: (fun k => (sg k)`[↑]`[↑])]))))).
Proof.
  intros Hfb Hinst Hempty Hta HP Htrans HbV HtV. pose proof (KBase_eq _ HB) as HE.
  pose proof (domain_envelope_facts _ HE t a b Hempty Hta HP) as HF.
  pose proof (CE2 HF) as Hnegative.
  pose proof (CE1 Hnegative) as HnotB. pose proof (CE2 Hnegative) as Hne.
  pose proof (raw_tagged_comprehension _ HB (S (S n)) (domain_cut theta) (a .: t .: sg) b t
    (domain_cut_bounded n theta Hfb) Hinst Hempty Hne) as T.
  fex T c HC. unfold domain_cut in HC. simp_in HC.
  fexists c. fsplit.
  - unfold raw_subset. fall z. fintro Hzc.
    pose proof HC as H. finst H z. pose proof (iff_l _ _ _ H Hzc) as Hcases.
    fcases Hcases Hzb Hrest.
    + fmemE.
    + fcases Hrest Hzt Hselected.
      * fmemE.
      * exact (raw_transitive_element _ v b z Htrans HbV (CE1 Hselected)).
  - fsplit.
    + pose proof HC as H. finst H t. apply (iff_r _ _ _ H). fright. fleft. feqE.
    + fall z. fintro Htz. fsplit.
      * fintro Hzc. pose proof HC as H. finst H z.
        pose proof (iff_l _ _ _ H Hzc) as Hcases. fcases Hcases Hzb Hrest.
        -- fabsurd. apply (IE HnotB). fmemE.
        -- fcases Hrest Hzt Hselected.
           ++ unfold raw_empty in Hempty. finst Hempty t. fabsurd. apply (IE Hempty). fmemE.
           ++ pose proof (CE2 Hselected) as Hcut.
              fsplit; [exact (CE1 Hcut)|]. pose proof (CE2 (CE2 Hcut)) as Htheta. kconv Htheta.
      * fintro Hselected. fdestr Hselected Hza Htheta.
        pose proof HC as H. finst H z. apply (iff_r _ _ _ H).
        fright. fright. fsplit.
        -- pose proof HP as P. unfold envelope_profile in P. finst P z.
           apply (iff_r _ _ _ P). fright. fsplit; assumption.
        -- fsplit; [exact Hza|]. fsplit; [exact Htz|]. kconv Htheta.
Qed.
