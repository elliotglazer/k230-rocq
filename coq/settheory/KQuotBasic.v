(** Empty set and Pairing with quotient equality and membership. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KBase KMarkers KDomain KTagged KDPair KQuot KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition qempty (t e : term) : form :=
  t ∈' e ∧ ∀ (t`[↑] ∈' $0 → (dmem t`[↑] $0 e`[↑] → ⊥)).
Definition qpair (t a b c : term) : form :=
  t ∈' c ∧ ∀ (t`[↑] ∈' $0 →
    (dmem t`[↑] $0 c`[↑] ↔ (deqv t`[↑] $0 a`[↑] ∨ deqv t`[↑] $0 b`[↑]))).
#[global] Arguments qempty : simpl never.
#[global] Arguments qpair : simpl never.
Lemma qempty_subst t e sg : (qempty t e)[sg] = qempty t`[sg] e`[sg].
Proof. psubst qempty. Qed.
Lemma qpair_subst t a b c sg : (qpair t a b c)[sg] = qpair t`[sg] a`[sg] b`[sg] c`[sg].
Proof. psubst qpair. Qed.
#[global] Hint Rewrite qempty_subst qpair_subst : fsub.

Lemma domain_empty_qempty G t e : G ⊢C domain_empty t e -> G ⊢C qempty t e.
Proof.
  intros H. unfold domain_empty in H. fdestr H Hte Hnone.
  unfold qempty. fsplit; [exact Hte|]. fall u. fintro Htu. fintro Hmem.
  unfold dmem in Hmem. fex Hmem v HV. pose proof (CE1 HV) as Hv.
  unfold dchild in Hv. fdestr Hv Htv Hve.
  finst Hnone v. fmp Hnone Htv. exact (IE Hnone Hve).
Qed.

Lemma domain_pair_qpair G (HE : incl EqAx G) t a b c :
  G ⊢C t ∈' a -> G ⊢C t ∈' b -> G ⊢C domain_pair t a b c -> G ⊢C qpair t a b c.
Proof.
  intros Hta Htb HP. unfold domain_pair in HP. fdestr HP Htc Hmembers.
  unfold qpair. fsplit; [exact Htc|]. fall u. fintro Htu. fsplit.
  - fintro Huc. unfold dmem in Huc. fex Huc v HV. fdestr HV Hchild Huv.
    unfold dchild in Hchild. fdestr Hchild Htv Hvc.
    pose proof Hmembers as H. finst H v. fmp H Htv.
    pose proof (iff_l _ _ _ H Hvc) as E. fcases E Hva Hvb.
    + fleft. frewE Hva (deqv t`[↑] u`[↑] $0). exact Huv.
    + fright. frewE Hvb (deqv t`[↑] u`[↑] $0). exact Huv.
  - fintro Hcases. fcases Hcases Hua Hub.
    + fassert Hac : (a ∈' c).
      { pose proof Hmembers as H. finst H a. fmp H Hta.
        apply (iff_r _ _ _ H). fleft. feqE. }
      unfold dmem. fexists a. fsplit; [unfold dchild; fsplit; assumption|exact Hua].
    + fassert Hbc : (b ∈' c).
      { pose proof Hmembers as H. finst H b. fmp H Htb.
        apply (iff_r _ _ _ H). fright. feqE. }
      unfold dmem. fexists b. fsplit; [unfold dchild; fsplit; assumption|exact Hub].
Qed.

Definition qempty_statement : form := ∀ (raw_empty $0 → ∃ qempty $1 $0).
Theorem K0_proves_qempty : K0 ⊢TC qempty_statement.
Proof.
  exists KBase. split; [exact KBase_ok|]. unfold qempty_statement. fall t.
  match goal with |- ?G ⊢C _ =>
    assert (HB : incl KBase G) by (intros a Ha; exact Ha)
  end.
  fintro Hempty. fobtain (domain_empty_exists _ HB t Hempty) as e He.
  fexists e. exact (domain_empty_qempty _ t e He).
Qed.

Definition qpair_statement : form :=
  ∀ ∀ ∀ (raw_empty $2 → $2 ∈' $1 → $2 ∈' $0 → ∃ qpair $3 $2 $1 $0).
Theorem K0_proves_qpair : K0 ⊢TC qpair_statement.
Proof.
  set (pi := forall_times 3 (kp0 (tagged_matrix true_formula))).
  set (B0 := KBase ++ [pi]).
  assert (HB : incl KBase B0) by (intros a Ha; apply in_or_app; now left).
  assert (HPI : In pi B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros a Ha. apply in_app_or in Ha as [Ha|[<-|[]]].
    + apply KBase_ok, Ha.
    + apply K0_instance, kp0_closed, (tagged_matrix_bounded 0). cbn. tauto.
  - unfold qpair_statement. fall t. fall a. fall b.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HPI' : In pi G) by exact HPI
    end.
    fintro Hempty. fintro Hta. fintro Htb.
    pose proof (KBase_eq _ HB') as HE.
    fobtain (domain_pair_exists _ HB' t a b HPI' Hempty Hta Htb) as c HC.
    fexists c. exact (domain_pair_qpair _ HE t a b c Hta Htb HC).
Qed.

Corollary KPrimeOrd_proves_qempty : KPrimeOrd ⊢TC qempty_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_qempty. Qed.
Corollary KPrimeOrd_proves_qpair : KPrimeOrd ⊢TC qpair_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_qpair. Qed.
