(** The interpreted domain D_t(x) := t in x, for a fixed raw empty marker t. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KPRaw KBase KMarkers KPSeparation.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition domain_empty (t e : term) : form :=
  t ∈' e ∧ ∀ (t`[↑] ∈' $0 → $0 ∈' e`[↑] → ⊥).

Lemma domain_empty_exists G (HB : incl KBase G) t :
  G ⊢C raw_empty t -> G ⊢C ∃ domain_empty t`[↑] $0.
Proof.
  intros Hempty. pose proof (KBase_eq _ HB) as HE.
  fobtain (KBase_singleton _ HB t) as e He.
  fexists e. unfold domain_empty. fsplit.
  - unfold raw_singleton in He. exact (CE1 He).
  - fall x. fintro Htx. fintro Hxe. unfold raw_singleton in He.
    pose proof (CE2 He) as Hprofile. finst Hprofile x. fmp Hprofile Hxe.
    unfold raw_empty in Hempty. finst Hempty t. apply (IE Hempty). fmemE.
Qed.

Definition domain_selector : form := $1 ∈' $0.
Lemma domain_selector_bounded : fb 2 domain_selector.
Proof. cbn. lia. Qed.

Definition envelope_profile (t a b : term) : form :=
  ∀ ($0 ∈' b`[↑] ↔ ($0 ≡' a`[↑] ∨ ($0 ∈' a`[↑] ∧ t`[↑] ∈' $0))).

Lemma envelope_profile_subst t a b sg :
  (envelope_profile t a b)[sg] = envelope_profile t`[sg] a`[sg] b`[sg].
Proof. psubst envelope_profile. Qed.
#[global] Hint Rewrite envelope_profile_subst : fsub.
#[global] Arguments envelope_profile : simpl never.

Lemma domain_envelope_exists G (HB : incl KBase G) t a :
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  G ⊢C ∃ envelope_profile t`[↑] a`[↑] $0.
Proof.
  intros Hin. pose proof (KBase_eq _ HB) as HE.
  assert (Hs : In (forall_times 1 (kp0 singleton_matrix)) G).
  { apply HB. unfold KBase. apply in_or_app. right. cbn. tauto. }
  pose proof (kp0_augmented_separation G HE 1 domain_selector (t .: var) a
    domain_selector_bounded Hs Hin) as H.
  unfold domain_selector in H. simp_in H.
  unfold envelope_profile. kconv H.
Qed.

Lemma domain_envelope_facts G (HE : incl EqAx G) t a b :
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C envelope_profile t a b ->
  G ⊢C (a ∈' b ∧ ∀ ($0 ∈' b`[↑] → t`[↑] ∈' $0)) ∧
       ((¬ (t ∈' b)) ∧ (¬ (b ≡' t))).
Proof.
  intros Hempty Hta Hprofile.
  fassert Hab : (a ∈' b).
  { pose proof Hprofile as H. unfold envelope_profile in H. finst H a.
    apply (iff_r _ _ _ H). fleft. feqE. }
  fassert HallD : (∀ ($0 ∈' b`[↑] → t`[↑] ∈' $0)).
  { fall x. fintro Hxb. pose proof Hprofile as H. unfold envelope_profile in H. finst H x.
    pose proof (iff_l _ _ _ H Hxb) as Hcases. fcases Hcases Hxa Hselected.
    - fmemE.
    - exact (CE2 Hselected). }
  fsplit.
  - fsplit; assumption.
  - fsplit.
    + fintro Htb. pose proof HallD as H. finst H t. fmp H Htb.
      unfold raw_empty in Hempty. finst Hempty t. exact (IE Hempty H).
    + fintro E. unfold raw_empty in Hempty. finst Hempty a.
      apply (IE Hempty). fmemE.
Qed.
