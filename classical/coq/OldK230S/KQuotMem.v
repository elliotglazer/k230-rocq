(** Interpreted membership respects the bisimulation equality in both arguments. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldZFC Require Import Z_base.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KTagged KRelation KQuot KQuotSym KQuotTrans KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma dmem_left G (HB : incl KBase G) t x x' y :
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))) G ->
  In (forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))) G ->
  G ⊢C raw_empty t -> G ⊢C deqv t x x' -> G ⊢C dmem t x y -> G ⊢C dmem t x' y.
Proof.
  intros Hsym Htrans Hempty Hxx' Hxy.
  unfold dmem in Hxy. fex Hxy u HU. fdestr HU Hu Hxu.
  pose proof (deqv_sym _ HB t x x' Hsym Hempty Hxx') as Hx'x.
  unfold dmem. fexists u. fsplit; [exact Hu|].
  exact (deqv_trans _ HB t x' x u Htrans Hempty Hx'x Hxu).
Qed.

Lemma dmem_right G (HB : incl KBase G) t x y y' :
  In (forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))) G ->
  G ⊢C raw_empty t -> G ⊢C deqv t y y' -> G ⊢C dmem t x y -> G ⊢C dmem t x y'.
Proof.
  intros Htrans Hempty Hyy' Hxy.
  unfold dmem in Hxy. fex Hxy u HU. fdestr HU Hu Hxu.
  unfold deqv in Hyy'. fex Hyy' r HR. fdestr HR Hbis Hedge.
  pose proof (dbisim_forth _ t r y y' u Hbis Hedge Hu) as F.
  fex F v HV. fdestr HV Hv Huv.
  fassert Heq : (deqv t u v).
  { unfold deqv. fexists r. fsplit; assumption. }
  unfold dmem. fexists v. fsplit; [exact Hv|].
  exact (deqv_trans _ HB t x u v Htrans Hempty Hxu Heq).
Qed.

Definition dmem_congr_statement : form :=
  ∀ ∀ ∀ ∀ ∀ (raw_empty $4 → deqv $4 $3 $2 → deqv $4 $1 $0 →
    dmem $4 $3 $1 → dmem $4 $2 $0).

Theorem K0_proves_dmem_congr : K0 ⊢TC dmem_congr_statement.
Proof.
  set (si := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))).
  set (ci := forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))).
  set (B0 := KBase ++ [si; ci]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HSI : In si B0) by (apply in_or_app; right; now left).
  assert (HCI : In ci B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_reverse_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_composition_bounded.
  - unfold dmem_congr_statement. fall t. fall x. fall x'. fall y. fall y'.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HSI' : In si G) by exact HSI;
      assert (HCI' : In ci G) by exact HCI
    end.
    fintro Hempty. fintro Hxx'. fintro Hyy'. fintro Hxy.
    pose proof (dmem_left _ HB' t x x' y HSI' HCI' Hempty Hxx' Hxy) as Hx'y.
    exact (dmem_right _ HB' t x' y y' HCI' Hempty Hyy' Hx'y).
Qed.

Corollary KPrimeOrd_proves_dmem_congr : KPrimeOrd ⊢TC dmem_congr_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_dmem_congr. Qed.
