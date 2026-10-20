(** Union first in the tagged domain, then with quotient membership. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KDomain KTagged KPSeparation KDSeparation KRelation KQuot KQuotSym KQuotTrans KQuotMem KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** Selected member z at 0, parameters t and a at 1/2. *)
Definition domain_union_selector : form := ∃ (dchild $2 $0 $3 ∧ $1 ∈' $0).
Lemma domain_union_selector_bounded : fb 3 domain_union_selector.
Proof. unfold domain_union_selector, dchild. cbn. lia. Qed.

Definition domain_union (t a u : term) : form :=
  t ∈' u ∧ ∀ (t`[↑] ∈' $0 →
    ($0 ∈' u`[↑] ↔ ∃ (dchild t`[↑]`[↑] $0 a`[↑]`[↑] ∧ $1 ∈' $0))).
#[global] Arguments domain_union : simpl never.
Lemma domain_union_subst t a u sg :
  (domain_union t a u)[sg] = domain_union t`[sg] a`[sg] u`[sg].
Proof. psubst domain_union. Qed.
#[global] Hint Rewrite domain_union_subst : fsub.

Lemma domain_union_exists G (HB : incl KBase G) t a :
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times 7 (kp0 (tagged_matrix (domain_cut domain_union_selector)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C ∃ domain_union t`[↑] a`[↑] $0.
Proof.
  intros Henv Hinst Hempty Hta.
  fobtain (KBase_transitive _ HB a) as v HV. fdestr HV HaV Htrans.
  pose proof (raw_transitive_element _ v a t Htrans HaV Hta) as Htv.
  pose proof (domain_separation _ HB 2 domain_union_selector (t .: a .: var) t v
    domain_union_selector_bounded Henv Hinst Hempty Htv) as T.
  fex T u HU. unfold domain_union_selector in HU. simp_in HU.
  fdestr HU Htu Hmembers. fexists u. unfold domain_union. fsplit; [exact Htu|].
  fall z. fintro Htz. pose proof Hmembers as H. finst H z. fmp H Htz. fsplit.
  - fintro Hzu. exact (CE2 (iff_l _ _ _ H Hzu)).
  - fintro Hex. fex Hex b HBb. fdestr HBb Hb Hzb.
    pose proof Hb as Hba. unfold dchild in Hba. pose proof (CE2 Hba) as Hba'.
    pose proof (raw_transitive_element _ v a b Htrans HaV Hba') as HbV.
    apply (iff_r _ _ _ H). fsplit.
    + exact (raw_transitive_element _ v b z Htrans HbV Hzb).
    + fexists b. fsplit; assumption.
Qed.

Definition qunion (t a u : term) : form :=
  t ∈' u ∧ ∀ (t`[↑] ∈' $0 →
    (dmem t`[↑] $0 u`[↑] ↔
      ∃ (t`[↑]`[↑] ∈' $0 ∧ (dmem t`[↑]`[↑] $0 a`[↑]`[↑] ∧ dmem t`[↑]`[↑] $1 $0)))).
#[global] Arguments qunion : simpl never.
Lemma qunion_subst t a u sg : (qunion t a u)[sg] = qunion t`[sg] a`[sg] u`[sg].
Proof. psubst qunion. Qed.
#[global] Hint Rewrite qunion_subst : fsub.

Lemma domain_union_qunion G (HB : incl KBase G) t a u :
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))) G ->
  In (forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))) G ->
  G ⊢C raw_empty t -> G ⊢C domain_union t a u -> G ⊢C qunion t a u.
Proof.
  intros Hdiag Hcomp Hempty HU. unfold domain_union in HU. fdestr HU Htu Hmembers.
  unfold qunion. fsplit; [exact Htu|]. fall z. fintro Htz. fsplit.
  - fintro Hzu. unfold dmem in Hzu. fex Hzu w HW. fdestr HW Hw Hzw.
    pose proof Hw as Hw'. unfold dchild in Hw'. fdestr Hw' Htw Hwu.
    pose proof Hmembers as H. finst H w. fmp H Htw.
    pose proof (iff_l _ _ _ H Hwu) as Hex. fex Hex b HBb. fdestr HBb Hb Hwb.
    pose proof Hb as Hb'. unfold dchild in Hb'. pose proof (CE1 Hb') as Htb.
    fexists b. fsplit; [exact Htb|]. fsplit.
    + unfold dmem. fexists b. fsplit; [exact Hb|].
      exact (deqv_refl _ HB t b Hdiag Hempty Htb).
    + unfold dmem. fexists w. fsplit; [unfold dchild; fsplit; assumption|exact Hzw].
  - fintro Hex. fex Hex b HBb. fdestr HBb Htb Hbm. fdestr Hbm Hba Hzb.
    unfold dmem in Hba. fex Hba c HC. fdestr HC Hc Hbc.
    pose proof (dmem_right _ HB t z b c Hcomp Hempty Hbc Hzb) as Hzc.
    unfold dmem in Hzc. fex Hzc w HW. fdestr HW Hw Hzw.
    pose proof Hw as Hw'. unfold dchild in Hw'. fdestr Hw' Htw Hwc.
    fassert Hwu : (w ∈' u).
    { pose proof Hmembers as H. finst H w. fmp H Htw. apply (iff_r _ _ _ H).
      fexists c. fsplit; assumption. }
    unfold dmem. fexists w. fsplit; [unfold dchild; fsplit; assumption|exact Hzw].
Qed.

Definition qunion_statement : form := ∀ ∀ (raw_empty $1 → $1 ∈' $0 → ∃ qunion $2 $1 $0).
Theorem K0_proves_qunion : K0 ⊢TC qunion_statement.
Proof.
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (ui := forall_times 7 (kp0 (tagged_matrix (domain_cut domain_union_selector)))).
  set (di := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))).
  set (ci := forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))).
  set (B0 := KBase ++ [ei; ui; di; ci]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; cbn; tauto).
  assert (HUI : In ui B0) by (apply in_or_app; right; cbn; tauto).
  assert (HDI : In di B0) by (apply in_or_app; right; cbn; tauto).
  assert (HCI : In ci B0) by (apply in_or_app; right; cbn; tauto).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[<-|[<-|[]]]]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded, domain_union_selector_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, domain_diagonal_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, domain_composition_bounded.
  - unfold qunion_statement. fall t. fall a.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HEI' : In ei G) by exact HEI;
      assert (HUI' : In ui G) by exact HUI;
      assert (HDI' : In di G) by exact HDI;
      assert (HCI' : In ci G) by exact HCI
    end.
    fintro Hempty. fintro Hta.
    fobtain (domain_union_exists _ HB' t a HEI' HUI' Hempty Hta) as u HU.
    fexists u. exact (domain_union_qunion _ HB' t a u HDI' HCI' Hempty HU).
Qed.

Corollary KPrimeOrd_proves_qunion : KPrimeOrd ⊢TC qunion_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_qunion. Qed.
