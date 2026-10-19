(** Extensionality of the bisimulation quotient, from supported Collection. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From K230S Require Import KP0 KP0Use KBase KMarkers KPSeparation KDomain KCollection KTagged KRelation KQuot KQuotSym KQuotCollect KQuotUnion KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition same_dmembers (t x y : term) : form :=
  ∀ (t`[↑] ∈' $0 → (dmem t`[↑] $0 x`[↑] ↔ dmem t`[↑] $0 y`[↑])).
#[global] Arguments same_dmembers : simpl never.
Lemma same_dmembers_subst t x y sg :
  (same_dmembers t x y)[sg] = same_dmembers t`[sg] x`[sg] y`[sg].
Proof. psubst same_dmembers. Qed.
#[global] Hint Rewrite same_dmembers_subst : fsub.

Lemma deqv_ext G (HB : incl KBase G) t x y :
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))) G ->
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))) G ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_forward))) G ->
  In (forall_times 6 (kp0 (collection_matrix bisim_backward))) G ->
  In (forall_times 9 (kp0 (tagged_matrix (relation_selector rooted_union)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' x -> G ⊢C t ∈' y ->
  G ⊢C same_dmembers t x y -> G ⊢C deqv t x y.
Proof.
  intros Hdiag Hsym Henv Hforward Hbackward Hunion Hempty Htx Hty Hext.
  fassert HF : (forth_match t x y).
  { unfold forth_match. fall a. fintro Ha.
    pose proof Ha as Hac. unfold dchild in Hac. pose proof (CE1 Hac) as Hta.
    pose proof (deqv_refl _ HB t a Hdiag Hempty Hta) as Hself.
    fassert Hax : (dmem t a x).
    { unfold dmem. fexists a. fsplit; assumption. }
    pose proof Hext as E. unfold same_dmembers in E. finst E a. fmp E Hta.
    exact (iff_l _ _ _ E Hax). }
  fassert HBmatch : (back_match t x y).
  { unfold back_match. fall b. fintro Hb.
    pose proof Hb as Hbc. unfold dchild in Hbc. pose proof (CE1 Hbc) as Htb.
    pose proof (deqv_refl _ HB t b Hdiag Hempty Htb) as Hself.
    fassert Hby : (dmem t b y).
    { unfold dmem. fexists b. fsplit; assumption. }
    pose proof Hext as E. unfold same_dmembers in E. finst E b. fmp E Htb.
    pose proof (iff_r _ _ _ E Hby) as Hbx. unfold dmem in Hbx.
    fex Hbx a HA. fdestr HA Ha Hba. fexists a. fsplit; [exact Ha|].
    exact (deqv_sym _ HB t b a Hsym Hempty Hba). }
  pose proof (collect_forth_bisim _ HB t x y Henv Hforward Hempty Htx HF) as F.
  fex F cf HCF. fdestr HCF HFcover HFfamily.
  pose proof (collect_back_bisim _ HB t x y Henv Hbackward Hempty Hty HBmatch) as B.
  fex B cb HCB. fdestr HCB HBcover HBfamily.
  exact (bisim_union_with_root _ HB t x y cf cb Hunion Hempty Htx Hty
    HFcover HBcover HFfamily HBfamily).
Qed.

Definition deqv_ext_statement : form :=
  ∀ ∀ ∀ (raw_empty $2 → $2 ∈' $1 → $2 ∈' $0 →
    same_dmembers $2 $1 $0 → deqv $2 $1 $0).

Theorem K0_proves_deqv_ext : K0 ⊢TC deqv_ext_statement.
Proof.
  set (di := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))).
  set (si := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))).
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (fi := forall_times 6 (kp0 (collection_matrix bisim_forward))).
  set (bi := forall_times 6 (kp0 (collection_matrix bisim_backward))).
  set (ui := forall_times 9 (kp0 (tagged_matrix (relation_selector rooted_union)))).
  set (B0 := KBase ++ [di; si; ei; fi; bi; ui]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HDI : In di B0) by (apply in_or_app; right; cbn; tauto).
  assert (HSI : In si B0) by (apply in_or_app; right; cbn; tauto).
  assert (HEI : In ei B0) by (apply in_or_app; right; cbn; tauto).
  assert (HFI : In fi B0) by (apply in_or_app; right; cbn; tauto).
  assert (HBI : In bi B0) by (apply in_or_app; right; cbn; tauto).
  assert (HUI : In ui B0) by (apply in_or_app; right; cbn; tauto).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_diagonal_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_reverse_bounded.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, collection_matrix_bounded, bisim_forward_bounded.
    + apply K0_instance, kp0_closed, collection_matrix_bounded, bisim_backward_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact rooted_union_bounded.
  - unfold deqv_ext_statement. fall t. fall x. fall y.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HDI' : In di G) by exact HDI;
      assert (HSI' : In si G) by exact HSI;
      assert (HEI' : In ei G) by exact HEI;
      assert (HFI' : In fi G) by exact HFI;
      assert (HBI' : In bi G) by exact HBI;
      assert (HUI' : In ui G) by exact HUI
    end.
    fintro Hempty. fintro Htx. fintro Hty. fintro Hext.
    exact (deqv_ext _ HB' t x y HDI' HSI' HEI' HFI' HBI' HUI' Hempty Htx Hty Hext).
Qed.

Corollary KPrimeOrd_proves_deqv_ext : KPrimeOrd ⊢TC deqv_ext_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_deqv_ext. Qed.
