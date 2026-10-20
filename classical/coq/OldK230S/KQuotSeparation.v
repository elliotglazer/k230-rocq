(** Separation for every formula translated into the tagged quotient. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0 KP0Use KBase KMarkers KDomain KPSeparation KTagged KDSeparation KQuot KQuotFormula KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** Selected object 0, marker 1, then phi's parameters. *)
Definition quotient_predicate (phi : form) : form :=
  qtrans $1 phi[$0 .: (fun k => $(2 + k))].

Lemma quotient_predicate_bounded n phi : fb (S n) phi ->
  fb (S (S n)) (quotient_predicate phi).
Proof.
  intros H. unfold quotient_predicate. apply qtrans_bounded; [|cbn; lia].
  eapply fb_subst; [exact H|]. intros [|k] Hk; cbn; lia.
Qed.

Definition qseparation (t a c : term) (phi : form) (sg : nat -> term) : form :=
  t ∈' c ∧ ∀ (t`[↑] ∈' $0 →
    (dmem t`[↑] $0 c`[↑] ↔
      (dmem t`[↑] $0 a`[↑] ∧ qtrans t`[↑] phi[$0 .: (fun k => (sg k)`[↑])]))).

Lemma qseparation_exists G (HL : incl KLogic G) n phi (sg : nat -> term) t a :
  fb (S n) phi ->
  In (forall_times 3 (kp0 (separation_matrix domain_selector))) G ->
  In (forall_times (S (S (S (S (S (S n))))))
    (kp0 (tagged_matrix (domain_cut (quotient_predicate phi))))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a ->
  G ⊢C ∃ qseparation t`[↑] a`[↑] $0 phi (fun k => (sg k)`[↑]).
Proof.
  intros Hfb Henv Hinst Hempty Hta.
  pose proof (domain_separation _ (KLogic_base _ HL) (S n) (quotient_predicate phi)
    (t .: sg) t a (quotient_predicate_bounded n phi Hfb) Henv Hinst Hempty Hta) as T.
  fex T c HC. fdestr HC Htc Hmembers.
  unfold quotient_predicate in Hmembers. simp_in Hmembers.
  fexists c. unfold qseparation. fsplit; [exact Htc|]. fall z. fintro Htz. fsplit.
  - fintro Hzc. unfold dmem in Hzc. fex Hzc w HW. fdestr HW Hw Hzw.
    unfold dchild in Hw. fdestr Hw Htw Hwc.
    pose proof Hmembers as H. finst H w. fmp H Htw.
    pose proof (iff_l _ _ _ H Hwc) as Hselected. fdestr Hselected Hwa Hphi.
    fassert Hphiw : (qtrans t phi[w .: sg]). { kconv Hphi. }
    pose proof (KLogic_sym _ HL t z w Hempty Hzw) as Hwz.
    pose proof (qtrans_unary_inv _ HL t phi sg w z Hempty Hwz Hphiw) as Hphiz.
    fsplit.
    + unfold dmem. fexists w. fsplit; [unfold dchild; fsplit; assumption|exact Hzw].
    + kconv Hphiz.
  - fintro Hselected. fdestr Hselected Hza Hphi.
    fassert Hphiz : (qtrans t phi[z .: sg]). { kconv Hphi. }
    unfold dmem in Hza. fex Hza w HW. fdestr HW Hw Hzw.
    unfold dchild in Hw. fdestr Hw Htw Hwa.
    pose proof (qtrans_unary_inv _ HL t phi sg z w Hempty Hzw Hphiz) as Hphiw.
    fassert Hwc : (w ∈' c).
    { pose proof Hmembers as H. finst H w. fmp H Htw.
      apply (iff_r _ _ _ H). fsplit; [exact Hwa|]. kconv Hphiw. }
    unfold dmem. fexists w. fsplit; [unfold dchild; fsplit; assumption|exact Hzw].
Qed.

Definition qseparation_statement (phi : form) : form :=
  ∀ ∀ (raw_empty $0 → $0 ∈' $1 →
    ∃ qseparation $1 $2 $0 phi (fun k => $(3 + k))).

Theorem K0_proves_qseparation n phi : fb (S n) phi ->
  K0 ⊢TC forall_times n (qseparation_statement phi).
Proof.
  intros Hfb.
  set (ei := forall_times 3 (kp0 (separation_matrix domain_selector))).
  set (si := forall_times (S (S (S (S (S (S n))))))
    (kp0 (tagged_matrix (domain_cut (quotient_predicate phi))))).
  set (B0 := KLogic ++ [ei; si]).
  assert (HL : incl KLogic B0) by (intros b Hb; apply in_or_app; now left).
  assert (HEI : In ei B0) by (apply in_or_app; right; now left).
  assert (HSI : In si B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KLogic_ok, Hb.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, domain_selector_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded,
        quotient_predicate_bounded, Hfb.
  - apply ft_intro. intros sg. unfold qseparation_statement. cbn.
    fall a. fall t.
    match goal with |- ?G ⊢C _ =>
      assert (HL' : incl KLogic G) by exact HL;
      assert (HEI' : In ei G) by exact HEI;
      assert (HSI' : In si G) by exact HSI
    end.
    fintro Hempty. fintro Hta.
    pose proof (qseparation_exists _ HL' n phi sg t a Hfb HEI' HSI' Hempty Hta) as T.
    unfold qseparation in T |- *. cbn. kconv T.
Qed.

Corollary KPrimeOrd_proves_qseparation n phi : fb (S n) phi ->
  KPrimeOrd ⊢TC forall_times n (qseparation_statement phi).
Proof. intros H. apply K0_derivation_to_KPrimeOrd, K0_proves_qseparation, H. Qed.
