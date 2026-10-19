(** Power Set in the quotient, using uniformly bounded representatives. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From K230S Require Import KP0 KP0Use KPRaw KPTransitive KBase KMarkers KDomain KTagged KDSeparation KQuot KQuotSym KQuotMem KQuotExt KQuotFormula KQuotContext KQuotPowerBound KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition qsubset (t x a : term) : form :=
  ∀ (t`[↑] ∈' $0 → (dmem t`[↑] $0 x`[↑] → dmem t`[↑] $0 a`[↑])).
#[global] Arguments qsubset : simpl never.
Lemma qsubset_subst t x a sg : (qsubset t x a)[sg] = qsubset t`[sg] x`[sg] a`[sg].
Proof. psubst qsubset. Qed.
#[global] Hint Rewrite qsubset_subst : fsub.

Lemma qsubset_left G (HL : incl KLogic G) t x x' a :
  G ⊢C raw_empty t -> G ⊢C deqv t x x' -> G ⊢C qsubset t x a -> G ⊢C qsubset t x' a.
Proof.
  intros Hempty Hxx' Hsub. unfold qsubset in Hsub |- *.
  fall z. fintro Htz. fintro Hzx'.
  pose proof (KLogic_sym _ HL t x x' Hempty Hxx') as Hx'x.
  pose proof (dmem_right _ (KLogic_base _ HL) t z x' x
    (KLogic_compose _ HL) Hempty Hx'x Hzx') as Hzx.
  finst Hsub z. fmp Hsub Htz. exact (IE Hsub Hzx).
Qed.

Definition member_predicate : form := dmem $1 $0 $2.
Definition subset_predicate : form := qsubset $1 $0 $2.
Lemma member_predicate_bounded : fb 3 member_predicate.
Proof. unfold member_predicate. apply fb_dmem; cbn; lia. Qed.
Lemma subset_predicate_bounded : fb 3 subset_predicate.
Proof. unfold subset_predicate, qsubset, dmem, deqv, dbisim, dchild, App0, OP0, Sing0, Pair0. cbn. lia. Qed.

Lemma bounded_subset_representative G (HK : incl KExt G) t a b v y :
  In (forall_times 7 (kp0 (tagged_matrix (domain_cut member_predicate)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C t ∈' y ->
  G ⊢C envelope_profile t a b -> G ⊢C raw_transitive v ->
  G ⊢C b ∈' v -> G ⊢C t ∈' v -> G ⊢C qsubset t y a ->
  G ⊢C ∃ (raw_subset $0 v`[↑] ∧ (t`[↑] ∈' $0 ∧ deqv t`[↑] y`[↑] $0)).
Proof.
  intros Hinst Hempty Hta Hty HP Htrans HbV HtV Hsub.
  pose proof (KExt_logic _ HK) as HL.
  pose proof (bounded_domain_separation _ (KExt_base _ HK) 2 member_predicate (t .: y .: var)
    t a b v member_predicate_bounded Hinst Hempty Hta HP Htrans HbV HtV) as T.
  fex T c HC. fdestr HC HcV Hrest. fdestr Hrest Htc Hmembers.
  unfold member_predicate in Hmembers. simp_in Hmembers.
  fexists c. fsplit; [exact HcV|]. fsplit; [exact Htc|].
  apply (KExt_ext _ HK t y c Hempty Hty Htc).
  unfold same_dmembers. fall z. fintro Htz. fsplit.
  - fintro Hzy.
    pose proof Hsub as HS. unfold qsubset in HS. finst HS z. fmp HS Htz. fmp HS Hzy.
    unfold dmem in HS. fex HS w HW. fdestr HW Hw Hzw.
    unfold dchild in Hw. fdestr Hw Htw Hwa.
    pose proof (dmem_left _ (KLogic_base _ HL) t z w y
      (KLogic_reverse _ HL) (KLogic_compose _ HL) Hempty Hzw Hzy) as Hwy.
    fassert Hwc : (w ∈' c).
    { pose proof Hmembers as H. finst H w. fmp H Htw.
      apply (iff_r _ _ _ H). fsplit; [exact Hwa|exact Hwy]. }
    unfold dmem. fexists w. fsplit; [unfold dchild; fsplit; assumption|exact Hzw].
  - fintro Hzc. unfold dmem in Hzc. fex Hzc w HW. fdestr HW Hw Hzw.
    unfold dchild in Hw. fdestr Hw Htw Hwc.
    pose proof Hmembers as H. finst H w. fmp H Htw.
    pose proof (CE2 (iff_l _ _ _ H Hwc)) as Hwy.
    pose proof (KLogic_sym _ HL t z w Hempty Hzw) as Hwz.
    exact (dmem_left _ (KLogic_base _ HL) t w z y
      (KLogic_reverse _ HL) (KLogic_compose _ HL) Hempty Hwz Hwy).
Qed.

Definition qpower (t a p : term) : form :=
  t ∈' p ∧ ∀ (t`[↑] ∈' $0 → (dmem t`[↑] $0 p`[↑] ↔ qsubset t`[↑] $0 a`[↑])).
#[global] Arguments qpower : simpl never.
Lemma qpower_subst t a p sg : (qpower t a p)[sg] = qpower t`[sg] a`[sg] p`[sg].
Proof. psubst qpower. Qed.
#[global] Hint Rewrite qpower_subst : fsub.

Lemma qpower_exists G (HK : incl KExt G) t a :
  In (forall_times 7 (kp0 (tagged_matrix (domain_cut member_predicate)))) G ->
  In (forall_times 7 (kp0 (tagged_matrix (domain_cut subset_predicate)))) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C ∃ qpower t`[↑] a`[↑] $0.
Proof.
  intros Hmember Hsubset Hempty Hta.
  pose proof (KExt_base _ HK) as HB. pose proof (KExt_logic _ HK) as HL.
  pose proof (fixed_separation_bound _ HB t a (KExt_envelope _ HK) Hempty Hta) as T.
  fex T b HBnd. fdestr HBnd HP Hex. fex Hex v HV.
  fdestr HV Htrans Hmem. fdestr Hmem HbV HtV.
  fobtain (KBase_power _ HB v) as p Hpower.
  fassert Htp : (t ∈' p).
  { pose proof Hpower as H. finst H t. apply (iff_r _ _ _ H).
    unfold raw_subset, raw_empty in *. fall z. fintro Hzt.
    finst Hempty z. fabsurd. exact (IE Hempty Hzt). }
  pose proof (domain_separation _ HB 2 subset_predicate (t .: a .: var) t p
    subset_predicate_bounded (KExt_envelope _ HK) Hsubset Hempty Htp) as T.
  fex T q HQ. fdestr HQ Htq Hmembers. unfold subset_predicate in Hmembers. simp_in Hmembers.
  fexists q. unfold qpower. fsplit; [exact Htq|]. fall y. fintro Hty. fsplit.
  - fintro Hyq. unfold dmem in Hyq. fex Hyq c HC. fdestr HC Hc Hyc.
    unfold dchild in Hc. fdestr Hc Htc Hcq.
    pose proof Hmembers as H. finst H c. fmp H Htc.
    pose proof (CE2 (iff_l _ _ _ H Hcq)) as Hcsub.
    pose proof (KLogic_sym _ HL t y c Hempty Hyc) as Hcy.
    exact (qsubset_left _ HL t c y a Hempty Hcy Hcsub).
  - fintro Hysub.
    pose proof (bounded_subset_representative _ HK t a b v y Hmember Hempty Hta Hty
      HP Htrans HbV HtV Hysub) as R.
    fex R c HC. fdestr HC HcV Hrest. fdestr Hrest Htc Hyc.
    fassert Hcp : (c ∈' p).
    { pose proof Hpower as H. finst H c. exact (iff_r _ _ _ H HcV). }
    pose proof (qsubset_left _ HL t y c a Hempty Hyc Hysub) as Hcsub.
    fassert Hcq : (c ∈' q).
    { pose proof Hmembers as H. finst H c. fmp H Htc.
      apply (iff_r _ _ _ H). fsplit; assumption. }
    unfold dmem. fexists c. fsplit; [unfold dchild; fsplit; assumption|exact Hyc].
Qed.

Definition qpower_statement : form := ∀ ∀ (raw_empty $1 → $1 ∈' $0 → ∃ qpower $2 $1 $0).
Theorem K0_proves_qpower : K0 ⊢TC qpower_statement.
Proof.
  set (mi := forall_times 7 (kp0 (tagged_matrix (domain_cut member_predicate)))).
  set (pi := forall_times 7 (kp0 (tagged_matrix (domain_cut subset_predicate)))).
  set (B0 := KExt ++ [mi; pi]).
  assert (HK : incl KExt B0) by (intros b Hb; apply in_or_app; now left).
  assert (HMI : In mi B0) by (apply in_or_app; right; now left).
  assert (HPI : In pi B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KExt_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded, member_predicate_bounded.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, domain_cut_bounded, subset_predicate_bounded.
  - unfold qpower_statement. fall t. fall a.
    match goal with |- ?G ⊢C _ =>
      assert (HK' : incl KExt G) by exact HK;
      assert (HMI' : In mi G) by exact HMI;
      assert (HPI' : In pi G) by exact HPI
    end.
    fintro Hempty. fintro Hta. exact (qpower_exists _ HK' t a HMI' HPI' Hempty Hta).
Qed.

Corollary KPrimeOrd_proves_qpower : KPrimeOrd ⊢TC qpower_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_qpower. Qed.
