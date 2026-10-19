(** Singleton-closed sets and the translated Zermelo Infinity axiom. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KBase KMarkers KTagged KDPair KQuot KQuotBasic KQuotFormula KSingletonClosure KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition qsingleton (t x s : term) : form :=
  ∀ (t`[↑] ∈' $0 → (dmem t`[↑] $0 s`[↑] ↔ deqv t`[↑] $0 x`[↑])).
#[global] Arguments qsingleton : simpl never.
Lemma qsingleton_subst t x s sg :
  (qsingleton t x s)[sg] = qsingleton t`[sg] x`[sg] s`[sg].
Proof. psubst qsingleton. Qed.
#[global] Hint Rewrite qsingleton_subst : fsub.

Lemma domain_pair_qsingleton G (HL : incl KLogic G) t x p s :
  G ⊢C raw_empty t -> G ⊢C t ∈' p -> G ⊢C deqv t x p ->
  G ⊢C domain_pair t p p s -> G ⊢C qsingleton t x s.
Proof.
  intros Hempty Htp Hxp HP.
  pose proof (domain_pair_qpair _ (KBase_eq _ (KLogic_base _ HL)) t p p s Htp Htp HP) as HQ.
  unfold qpair in HQ. pose proof (CE2 HQ) as Hmembers.
  unfold qsingleton. fall z. fintro Htz.
  finst Hmembers z. fmp Hmembers Htz. fsplit.
  - fintro Hzs. pose proof (iff_l _ _ _ Hmembers Hzs) as E.
    fassert Hzp : (deqv t z p).
    { fcases E E1 E2; assumption. }
    pose proof (KLogic_sym _ HL t x p Hempty Hxp) as Hpx.
    exact (KLogic_trans _ HL t z p x Hempty Hzp Hpx).
  - fintro Hzx. apply (iff_r _ _ _ Hmembers). fleft.
    exact (KLogic_trans _ HL t z x p Hempty Hzx Hxp).
Qed.

Definition qinfinity (t a u : term) : form :=
  t ∈' u ∧ (dmem t a u ∧
    ∀ (t`[↑] ∈' $0 → dmem t`[↑] $0 u`[↑] →
      ∃ (t`[↑]`[↑] ∈' $0 ∧ (dmem t`[↑]`[↑] $0 u`[↑]`[↑] ∧ qsingleton t`[↑]`[↑] $1 $0)))).
#[global] Arguments qinfinity : simpl never.
Lemma qinfinity_subst t a u sg : (qinfinity t a u)[sg] = qinfinity t`[sg] a`[sg] u`[sg].
Proof. psubst qinfinity. Qed.
#[global] Hint Rewrite qinfinity_subst : fsub.

Lemma qinfinity_exists G (HL : incl KLogic G) t a :
  In (forall_times 3 (kp0 (tagged_matrix true_formula))) G ->
  In (forall_times 2 (kp0 singleton_closure_matrix)) G ->
  G ⊢C raw_empty t -> G ⊢C t ∈' a -> G ⊢C ∃ qinfinity t`[↑] a`[↑] $0.
Proof.
  intros Hpair Hclosure Hempty Hta. pose proof (KLogic_base _ HL) as HB.
  pose proof (KBase_eq _ HB) as HE.
  fobtain (singleton_closure_exists _ HB t a Hpair Hclosure Hempty Hta) as c HC.
  unfold singleton_closure_profile in HC. fdestr HC Hseed Hclosed. fdestr Hseed Hac Hall.
  fassert HnotC : (¬ (t ∈' c)).
  { fintro Htc. pose proof Hall as H. finst H t. fmp H Htc.
    unfold raw_empty in Hempty. finst Hempty t. exact (IE Hempty H). }
  fassert Hct : (¬ (c ≡' t)).
  { fintro Ect. unfold raw_empty in Hempty. finst Hempty a. apply (IE Hempty). fmemE. }
  pose proof (raw_tagged_comprehension _ HB 0 true_formula var c t ltac:(cbn; tauto)
    Hpair Hempty Hct) as T.
  fex T u HU. unfold true_formula in HU. simp_in HU.
  fassert Htu : (t ∈' u).
  { pose proof HU as H. finst H t. apply (iff_r _ _ _ H). fright. fleft. feqE. }
  fassert Hmembers : (∀ (t`[↑] ∈' $0 → ($0 ∈' u`[↑] ↔ $0 ∈' c`[↑]))).
  { fall z. fintro Htz. pose proof HU as H. finst H z. fsplit.
    - fintro Hzu. pose proof (iff_l _ _ _ H Hzu) as Hcases.
      fcases Hcases Hzc Hrest.
      + fabsurd. apply (IE HnotC). fmemE.
      + fcases Hrest Hzt Hselected.
        * unfold raw_empty in Hempty. finst Hempty t. fabsurd. apply (IE Hempty). fmemE.
        * exact (CE1 Hselected).
    - fintro Hzc. apply (iff_r _ _ _ H). fright. fright. fsplit; [exact Hzc|].
      fintro Hfalse. exact Hfalse. }
  fexists u. unfold qinfinity. fsplit; [exact Htu|]. fsplit.
  - fassert Hau : (a ∈' u).
    { pose proof Hmembers as H. finst H a. fmp H Hta. exact (iff_r _ _ _ H Hac). }
    unfold dmem. fexists a. fsplit; [unfold dchild; fsplit; assumption|].
    exact (KLogic_refl _ HL t a Hempty Hta).
  - fall x. fintro Htx. fintro Hxu. unfold dmem in Hxu.
    fex Hxu p HP. fdestr HP Hp Hxp. unfold dchild in Hp. fdestr Hp Htp Hpu.
    pose proof Hmembers as H. finst H p. fmp H Htp.
    pose proof (iff_l _ _ _ H Hpu) as Hpc.
    pose proof Hclosed as C. finst C p. fmp C Hpc.
    fex C s HS. fdestr HS Hsc Hpairps.
    pose proof Hpairps as Hs. unfold domain_pair in Hs. pose proof (CE1 Hs) as Hts.
    fassert Hsu : (s ∈' u).
    { pose proof Hmembers as M. finst M s. fmp M Hts. exact (iff_r _ _ _ M Hsc). }
    fexists s. fsplit; [exact Hts|]. fsplit.
    + unfold dmem. fexists s. fsplit; [unfold dchild; fsplit; assumption|].
      exact (KLogic_refl _ HL t s Hempty Hts).
    + exact (domain_pair_qsingleton _ HL t x p s Hempty Htp Hxp Hpairps).
Qed.

Definition qinfinity_statement : form :=
  ∀ ∀ (raw_empty $1 → $1 ∈' $0 → ∃ qinfinity $2 $1 $0).

Theorem K0_proves_qinfinity : K0 ⊢TC qinfinity_statement.
Proof.
  set (pi := forall_times 3 (kp0 (tagged_matrix true_formula))).
  set (ci := forall_times 2 (kp0 singleton_closure_matrix)).
  set (B0 := KLogic ++ [pi; ci]).
  assert (HL : incl KLogic B0) by (intros b Hb; apply in_or_app; now left).
  assert (HPI : In pi B0) by (apply in_or_app; right; now left).
  assert (HCI : In ci B0) by (apply in_or_app; right; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply KLogic_ok, Hb.
    + apply K0_instance, kp0_closed, (tagged_matrix_bounded 0). cbn. tauto.
    + apply K0_instance, kp0_closed, singleton_closure_matrix_bounded.
  - unfold qinfinity_statement. fall t. fall a.
    match goal with |- ?G ⊢C _ =>
      assert (HL' : incl KLogic G) by exact HL;
      assert (HPI' : In pi G) by exact HPI;
      assert (HCI' : In ci G) by exact HCI
    end.
    fintro Hempty. fintro Hta. exact (qinfinity_exists _ HL' t a HPI' HCI' Hempty Hta).
Qed.

Definition qtranslated_infinity : form := ∀ (raw_empty $0 → qtrans $0 INF_lib).
Theorem K0_proves_qtranslated_infinity : K0 ⊢TC qtranslated_infinity.
Proof.
  destruct K0_proves_qinfinity as [B [HB H]]. exists B. split; [exact HB|].
  unfold qinfinity_statement in H. unfold qtranslated_infinity.
  fall t. fintro Hempty. finst H t.
  cbn [qtrans INF_lib]. fall a. fintro Hta.
  finst H a. fmp H Hempty. fmp H Hta.
  unfold qinfinity, qsingleton in H. kconv H.
Qed.

Corollary KPrimeOrd_proves_qtranslated_infinity : KPrimeOrd ⊢TC qtranslated_infinity.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_qtranslated_infinity. Qed.
