(** Reversal of coded bisimulations in the tagged domain. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From M254S Require Import S_raw.
From K230S Require Import KP0 KP0Use KPRaw KPTransitive KBase KMarkers KTagged KRelation KQuot KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma raw_app_endpoints G v r x y :
  G ⊢C raw_transitive v -> G ⊢C r ∈' v -> G ⊢C App0 r x y ->
  G ⊢C x ∈' v ∧ y ∈' v.
Proof.
  intros Htrans Hr Hxy. unfold App0 in Hxy. fex Hxy c HC. fdestr HC Hcr Hop.
  pose proof (raw_transitive_element _ v r c Htrans Hr Hcr) as HcV.
  unfold OP0 in Hop. fdestr Hop H12 H3. fdestr H12 H1 H2. fsplit.
  - fex H1 s HS. fdestr HS Hsc Hs. unfold Sing0 in Hs.
    pose proof (raw_transitive_element _ v c s Htrans HcV Hsc) as HsV.
    exact (raw_transitive_element _ v s x Htrans HsV (CE1 Hs)).
  - fex H2 d HD. fdestr HD Hdc Hd. unfold Pair0 in Hd.
    pose proof (raw_transitive_element _ v c d Htrans HcV Hdc) as HdV.
    exact (raw_transitive_element _ v d y Htrans HdV (CE2 (CE1 Hd))).
Qed.

Lemma dbisim_types G t r p q : G ⊢C dbisim t r -> G ⊢C App0 r p q ->
  G ⊢C t ∈' p ∧ t ∈' q.
Proof.
  intros H Hpq. unfold dbisim in H. pose proof (CE2 H) as T.
  finst T p q. fmp T Hpq. exact (CE1 T).
Qed.

Lemma dbisim_forth G t r p q a : G ⊢C dbisim t r -> G ⊢C App0 r p q ->
  G ⊢C dchild t a p -> G ⊢C ∃ (dchild t`[↑] $0 q`[↑] ∧ App0 r`[↑] a`[↑] $0).
Proof.
  intros H Hpq Ha. unfold dbisim in H. pose proof (CE2 H) as T.
  finst T p q. fmp T Hpq. pose proof (CE1 (CE2 T)) as F.
  finst F a. exact (IE F Ha).
Qed.

Lemma dbisim_back G t r p q b : G ⊢C dbisim t r -> G ⊢C App0 r p q ->
  G ⊢C dchild t b q -> G ⊢C ∃ (dchild t`[↑] $0 p`[↑] ∧ App0 r`[↑] $0 b`[↑]).
Proof.
  intros H Hpq Hb. unfold dbisim in H. pose proof (CE2 H) as T.
  finst T p q. fmp T Hpq. pose proof (CE2 (CE2 T)) as B.
  finst B b. exact (IE B Hb).
Qed.

Lemma deqv_typed G t x y : G ⊢C deqv t x y -> G ⊢C t ∈' x ∧ t ∈' y.
Proof.
  intros H. unfold deqv in H. fex H r HR. fdestr HR Hbis Hxy.
  exact (dbisim_types _ t r x y Hbis Hxy).
Qed.

Definition domain_reverse : form := App0 $2 $1 $0.
Lemma domain_reverse_bounded : fb 3 domain_reverse.
Proof. unfold domain_reverse, App0, OP0, Sing0, Pair0. cbn. lia. Qed.

Lemma deqv_sym G (HB : incl KBase G) t x y :
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))) G ->
  G ⊢C raw_empty t -> G ⊢C deqv t x y -> G ⊢C deqv t y x.
Proof.
  intros Hinst Hempty Hxy. pose proof (KBase_eq _ HB) as HE.
  unfold deqv in Hxy. fex Hxy r HR. fdestr HR Hbis Hxy.
  fobtain (KBase_transitive _ HB r) as v HV. fdestr HV HrV Htrans.
  pose proof (KBase_bounded_relation _ HB 1 domain_reverse (r .: var) t v
    domain_reverse_bounded Hinst Hempty) as T.
  fex T s HS. unfold relation_profile in HS. fdestr HS Hts Hedges.
  unfold domain_reverse in Hedges. simp_in Hedges.
  fassert Hrev : (∀ ∀ (App0 r`[↑]`[↑] $1 $0 → App0 s`[↑]`[↑] $0 $1)).
  { fall p. fall q. fintro Hpq.
    pose proof (raw_app_endpoints _ v r p q Htrans HrV Hpq) as HPQ.
    pose proof Hedges as H. finst H q p. apply (iff_r _ _ _ H).
    fsplit; [fsplit; [exact (CE2 HPQ)|exact (CE1 HPQ)]|exact Hpq]. }
  fassert Hback : (∀ ∀ (App0 s`[↑]`[↑] $1 $0 → App0 r`[↑]`[↑] $0 $1)).
  { fall p. fall q. fintro Hpq. pose proof Hedges as H. finst H p q.
    exact (CE2 (iff_l _ _ _ H Hpq)). }
  unfold deqv. fexists s. fsplit.
  - unfold dbisim. fsplit; [exact Hts|]. fall p. fall q. fintro Hpq.
    pose proof Hback as H. finst H p q. fmp H Hpq.
    pose proof (dbisim_types _ t r q p Hbis H) as Htypes.
    fsplit; [fsplit; [exact (CE2 Htypes)|exact (CE1 Htypes)]|]. fsplit.
    + fall a. fintro Ha.
      pose proof (dbisim_back _ t r q p a Hbis H Ha) as B.
      fex B b HBb. fdestr HBb Hb Hba. fexists b. fsplit; [exact Hb|].
      pose proof Hrev as Hturn. finst Hturn b a. exact (IE Hturn Hba).
    + fall b. fintro Hb.
      pose proof (dbisim_forth _ t r q p b Hbis H Hb) as F.
      fex F a HFa. fdestr HFa Ha Hba. fexists a. fsplit; [exact Ha|].
      pose proof Hrev as Hturn. finst Hturn b a. exact (IE Hturn Hba).
  - finst Hrev x y. exact (IE Hrev Hxy).
Qed.

Definition deqv_sym_statement : form :=
  ∀ ∀ ∀ (raw_empty $2 → deqv $2 $1 $0 → deqv $2 $0 $1).

Theorem K0_proves_deqv_sym : K0 ⊢TC deqv_sym_statement.
Proof.
  set (ri := forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))).
  set (B0 := KBase ++ [ri]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_reverse_bounded.
  - unfold deqv_sym_statement. fall t. fall x. fall y.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty. fintro Hxy. exact (deqv_sym _ HB' t x y HRI' Hempty Hxy).
Qed.

Corollary KPrimeOrd_proves_deqv_sym : KPrimeOrd ⊢TC deqv_sym_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_deqv_sym. Qed.
