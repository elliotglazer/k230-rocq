(** Composition of coded bisimulations in the tagged domain. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldZFC Require Import Z_base.
From OldM254S Require Import S_raw.
From OldK230S Require Import KP0 KP0Use KPRaw KPPair KPTransitive KBase KMarkers KTagged KRelation KQuot KQuotSym KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** Endpoints are 0/1 and relation parameters are 2/3. *)
Definition domain_composition : form := ∃ (App0 $3 $1 $0 ∧ App0 $4 $0 $2).
Lemma domain_composition_bounded : fb 4 domain_composition.
Proof. unfold domain_composition, App0, OP0, Sing0, Pair0. cbn. lia. Qed.

Lemma deqv_trans G (HB : incl KBase G) t x y z :
  In (forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))) G ->
  G ⊢C raw_empty t -> G ⊢C deqv t x y -> G ⊢C deqv t y z -> G ⊢C deqv t x z.
Proof.
  intros Hinst Hempty Hxy Hyz. pose proof (KBase_eq _ HB) as HE.
  unfold deqv in Hxy, Hyz.
  fex Hxy r1 HR1. fdestr HR1 Hbis1 Hedge1.
  fex Hyz r2 HR2. fdestr HR2 Hbis2 Hedge2.
  fobtain (KBase_pair _ HB r1 r2) as p HP.
  fobtain (KBase_transitive _ HB p) as v HV. fdestr HV HpV Htrans.
  unfold raw_pair in HP. pose proof (CE1 (CE1 HP)) as Hr1p.
  pose proof (CE2 (CE1 HP)) as Hr2p.
  pose proof (raw_transitive_element _ v p r1 Htrans HpV Hr1p) as Hr1V.
  pose proof (raw_transitive_element _ v p r2 Htrans HpV Hr2p) as Hr2V.
  pose proof (KBase_bounded_relation _ HB 2 domain_composition (r1 .: r2 .: var) t v
    domain_composition_bounded Hinst Hempty) as T.
  fex T s HS. unfold relation_profile in HS. fdestr HS Hts Hedges.
  unfold domain_composition in Hedges. simp_in Hedges.
  fassert Hcomp : (∀ ∀ ∀ ((App0 r1`[↑]`[↑]`[↑] $2 $0 ∧ App0 r2`[↑]`[↑]`[↑] $0 $1) →
    App0 s`[↑]`[↑]`[↑] $2 $1)).
  { fall a. fall c. fall b. fintro Hac. fdestr Hac Hab Hbc.
    pose proof (raw_app_endpoints _ v r1 a b Htrans Hr1V Hab) as H1.
    pose proof (raw_app_endpoints _ v r2 b c Htrans Hr2V Hbc) as H2.
    pose proof Hedges as H. finst H a c. apply (iff_r _ _ _ H).
    fsplit; [fsplit; [exact (CE1 H1)|exact (CE2 H2)]|].
    fexists b. fsplit; assumption. }
  unfold deqv. fexists s. fsplit.
  - unfold dbisim. fsplit; [exact Hts|]. fall a. fall c. fintro Hac.
    pose proof Hedges as H. finst H a c.
    pose proof (CE2 (iff_l _ _ _ H Hac)) as Hex. fex Hex b Hb.
    fdestr Hb Hab Hbc.
    pose proof (dbisim_types _ t r1 a b Hbis1 Hab) as Htypes1.
    pose proof (dbisim_types _ t r2 b c Hbis2 Hbc) as Htypes2.
    fsplit; [fsplit; [exact (CE1 Htypes1)|exact (CE2 Htypes2)]|]. fsplit.
    + fall a'. fintro Ha'.
      pose proof (dbisim_forth _ t r1 a b a' Hbis1 Hab Ha') as F1.
      fex F1 b' HB'. fdestr HB' Hb' Ha'b'.
      pose proof (dbisim_forth _ t r2 b c b' Hbis2 Hbc Hb') as F2.
      fex F2 c' HC'. fdestr HC' Hc' Hb'c'. fexists c'. fsplit; [exact Hc'|].
      pose proof Hcomp as Hjoin. finst Hjoin a' c' b'. apply (IE Hjoin). fsplit; assumption.
    + fall c'. fintro Hc'.
      pose proof (dbisim_back _ t r2 b c c' Hbis2 Hbc Hc') as B2.
      fex B2 b' HB'. fdestr HB' Hb' Hb'c'.
      pose proof (dbisim_back _ t r1 a b b' Hbis1 Hab Hb') as B1.
      fex B1 a' HA'. fdestr HA' Ha' Ha'b'. fexists a'. fsplit; [exact Ha'|].
      pose proof Hcomp as Hjoin. finst Hjoin a' c' b'. apply (IE Hjoin). fsplit; assumption.
  - finst Hcomp x z y. apply (IE Hcomp). fsplit; assumption.
Qed.

Definition deqv_trans_statement : form :=
  ∀ ∀ ∀ ∀ (raw_empty $3 → deqv $3 $2 $1 → deqv $3 $1 $0 → deqv $3 $2 $0).

Theorem K0_proves_deqv_trans : K0 ⊢TC deqv_trans_statement.
Proof.
  set (ri := forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))).
  set (B0 := KBase ++ [ri]).
  assert (HB : incl KBase B0) by (intros b Hb; apply in_or_app; now left).
  assert (HRI : In ri B0) by (apply in_or_app; right; now left).
  exists B0. split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[]]].
    + apply KBase_ok, Hb.
    + apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded.
      exact domain_composition_bounded.
  - unfold deqv_trans_statement. fall t. fall x. fall y. fall z.
    match goal with |- ?G ⊢C _ =>
      assert (HB' : incl KBase G) by exact HB;
      assert (HRI' : In ri G) by exact HRI
    end.
    fintro Hempty. fintro Hxy. fintro Hyz.
    exact (deqv_trans _ HB' t x y z HRI' Hempty Hxy Hyz).
Qed.

Corollary KPrimeOrd_proves_deqv_trans : KPrimeOrd ⊢TC deqv_trans_statement.
Proof. apply K0_derivation_to_KPrimeOrd, K0_proves_deqv_trans. Qed.
